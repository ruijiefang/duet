open BatEnum.Infix
module P = Polyhedron
module L = IntLattice
module V = Linear.QQVector
module LM = Linear.MakeLinearMap(QQ)(SrkUtil.Int)(V)(V)

module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "symbolicAbstraction" end)

(** Abstract domain that supports symbolic abstraction *)
module type AbstractDomain = sig
  type t
  type context
  val context : context Syntax.context

  val bottom : t
  val join : t -> t -> t
  val concretize : t -> context Syntax.formula
  val abstract : context Syntax.formula -> context Interpretation.interpretation -> t

  val pp : Format.formatter -> t -> unit

end

module type Target = sig

  type context
  val context : context Syntax.context

  (** Symbols that the input formula is in *)
  val formula_symbols : Syntax.Symbol.Set.t

  (** Constraints of the integer hull are to be linear in these terms *)
  val terms : context Syntax.arith_term BatArray.t

end

(** Convert between implicants over [Target.formula_symbols] and
    constraints in some vector space, and between interpretations of the implicant
    and valuations of vectors in the vector space.
    [Target.terms] are mapped to the lowest dimensions in this vector space,
    and other symbols of the implicant are mapped to higher dimensions.

    - [valuation(interp)(i) = interp(Target.terms[i])]
 *)
module ImplicantConstraintConversion (Target : Target) : sig

  val dimensions_to_eliminate : int list

  val ambient_dimension : int

  val valuation : Target.context Interpretation.interpretation -> int -> Q.t

  val constraints_of_implicant :
    Target.context Syntax.formula list ->
    ([> `Nonneg | `Zero ] * V.t) list * V.t list

  val implicant_of_constraints :
    ([< `Nonneg | `Pos | `Zero ] * V.t) BatEnum.t -> Target.context Syntax.formula list

end = struct

  let (basis, map_to_fresh_dims) =
    let open Syntax in
    let basis = BatDynArray.create () in
    let map =
      let neg_one = V.of_term QQ.one Linear.const_dim in
      BatArray.fold_lefti (fun map i t ->
          let vec = Linear.linterm_of Target.context t in
          BatDynArray.add basis vec;
          LM.may_add vec (V.of_term QQ.one i) map)
        (LM.add_exn neg_one neg_one LM.empty)
        Target.terms
      |> Symbol.Set.fold (fun symbol map ->
             let symbol_vec = V.of_term QQ.one (Linear.dim_of_sym symbol) in
             let ambient_dim = BatDynArray.length basis in
             match LM.add symbol_vec (V.of_term QQ.one ambient_dim) map with
             | Some map' ->
                BatDynArray.add basis symbol_vec;
                map'
             | None -> map
           )
           Target.formula_symbols
    in (basis, map)

  let ambient_dimension = BatDynArray.length basis + 1

  let dimensions_to_eliminate =
    let dim = Array.length Target.terms in
    BatList.of_enum (dim --^ ambient_dimension)

  let valuation interp i =
    Linear.evaluate_linterm
      (Interpretation.real interp)
      (BatDynArray.get basis i)

  let atom_of_constraint (ckind, cnstrnt) =
    let zero = Syntax.mk_zero Target.context in
    let term = Linear.term_of_vec Target.context (fun i -> Target.terms.(i)) cnstrnt in
    let mk_compare cmp term = Syntax.mk_compare cmp Target.context zero term in
    match ckind with
    | `Zero -> mk_compare `Eq term
    | `Nonneg -> mk_compare `Leq term
    | `Pos -> mk_compare `Lt term

  let implicant_of_constraints cnstrnts =
    cnstrnts /@ atom_of_constraint |> BatList.of_enum

  let linearize t =
    try
      Linear.linterm_of Target.context t
    with Linear.Nonlinear ->
      let s = Format.asprintf "Term %a is not linear" (Syntax.ArithTerm.pp Target.context) t in
      failwith s

  let constraint_of_atom atom =
    let image v = LM.apply map_to_fresh_dims v |> BatOption.get in
    match atom with
    | `ArithComparison (`Lt, t1, t2) ->
       (* `Ineq (`Pos, V.sub (linearize context t2) (linearize context t1)) *)
       (* Silently convert to non-strict inequality *)
       logf "Warning: Silently converting > to >= 0@.";
       `Ineq (`Nonneg, image (V.sub (linearize t2) (linearize t1)))
    | `ArithComparison (`Leq, t1, t2) ->
       `Ineq (`Nonneg, image (V.sub (linearize t2) (linearize t1)))
    | `ArithComparison (`Eq, t1, t2) ->
       `Ineq (`Zero, image (V.sub (linearize t2) (linearize t1)))
    | `IsInt s ->
       `InLat (image (linearize s))
    | `Literal _
      | `ArrEq _ -> failwith "Cannot handle atoms"

  let constraints_of_implicant atoms =
    List.fold_left
      (fun (inequalities, lattice_constraints) atom ->
        match constraint_of_atom
                (Interpretation.destruct_atom Target.context atom) with
        | `Ineq cnstrnt -> (cnstrnt :: inequalities, lattice_constraints)
        | `InLat v -> (inequalities, v :: lattice_constraints)
      )
      ([], [])
      atoms

end

module IntHullProjection (Target : Target)
       : (AbstractDomain with type t = DD.closed DD.t
                          and type context = Target.context) = struct

  include ImplicantConstraintConversion(Target)

  type t = DD.closed DD.t
  type context = Target.context
  let context = Target.context

  let bottom = P.dd_of ambient_dimension P.bottom

  let join p1 p2 = DD.join p1 p2

  let concretize p =
    let p_formulas = implicant_of_constraints (DD.enum_constraints p) in
    Syntax.mk_and context p_formulas

  let abstract formula interp =
    let implicant =
      match Interpretation.select_implicant interp formula with
      | Some implicant -> implicant
      | None -> failwith "No implicant found" in
    let (inequalities, _lattice_constraints) = constraints_of_implicant implicant in
    let p = DD.of_constraints_closed ambient_dimension (BatList.enum inequalities) in
    let hull = P.integer_hull_dd ambient_dimension p in
    DD.project dimensions_to_eliminate hull

  let pp fmt p =
    Format.fprintf fmt "{ polyhedron : %a }"
      (DD.pp (fun fmt d -> Format.fprintf fmt "%d" d)) p

end

module Abstract (A : AbstractDomain) : sig

  val abstract : A.context Syntax.formula -> A.t

end = struct

  type t =
    {
      solver : A.context Smt.Solver.t
    ; value : A.t
    }

  let init formula =
    let solver = Smt.mk_solver A.context in
    Smt.Solver.add solver [formula];
    { solver ; value = A.bottom }

  let abstract formula =
    let state = init formula in
    let rec go bound n state =
      logf "Iteration %d@." n;
      match Smt.Solver.get_model state.solver with
      | `Sat interp ->
         let rho = A.abstract formula interp in
         logf "abstract: abstracted, now joining";
         let joined = A.join state.value rho in
         logf "abstract: joining rho %a with %a to get %a@."
           A.pp rho
           A.pp state.value
           A.pp joined;
         let formula = A.concretize joined in
         logf "abstract: new constraint to negate: %a@." (Syntax.pp_smtlib2 A.context) formula;
         Smt.Solver.add state.solver
           [Syntax.mk_not A.context formula];
         let next = { state with value = joined } in
         begin match bound with
         | Some b -> if n <= b then go (Some b) (n + 1) next
                     else state
         | None -> go bound (n + 1) next
         end
      | `Unsat ->
         state
      | `Unknown -> failwith "Can't get model"
    in (go None 1 state).value

end

let integer_hull (type a) (srk : a Syntax.context) how (phi : a Syntax.formula)
      terms =
  let module Target = struct
      type context = a
      let context = srk
      let formula_symbols = Syntax.symbols phi
      let terms = terms
    end in
  let module Domain =
    (val
       (match how with
        | `Standard -> (module IntHullProjection(Target))
        | `Cone -> failwith "Not implemented yet"
        | `Cooper -> failwith "Not implemented yet"
       )
       : AbstractDomain with type t = DD.closed DD.t and type context = a)
  in
  let module Compute = Abstract(Domain) in
  Compute.abstract phi
