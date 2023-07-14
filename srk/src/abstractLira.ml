open BatEnum.Infix
module P = Polyhedron
module L = IntLattice
module V = Linear.QQVector
module LM = Linear.MakeLinearMap(QQ)(SrkUtil.Int)(V)(V)

module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "srk.abstractLia" end)

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

  val int_frac_ctx : context LinearTerm.IntFracContext.t

  (** Target symbols to preserve *)
  val symbols : Syntax.symbol list

end

module Lira (Target : Target) : AbstractDomain
       with type context = Target.context = struct

  open Syntax

  module Lt = LinearTerm

  type context = Target.context
  let context = Target.context

  type extended_lattice =
    | LatTop (* Corresponds to false *)
    | LatStd of IntLattice.t

  (* The ambient space is spanned by the integer and fractional dimensions 
     of the symbols to preserve.
   *)              
  let ambient_dimension = (List.length Target.symbols) * 2

  type t = DD.closed DD.t * extended_lattice

  let bottom = ( Polyhedron.dd_of ambient_dimension Polyhedron.bottom, LatTop )

  let lattice_meet l1 l2 =
    match l1, l2 with
    | LatTop, LatTop -> LatTop
    | LatTop, LatStd l
      | LatStd l, LatTop -> LatStd l
    | LatStd l1, LatStd l2 -> LatStd (IntLattice.intersect l1 l2)

  let join (p1, l1) (p2, l2) =
    (DD.join p1 p2, lattice_meet l1 l2)

  let all_int_vars = Lt.IntFracContext.int_vars Target.int_frac_ctx
  let all_frac_vars = Lt.IntFracContext.frac_vars Target.int_frac_ctx

  let fractional_bounds =
    Symbol.Set.fold (fun x bounds ->
        let v = V.of_term QQ.one (int_of_symbol x) in
        (`Nonneg, v)
        :: (`Pos, V.add_term QQ.one Linear.const_dim (V.negate v))
        :: bounds
      )
      all_frac_vars
      []

  let is_int_intvars =
    Symbol.Set.fold
      (fun x is_ints -> V.of_term QQ.one (int_of_symbol x) :: is_ints)
      all_int_vars
      []

  let polyhedral_atom_of srk (ckind, v) =
    let op = match ckind with
      | `Zero -> mk_eq srk (mk_real srk QQ.zero)
      | `Nonneg -> mk_leq srk (mk_real srk QQ.zero)
      | `Pos -> mk_lt srk (mk_real srk QQ.zero)
    in op (Linear.of_linterm srk v)

  let (target_int_vars, target_frac_vars) =
    List.fold_left (fun (int_vars, frac_vars) x ->
        let int_var = Lt.IntFracContext.int_var_of x Target.int_frac_ctx in
        let frac_var = Lt.IntFracContext.frac_var_of x Target.int_frac_ctx in
        ( int_var :: int_vars, frac_var :: frac_vars)
      ) ([], []) Target.symbols
    |> (fun (iv, fv) -> (List.rev iv, List.rev fv))

  (* Both real and integer dimensions for the target symbols +
     integer dimensions for the other symbols.
   *)
  let (target_terms_for_real, target_real_dim_to_symbol) =
    BatList.fold_lefti (fun (terms, dim_to_symbol) i x ->
        ( Syntax.mk_const Target.context x :: terms
        , SrkUtil.Int.Map.add i x dim_to_symbol)
      ) ([], SrkUtil.Int.Map.empty)
      ( target_frac_vars @ Symbol.Set.elements all_int_vars)
    |> (fun (l, dim_to_symbol) -> List.rev l, dim_to_symbol)

  let integer_dims_to_eliminate =
    Symbol.Set.diff all_int_vars (Symbol.Set.of_list target_int_vars)
    |> Symbol.Set.elements
    |> List.map int_of_symbol

  let int_frac_map =
    Lt.IntFracContext.fold
      (fun _ ~int_var ~frac_var map ->
        fun dim -> if dim = int_of_symbol int_var then `Int
                   else if dim = int_of_symbol frac_var then `Frac
                   else map dim)
      Target.int_frac_ctx
      (fun _ -> invalid_arg "dimension is not in int-frac context")

  let term_of_vector v =
    let open Syntax in
    BatEnum.fold (fun l (coeff, dim) ->
        let dim_sym = symbol_of_int dim in
        let x = Lt.IntFracContext.original_var_of dim_sym
                  Target.int_frac_ctx in
        let tx =
          let tx0 = mk_const context x in
          if Symbol.Set.mem dim_sym all_int_vars then
            mk_floor context tx0
          else if Symbol.Set.mem dim_sym all_frac_vars then
            mk_sub context tx0 (mk_floor context tx0)
          else
            failwith "Ambient dimension should only contain integer or 
                      fractional variables"
        in
        mk_mul context [mk_real context coeff; tx]
        :: l
      )
      []
      (V.enum v)
    |> mk_add context

  let implicant_of_polyhedral_constraint (ckind, vector) =
    let zero = Syntax.mk_zero context in
    let term = term_of_vector vector in
    let mk_compare cmp term = Syntax.mk_compare cmp context zero term in
    match ckind with
    | `Zero -> mk_compare `Eq term
    | `Nonneg -> mk_compare `Leq term
    | `Pos -> mk_compare `Lt term

  let concretize (p, l) =
    let open BatEnum in
    let polyhedral_atoms = DD.enum_constraints p
                           /@ implicant_of_polyhedral_constraint
                           |> BatList.of_enum in
    let lattice_atoms =
      match l with
      | LatTop -> []
      | LatStd l ->
         List.map (fun v -> Syntax.mk_is_int context (term_of_vector v))
           (IntLattice.basis l)
    in
    Syntax.mk_and context (polyhedral_atoms @ lattice_atoms)

  let constraints_of_implicant implicant m =
    let linear_implicant =
      Lt.LinearFormula.purify Target.context Target.int_frac_ctx implicant m in
    let inequalities =
      Lt.LinearFormula.polyhedral_constraints_in linear_implicant in
    let lattice_constraints =
      Lt.LinearFormula.lattice_constraints_in linear_implicant in
    (inequalities, lattice_constraints)

  let abstract phi interp =
    let implicant =
      match Interpretation.select_implicant interp phi with
      | Some implicant -> implicant
      | None -> failwith "No implicant found" in
    let ext_interp =
      Lt.IntFracContext.extend_model
        Target.context Target.int_frac_ctx interp in
    let (inequalities, lattice_constraints) =
      constraints_of_implicant implicant ext_interp in
    let inequalities_with_fractional_bounds =
      BatEnum.fold (fun atoms ineq ->
          polyhedral_atom_of Target.context ineq :: atoms)
        (List.map (polyhedral_atom_of Target.context) fractional_bounds)
        inequalities
    in
    let poly_after_real_projection =
      (* TODO: Expose convex hull without going through terms? *)
      (Abstract.conv_hull Target.context
         (mk_and Target.context inequalities_with_fractional_bounds)
         (Array.of_list target_terms_for_real)
       |> DD.enum_constraints)
      /@ (fun (ckind, v) ->
        let mapped =
          BatEnum.fold (fun u (coeff, dim) ->
              let original_dim =
                int_of_symbol
                  (SrkUtil.Int.Map.find dim target_real_dim_to_symbol) in
              V.add_term coeff original_dim u
            ) V.zero
            (V.enum v)
        in (ckind, mapped))
      |> Polyhedron.of_constraints
    in
    let lattice_with_intvars =
      IntLattice.hermitize
        (List.rev_append is_int_intvars (BatList.of_enum lattice_constraints))
    in
    let (poly_after_int_projection, lattice_after_int_projection) =
      let model dim =
        Interpretation.evaluate_term ext_interp
          (mk_const Target.context (symbol_of_int dim)) in
      LatticePolyhedron.local_project int_frac_map model
        ~eliminate:integer_dims_to_eliminate
        ( poly_after_real_projection
        , lattice_with_intvars )
    in
    let lattice_hull =
      LatticePolyhedron.lattice_hull
        poly_after_int_projection lattice_after_int_projection in
    let lineality =
      Polyhedron.enum_constraints lattice_hull
      //@ (fun (ckind, v) ->
        match ckind with
        | `Zero -> Some v
        | _ -> None)
      |> BatList.of_enum
    in
    let lattice_with_lineality =
      List.rev_append lineality (IntLattice.basis lattice_after_int_projection)
      |> IntLattice.hermitize
    in
    ( P.dd_of ambient_dimension lattice_hull
    , LatStd lattice_with_lineality)

  let pp fmt (p, l) =
    Format.fprintf fmt "{ polyhedron : %a @. lattice: %a }"
      (DD.pp (fun fmt d -> Format.fprintf fmt "%d" d)) p
      (fun fmt l -> match l with
                    | LatTop -> Format.fprintf fmt "top"
                    | LatStd l -> IntLattice.pp fmt l) l

end

module Abstract (A : AbstractDomain) : sig

  val init : A.context Syntax.formula -> A.context Smt.Solver.t * A.t

  val abstract : A.context Syntax.formula -> A.t

end = struct

  let init formula =
    let solver = Smt.mk_solver A.context in
    Smt.Solver.add solver [formula];
    (solver, A.bottom)

  let abstract formula =
    let (solver, initial_value) = init formula in
    let rec go n value =
      logf "Iteration %d@." n;
      match Smt.Solver.get_model solver with
      | `Sat interp ->
         let rho = A.abstract formula interp in
         logf "abstract: abstracted, now joining";
         let joined = A.join value rho in
         logf "abstract: joining rho %a with %a to get %a@."
           A.pp rho
           A.pp value
           A.pp joined;
         let formula = A.concretize joined in
         logf "abstract: new constraint to negate: %a@."
           (Syntax.pp_smtlib2 A.context) formula;
         Smt.Solver.add solver
           [Syntax.mk_not A.context formula];
         go (n + 1) joined
      | `Unsat ->
         value
      | `Unknown -> failwith "Can't get model"
    in go 1 initial_value

end

let lira_hull (type a) (srk: a Syntax.context) (formula: a Syntax.formula)
      terms =
  let (formula_with_defining_symbols, symbols_to_keep, original_term_of) =
    Array.fold_left (fun (constraints, fresh_symbols, original_term_of) term ->
        let x = Syntax.mk_symbol srk `TyReal in
        ( Syntax.mk_eq srk (Syntax.mk_const srk x) term :: constraints
        , x :: fresh_symbols
        , Syntax.Symbol.Map.add x term original_term_of )
      )
      ([formula], [], Syntax.Symbol.Map.empty)
      terms
    |> (fun (phi, symbols, original_term_of) ->
      (Syntax.mk_and srk phi, List.rev symbols, original_term_of))
  in
  let int_frac_ctx =
    LinearTerm.IntFracContext.mk_context srk
      (Syntax.Symbol.Set.enum (Syntax.symbols formula_with_defining_symbols)) in
  let module LiraAbs = Lira(struct
                           type context = a
                           let context = srk
                           let int_frac_ctx = int_frac_ctx
                           let symbols = symbols_to_keep
                         end) in
  let module Compute = Abstract(LiraAbs) in
  Compute.abstract formula_with_defining_symbols
  |> LiraAbs.concretize
       
