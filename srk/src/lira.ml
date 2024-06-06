(** This module defines LIRA vectors (implicitly) and LIRA formulas.

    - A LIRA term (formula) is a term (formula) in the FOL with equality over
      (QQ; +, scalar multiplication, floor(-); >, >=, Int(-)).

    - A LIRA vector is a QQVector where every coordinate corresponds to either
      an integer-valued variable or a real-valued fractional variable
      (i.e., 0 <= x_frac < 1).
      When coordinates mean coefficients, it represents a term
      [sum_i a_i (x_int)_i + sum_j b_j (x_frac)_j] that is linear in
      integer and fractional variables.

      A LIRA vector exists in the context of a LIRA context ([SymbolBinding.t])
      which associates each "original" variable [x] in LIRA terms/formulas with
      an "original dimension", an "integer dimension" and a "fractional dimension";
      an integer dimension corresponds to an integer-valued variable [x_int],
      and a fractional dimension corresponds to a fractional-valued variable
      [x_frac]. In this way, a LIRA vector can be interpreted as a LIRA term,
      via the constraints [x = x_int + x_frac /\ Int(x_int) /\ 0 <= x_frac < 1].

      LIRA vectors represent only a subset of LIRA terms: those that are linear
      in floor(x) and frac(x) (= x - floor(x)), for variables x.
      Nevertheless, any LIRA term is semantically equal to a LIRA vector (the
      linear term it represents) modulo some conditions, which can itself
      be expressed as a formula over LIRA vectors (that we call a
      [linear_formula] below).

    - A LIRA formula ([linear_formula]) is a positive conjunction of
      inequalities and integrality constraints in (terms represented by)
      LIRA vectors.
 *)

include Log.Make(struct let name = "srk.lira" end)

module IntMap = SrkUtil.Int.Map
module IntSet = SrkUtil.Int.Set

let () = my_verbosity_level := `trace

module DimensionBinding : sig
  (** A dimension binding associates a dimension [n] ("original dimension")
      with a pair of dimensions ([n_int], [n_frac]) ("integer dimension",
      "fractional dimension"), such that:

      - The integer-fractional dimensions are guaranteed to be a segment
        of the natural numbers, starting from the first even number at least
        [initial].
      - Each integer dimension is even.
      - Each fractional dimension is odd.
 *)
  type t

  (** Integer and fractional dimensions begin at the smallest even
      number >= [initial].
   *)
  val empty: initial:int -> t

  (** [add n t] assigns [n] to a fresh integer dimension [n_int] and a fresh
      fractional dimension [n_frac].
   *)
  val add: int -> t -> t

  val int_frac_dim_of: int -> t -> int * int

  val to_original_dim: int -> t -> int

  val is_int_dim: t -> int -> bool

  val is_frac_dim: t -> int -> bool

  val fold: ('a -> original_dim:int -> int_dim:int -> frac_dim:int -> 'a) -> t -> 'a -> 'a

  val integer_constraints_for:
    (original_dim:int -> int_dim:int -> bool) -> t -> Linear.QQVector.t BatEnum.t

  val inequalities_for:
    (original_dim:int -> frac_dim:int -> bool) ->
    t -> (Polyhedron.constraint_kind * Linear.QQVector.t) BatEnum.t

  val pp: Format.formatter -> t -> unit

end = struct

  type t = { to_int_frac: int IntMap.t
           ; from_int_frac: int IntMap.t
           ; initial: int
           }

  let empty ~initial =
    let initial = if initial mod 2 = 0 then initial / 2 else (initial + 1) / 2 in
    { to_int_frac = IntMap.empty
    ; from_int_frac = IntMap.empty
    ; initial
    }

  let add original_dim t =
    match IntMap.find_opt original_dim t.to_int_frac with
    | None ->
       begin match IntMap.max_binding_opt t.from_int_frac with
       | None ->
          { to_int_frac = IntMap.add original_dim t.initial t.to_int_frac
          ; from_int_frac = IntMap.add t.initial original_dim t.from_int_frac
          ; initial = t.initial
          }
       | Some (curr_max, _) ->
          { to_int_frac = IntMap.add original_dim (curr_max + 1) t.to_int_frac
          ; from_int_frac = IntMap.add (curr_max + 1) original_dim t.from_int_frac
          ; initial = t.initial
          }
       end
    | Some _ -> t

  let int_frac_dim_of x t =
    match IntMap.find_opt x t.to_int_frac with
    | Some dim -> (2 * dim, 2 * dim + 1)
    | None ->
       logf ~level:`debug "int_frac_dim_of: Cannot find %d" x;
       raise Not_found

  let to_original_dim x t =
    try
      if x mod 2 = 0 then IntMap.find (x / 2) t.from_int_frac
      else IntMap.find ((x - 1) / 2) t.from_int_frac
    with Not_found ->
      logf ~level:`debug
        "to_original_dim: Cannot find original dimension for %d" x;
      raise Not_found

  let is_int_dim t x =
    let is_int_dim = (x mod 2 = 0) in
    let idx = if is_int_dim then x / 2 else (x - 1) / 2 in
    match IntMap.find_opt idx t.from_int_frac with
    | Some _ -> is_int_dim
    | None -> false

  let is_frac_dim t x =
    let is_int_dim = (x mod 2 = 0) in
    let idx = if is_int_dim then x / 2 else (x - 1) / 2 in
    match IntMap.find_opt idx t.from_int_frac with
    | Some _ -> not is_int_dim
    | None -> false

  let fold (f: 'a -> original_dim:int -> int_dim:int -> frac_dim:int -> 'a) t initial =
    IntMap.fold
      (fun source target curr ->
        f curr ~original_dim:source ~int_dim:(2*target) ~frac_dim:(2*target + 1))
      t.to_int_frac initial

  let integer_constraints_for select t =
    let cnstrs = BatEnum.empty () in
    fold (fun () ~original_dim ~int_dim ~frac_dim:_ ->
        if select ~original_dim ~int_dim then
          BatEnum.push cnstrs (Linear.QQVector.of_term QQ.one int_dim)
        else
          ())
      t ();
    cnstrs

  let bounds_for_frac_dim frac_dim =
    let lower_bound = (`Nonneg, Linear.QQVector.of_term QQ.one frac_dim) in
    let upper_bound = (`Pos,
                       Linear.QQVector.of_term (QQ.of_int (-1)) frac_dim
                       |> Linear.QQVector.add_term QQ.one Linear.const_dim)
    in
    [lower_bound; upper_bound]

  let inequalities_for select t =
    fold (fun bds ~original_dim ~int_dim:_ ~frac_dim ->
        if select ~original_dim ~frac_dim then
          BatEnum.append (BatList.enum (bounds_for_frac_dim frac_dim)) bds
        else
          bds)
      t (BatEnum.empty ())

  let pp fmt t =
    fold (fun () ~original_dim ~int_dim ~frac_dim ->
        Format.fprintf fmt "@[%d <--> (%d, %d)@]@;" original_dim int_dim frac_dim)
      t ()

end

module IntFracValuation : sig

  (** An assignment of [n_int] and [n_frac] dimensions in a dimension binding
      to [QQ.t]
   *)
  type t

  val value_of: t -> int -> QQ.t

  val of_assignment: (int -> QQ.t) -> t

end = struct

  type t = (int -> QQ.t)

  let value_of valuation dim = valuation dim

  let of_assignment m = m

end

(** [dim_of_symbol] and [symbol_of_dim] has to be an isomorphism pair
    (whenever it is defined), and the image of [dim_of_symbol] should
    be contained in the original dimensions of [dimension_binding].
    [term_of_dim] interprets an original dimension that is not in the domain
    of [symbol_of_dim], so that every original dimension in [dimension_binding]
    corresponds to a term.
 *)
type 'a symbol_binding =
  {
    dim_of_symbol: Syntax.symbol -> int
  ; symbol_of_dim: int -> Syntax.symbol option
  ; term_of_dim: int -> 'a Syntax.arith_term option
  }

module Context : sig

  (** Associates each original variable (symbol) with an integer and a
      fractional dimension, via a dimension binding that first
      associates it with an original dimension.
   *)
  type 'a t

  val make: 'a symbol_binding -> DimensionBinding.t -> 'a t

  val valuation_of: 'a t -> 'a Interpretation.interpretation -> IntFracValuation.t

  val dimension_binding: 'a t -> DimensionBinding.t

  (** Get the symbol of an original dimension *)
  (* val symbol_of_dim: 'a t -> int -> Syntax.symbol option *)

  (** Get the original dimension of a symbol *)
  val dim_of_symbol: 'a t -> Syntax.symbol -> int

end = struct

  type 'a t =
    { dim_binding: DimensionBinding.t
    ; sym_binding: 'a symbol_binding
    }

  let make sym_binding dim_binding = { dim_binding; sym_binding }

  let valuation_of t interpretation =
    let m x =
      let original_dim = DimensionBinding.to_original_dim x t.dim_binding in
      let compute v =
        let intval = QQ.of_zz (QQ.floor v) in
        if DimensionBinding.is_int_dim t.dim_binding x then
          intval else
          QQ.sub v intval
      in
      begin match t.sym_binding.symbol_of_dim original_dim with
      | Some sym ->
         compute (Interpretation.real interpretation sym)
      | None ->
         begin match t.sym_binding.term_of_dim original_dim with
         | Some term ->
            compute (Interpretation.evaluate_term interpretation term)
         | None ->
            failwith (Format.sprintf
                        "valuation_of: querying int-frac dimension %d, original %d@;"
                        x original_dim)
         end
      end
    in
    IntFracValuation.of_assignment
      (fun x -> if x = Linear.const_dim then QQ.one else m x)

  let dimension_binding t = t.dim_binding

  (*
  let symbol_of_dim t = t.sym_binding.symbol_of_dim *)

  let dim_of_symbol t = t.sym_binding.dim_of_symbol

end

module Linearized : sig

  (** In the following datatypes, their support apart from the constant
      dimension must be contained in the set of integer-fractional dimensions
      existing within a dimension binding.
   *)

  type lira

  type 'a vector

  type linear_formula =
    {
      inequalities: (Polyhedron.constraint_kind * lira vector) list
    ; integral: lira vector list
    }

  (** A polyhedron-lattice pair over integer, fractional and the constant
      dimension
   *)
  type p_linear_set

  val tru: linear_formula

  val unfold_vector: lira vector -> Linear.QQVector.t

  val fold_vector: Linear.QQVector.t -> lira vector

  val unfold_linear_formula:
    linear_formula ->
    (Polyhedron.constraint_kind * Linear.QQVector.t) list * Linear.QQVector.t list

  val linear_set_of: linear_formula -> p_linear_set

  val unfold_linear_set: p_linear_set -> Polyhedron.t * IntLattice.t

  val fold_linear_set: Polyhedron.t * IntLattice.t -> p_linear_set

end = struct

  type lira = unit

  type 'a vector = Linear.QQVector.t

  let fold_vector v = v
  let unfold_vector v = v

  type linear_formula =
    {
      inequalities: (Polyhedron.constraint_kind * lira vector) list
    ; integral: lira vector list
    }

  let unfold_linear_formula phi = (phi.inequalities, phi.integral)

  let linear_set_of { inequalities; integral } =
    ( Polyhedron.of_constraints (BatList.enum inequalities)
    , IntLattice.hermitize integral )

  type p_linear_set = Polyhedron.t * IntLattice.t

  let unfold_linear_set (p, l) = (p, l)
  let fold_linear_set (p, l) = (p, l)

  let tru = {inequalities = []; integral = []}

end

module LinearizeTerm: sig

  open Linearized

  (** A linear condition is a linear formula where Int(-) constraints are
      pure, i.e., they do not contain any real-valued variables.
   *)
  type lincond = linear_formula

  (** Given a [term] whose symbols are in the domain of [binding],
      [linearize srk binding term m = (phi, v)] implies
      [m |= phi |= term = v], where the interpretation of [phi] and [v] is
      given by [binding], and the entailment is modulo
      LIRA, the equalities [x = x_int + x_frac], bounds for [x_frac],
      and integrality constraints for [x_int].
      Int literals in [phi] are pure, i.e., free of fractional variables.

      TODO: Track the fractional variables that are used in linearization.
      We only have to introduce bounds for these variables later.
   *)
  val linearize:
    'a Syntax.context -> 'a Context.t ->
    'a Syntax.arith_term -> 'a Interpretation.interpretation ->
    lincond * lira vector

  (** Given a LIRA vector [t] under [binding],
      and a valuation [m] for integer and fractional variables,
      [floor binding m t = (phi, t')] where [m |= phi],
      [phi |= floor(t) = t'], [t'] is free of fractional variables,
      and Int literals in [phi] are pure.
   *)
  val floor: DimensionBinding.t -> IntFracValuation.t ->
             lira vector -> lincond * lira vector

  val ceiling: DimensionBinding.t -> IntFracValuation.t ->
               lira vector -> lincond * lira vector

  val conjoin: lincond -> lincond -> lincond

end = struct

  open Linearized

  module DB = DimensionBinding

  type lincond = linear_formula

  let conjoin phi1 phi2 =
    {
      inequalities = List.rev_append phi1.inequalities phi2.inequalities
    ; integral = List.rev_append phi1.integral phi2.integral
    }

  let multiply_vectors v1 v2 =
    Linear.QQVector.fold (fun dim2 scalar2 outer_sop ->
        if dim2 = Linear.const_dim then
          Linear.QQVector.scalar_mul scalar2 v1
          |> Linear.QQVector.add outer_sop
        else
          Linear.QQVector.fold (fun dim1 scalar1 inner_sop ->
              if dim1 = Linear.const_dim then
                Linear.QQVector.add_term (QQ.mul scalar1 scalar2) dim2 inner_sop
              else
                raise Linear.Nonlinear
            )
            v1
            outer_sop
      )
      v2
      Linear.QQVector.zero

  let floor binding m v =
    let v = unfold_vector v in
    let (linearized_int, residue_to_floor, int_cond) =
      Linear.QQVector.fold (fun dim coeff (linearized, residue, cond) ->
          if not (DimensionBinding.is_int_dim binding dim) then
            (* fractional dimension or constant *)
            (linearized, Linear.QQVector.add_term coeff dim residue, cond)
          else (* integer dimension *)
            let remainder =
              logf ~level:`trace "Querying for dim = %d@;" dim;
              let x = QQ.mul coeff (IntFracValuation.value_of m dim) in
              QQ.sub x (QQ.of_zz (QQ.floor x))
            in
            let defloored =
              Linear.QQVector.of_term coeff dim
              |> Linear.QQVector.add_term (QQ.negate remainder) Linear.const_dim
            in
            ( Linear.QQVector.add defloored linearized
            , Linear.QQVector.add_term remainder Linear.const_dim residue
            , { cond with integral = (fold_vector defloored) :: cond.integral } )
        )
        v
        (Linear.QQVector.zero, Linear.QQVector.zero, tru)
      (*
        DB.fold (fun (linearized, v, cond) ~original_dim:_ ~int_dim ~frac_dim:_ ->
          let (a, v') = Linear.QQVector.pivot int_dim v in
          let remainder =
            Format.printf "Querying for int_dim = %d" int_dim;
            let x = QQ.mul a (IntFracValuation.value_of m int_dim) in
            QQ.sub x (QQ.of_zz (QQ.floor x))
          in
          let defloored =
            Linear.QQVector.of_term a int_dim
            |> Linear.QQVector.add_term (QQ.negate remainder) Linear.const_dim
          in
          ( Linear.QQVector.add defloored linearized
          , Linear.QQVector.add_term remainder Linear.const_dim v'
          , { cond with integral = defloored :: cond.integral }
          )
        ) binding (Linear.QQVector.zero, v, tru)
       *)
    in
    let (sum_of_fractional, fractional, residue_to_floor) =
      Linear.QQVector.fold (fun dim coeff (sum, fractional, residue) ->
          if not (DimensionBinding.is_frac_dim binding dim)
             && (dim = Linear.const_dim) then
            (sum, fractional, Linear.QQVector.add_term coeff dim residue)
          else
            begin
              logf ~level:`trace "Querying for frac_dim = %d" dim;
              let fraction = (IntFracValuation.value_of m dim) in
              ( QQ.add (QQ.mul coeff fraction) sum
              , Linear.QQVector.add_term coeff dim fractional
              , residue )
            end
        )
        residue_to_floor
        (QQ.zero, Linear.QQVector.zero, Linear.QQVector.zero)
      (*
      DB.fold (fun (sum, fractional, v) ~original_dim:_ ~int_dim:_ ~frac_dim ->
          let (coeff, v') = Linear.QQVector.pivot frac_dim v in
          Format.printf "Querying for frac_dim = %d" frac_dim;
          let fraction = (IntFracValuation.value_of m frac_dim) in
          ( QQ.add (QQ.mul coeff fraction) sum
          , Linear.QQVector.add_term coeff frac_dim fractional
          , v' )
        )
        binding
        (QQ.zero, Linear.QQVector.zero, residue_to_floor)
      *)
    in
    let y =
      Linear.QQVector.fold (fun dim coeff value ->
          if dim <> Linear.const_dim then
            invalid_arg
              (Format.asprintf
                 "floor: cannot take the floor of a non-LIRA vector, dim %d, coeff %a"
                 dim QQ.pp coeff)
          else
            QQ.add coeff value)
        residue_to_floor QQ.zero in
    let frac_y = QQ.sub y (QQ.of_zz (QQ.floor y)) in
    let n = QQ.of_zz (QQ.floor (QQ.add sum_of_fractional frac_y)) in
    let ny = QQ.add n (QQ.of_zz (QQ.floor y)) in
    let linearized = Linear.QQVector.add_term ny Linear.const_dim linearized_int in
    let cond =
      { int_cond with
        inequalities =
          [ (`Nonneg,
             (Linear.QQVector.add_term (QQ.sub frac_y n) Linear.const_dim fractional)
             |> fold_vector
            )
          ; (`Pos,
             Linear.QQVector.negate fractional
             |> Linear.QQVector.add_term
                  (QQ.add n (QQ.sub QQ.one frac_y)) Linear.const_dim
             |> fold_vector)
          ]
      }
    in
    (cond, fold_vector linearized)

  let ceiling binding m v =
    let (cond, v') =
      floor binding m (fold_vector (Linear.QQVector.negate (unfold_vector v)))
    in
    (cond, (fold_vector (Linear.QQVector.negate (unfold_vector v'))))

  let qq_of term =
    let (k, rest) = Linear.QQVector.pivot Linear.const_dim term in
    if Linear.QQVector.equal rest Linear.QQVector.zero then k
    else raise Linear.Nonlinear

  let nonzero_qq_of term =
    let qq = qq_of term in
    if QQ.equal qq QQ.zero then
      invalid_arg "linearize: division or mod by 0"
    else qq

  let linearize srk context term interp =
    let m = Context.valuation_of context interp in
    let (lincond, v) =
      Syntax.ArithTerm.eval srk
        (function
         | `Real r -> (tru, Linear.QQVector.of_term r Linear.const_dim)
         | `App (x, l) when l = [] ->
            begin try
                logf ~level:`trace
                  "linearize: translating symbol %a to dimension %d@;"
                  (Syntax.pp_symbol srk) x (Context.dim_of_symbol context x);
                let (int_dim, frac_dim) =
                  DB.int_frac_dim_of (Context.dim_of_symbol context x)
                    (Context.dimension_binding context) in
                let v = Linear.QQVector.of_term QQ.one int_dim
                        |> Linear.QQVector.add_term QQ.one frac_dim in
                (tru, v)
              with Not_found -> invalid_arg "linearize: binding is incomplete"
            end
         | `App (_x, _l) ->
            invalid_arg "linearize: Can't handle function symbols for now"
         | `Var (_x, _typ) ->
            invalid_arg "linearize: Can't handle quantified formulas for now"
         | `Add [phi_v] -> phi_v
         | `Add phis_vs  ->
            let (phis, vs) = BatList.split phis_vs in
            let conditions =
              { inequalities = List.concat (List.map (fun cond -> cond.inequalities) phis)
              ; integral = List.concat (List.map (fun cond -> cond.integral) phis)
              } in
            let v' = BatList.fold (fun curr v -> Linear.QQVector.add curr v)
                       Linear.QQVector.zero vs
            in
            (conditions, v')
         | `Mul [phi_v] -> phi_v
         | `Mul phis_vs ->
            let (phis, vs) = BatList.split phis_vs in
            let conditions =
              { inequalities = List.concat (List.map (fun cond -> cond.inequalities) phis)
              ; integral = List.concat (List.map (fun cond -> cond.integral) phis)
              } in
            let v' = List.fold_left multiply_vectors (BatList.hd vs) (BatList.tl vs) in
            (conditions, v')
         | `Binop (`Div, (phi1, v1), (phi2, v2)) ->
            let c = nonzero_qq_of v2 in
            (conjoin phi1 phi2, (Linear.QQVector.scalar_mul (QQ.inverse c) v1))
         | `Binop (`Mod, (phi1, v1), (phi2, v2)) ->
            (* a mod b = a - b floor(a/b) if b > 0
               a mod b = a - b ceiling(a/b) if b < 0
             *)
            let r2 = nonzero_qq_of v2 in
            let ratio = Linear.QQVector.scalar_mul (QQ.inverse r2) v1 in
            let round v =
              if QQ.lt QQ.zero r2 then
                floor (Context.dimension_binding context) m (fold_vector v)
              else
                ceiling (Context.dimension_binding context) m (fold_vector v)
            in
            let (rounding_phi, rounded) = round ratio in
            let moded = Linear.QQVector.scalar_mul (QQ.negate r2)
                          (unfold_vector rounded)
                        |> Linear.QQVector.add v1 in
            ( conjoin rounding_phi (conjoin phi1 phi2), moded )
         | `Unop (`Floor, (phi, v)) ->
            logf ~level:`trace "flooring v = %a@;"
              (Linear.QQVector.pp_term Format.pp_print_int) v;
            let (floor_phi, v') =
              floor (Context.dimension_binding context) m (fold_vector v) in
            logf ~level:`trace "floored v = %a@;"
              (Linear.QQVector.pp_term Format.pp_print_int) v;
            (conjoin floor_phi phi, (unfold_vector v'))
         | `Unop (`Neg, (phi, v)) ->
            (phi, Linear.QQVector.negate v)
         | `Ite (_ite_cond, _, _) ->
            invalid_arg "linearize: ite should have been simplified away"
         | `Select _ ->
            invalid_arg "linearize: select not handled yet"
        )
        term
    in
    (lincond, fold_vector v)

end

module LinearizeFormula : sig

  (** Given an [implicant] computed by [Interpretation.select_implicant],
      a [binding] that contains all symbols in [implicant] in its domain,
      and an interpretation [interp] that satisfies [implicant],
      [lira_implicant srk binding interp implicant = phi] where
      [interp |= phi |= implicant] modulo LIRA,
      equalities [x] = [x_int] + [x_frac],
      integrality constraints for [x_int], and bound constraints for [x_frac].
      All Int(-) literals in [phi] are pure, i.e., free of real-valued
      variables.
 *)
  val purify_implicant:
    'a Syntax.context -> 'a Context.t ->
    'a Interpretation.interpretation ->
    'a Syntax.formula list ->
    Linearized.p_linear_set

end = struct

  open Syntax
  open Linearized

  let linearize_inequality srk binding interp (rel, t1, t2) =
    logf ~level:`trace "Linearizing inequality: %a %a %a"
      (Syntax.ArithTerm.pp srk) t1
      (fun fmt rel -> match rel with
                      | `Lt -> Format.fprintf fmt "<"
                      | `Leq -> Format.fprintf fmt "<="
                      | `Eq -> Format.fprintf fmt "=") rel
      (Syntax.ArithTerm.pp srk) t2;
    let (cond1, linear1) = LinearizeTerm.linearize srk binding t1 interp in
    logf ~level:`trace "Linearized t1 = %a@;" (Syntax.ArithTerm.pp srk) t1;
    let (cond2, linear2) = LinearizeTerm.linearize srk binding t2 interp in
    logf ~level:`trace "Linearized t2 = %a@;" (Syntax.ArithTerm.pp srk) t2;
    let v =
      Linear.QQVector.sub (unfold_vector linear2) (unfold_vector linear1)
      |> fold_vector
    in
    let kind = match rel with
      | `Lt -> `Pos
      | `Leq -> `Nonneg
      | `Eq -> `Zero
    in
    logf ~level:`trace "Linearized inequality @[%a %a %a@]@; to @[%a %a@]@;"
      (Syntax.ArithTerm.pp srk) t1
      (fun fmt rel -> match rel with
                      | `Lt -> Format.fprintf fmt "<"
                      | `Leq -> Format.fprintf fmt "<="
                      | `Eq -> Format.fprintf fmt "=")
      rel
      (Syntax.ArithTerm.pp srk) t2
      (Linear.QQVector.pp_term Format.pp_print_int)
      (unfold_vector v)
      (fun fmt cnstr_kind -> match cnstr_kind with
                             | `Pos -> Format.fprintf fmt "> 0"
                             | `Nonneg -> Format.fprintf fmt ">= 0"
                             | `Zero -> Format.fprintf fmt "= 0"
      )
      kind;
    let cond = LinearizeTerm.conjoin cond1 cond2 in
    ((kind, v) :: cond.inequalities, cond.integral)

  let purify_implicant srk binding interp implicant =
    logf ~level:`trace
      "Purifying implicant @[%a@]@;"
      (Format.pp_print_list (Syntax.Formula.pp srk)) implicant;
    let adjoin (pcons, lcons) (polyhedral_cnstrs, lattice_cnstrs) =
      ( BatList.rev_append pcons polyhedral_cnstrs
      , BatList.rev_append lcons lattice_cnstrs
      )
    in
    let linearize_inequality = linearize_inequality srk binding interp in
    let collect curr_cnstrs literal =
      match Formula.destruct srk literal with
      | `Proposition (`App (_, _))
        | `Proposition (`Var _) ->
         invalid_arg "purify: LIRA cannot handle propositional atoms"
      | `Atom (`ArrEq (_a1, _a2)) ->
         invalid_arg "purify: LIRA cannot handle array terms"
      | `Atom (`Arith ineq) ->
         let cnstrs = linearize_inequality ineq in
         adjoin cnstrs curr_cnstrs
      | `Atom (`IsInt t) ->
         let cnstrs =
           linearize_inequality (`Eq, t, mk_floor srk t)
         in
         adjoin cnstrs curr_cnstrs
      | `Not phi ->
         begin match Formula.destruct srk phi with
         | `Proposition _ ->
            invalid_arg "purify: LIRA cannot handle propositional atoms"
         | `Atom (`ArrEq (_a1, _a2)) ->
            invalid_arg "purify: LIRA cannot handle array terms"
         | `Atom (`Arith (`Eq, t1, t2)) ->
            let cnstrs =
              if Interpretation.evaluate_formula interp (mk_lt srk t1 t2)
              then linearize_inequality (`Lt, t1, t2)
              else linearize_inequality (`Lt, t2, t1)
            in
            adjoin cnstrs curr_cnstrs
         | `Atom (`Arith (`Leq, t1, t2)) ->
            let cnstrs =
              linearize_inequality (`Lt, t2, t1) in
            adjoin cnstrs curr_cnstrs
         | `Atom (`Arith (`Lt, t1, t2)) ->
            let cnstrs =
              linearize_inequality (`Leq, t2, t1) in
            adjoin cnstrs curr_cnstrs
         | `Atom (`IsInt t) ->
            let cnstrs =
              linearize_inequality (`Lt, mk_floor srk t, t)
            in
            adjoin cnstrs curr_cnstrs
         | _ -> invalid_arg "purify: not a subformula of an implicant"
         end
      | _ -> invalid_arg "purify: not a subformula of an implicant"
    in
    let (pcons, lcons) = List.fold_left collect ([], []) implicant in
    linear_set_of {inequalities = pcons; integral = lcons}

end

(*
  lattice_hull P L =
  let F = { A1 x >= b1, A2 x > b2, A3 x = b3 } := P in
  let Cx + d \in Z := L in
  let recession_extension =
    { A1 x >= b1, A2 x > b, A3 x = b3, A1 r >= 0, A2 r >= 0
    ; A1(x - r) >= b1, A2(x - r) > b2, A3(x - r) = b3 }
  in
  let S = mk_solver (/\ {all_constraints}) in
  loop
    (fun (_S, _Q, m) -> Option.is_some m)
    (fun (S, Q, m) ->
      let Q1 = { recession_extension ; C(x - r) = C m(x) }
               |> local_project_onto m x
      in
      let Q = cl (DD.join Q Q1) in
      let S = Solver.add_constraints S (~(constraints of Q1)) in
      (S, Q, Solver.get_model S))
    (S, DD.bottom, Solver.get_model S)
 *)

module LocalProject : sig

  (** If [Y] is the set of original dimensions not in [onto_original],
      [lira_project binding m onto implicant = (P, L)] where
      - [P] and [L] are in the integer and fractional dimensions corresponding to
        original dimensions in [onto].
      - [m |= P /\ L] and
      - [P' /\ L'] |= exists Y. (Int(Y_int) /\ 0 <= Y_frac < 1) /\ implicant].
      Entailments are all modulo LIRA.
   *)
  val lira_project:
    DimensionBinding.t ->
    IntFracValuation.t -> onto_original:IntSet.t ->
    Linearized.p_linear_set -> Linearized.p_linear_set

  (** Let A be the set of (necesssarily) integer-fractional dimensions that
      are constrained in [linear_set] and B be the original dimensions
      corresponding to A acccording to [binding].

      Suppose A and B are disjoint (as subsets of integers).
      If [m |= linear_set],
      [project_onto_original m binding linear_set = (P, L)] is such that

      - [P] and [L] are in dimensions B
      - [m |= P /\ L] (where we interpret original dimensions [x] as [x_int + x_frac]),
      - If [ax <= b] is an inequality and in dimensions B,
        and
        [P /\ L /\_{x in B} x = x_int + x_frac /\ Int(x_int) /\ 0 <= x_frac < 1
          |= ax <= b] modulo LIRA, then
        [P /\ L |= ax <= b].

      The procedure has finite image, and each local projection is complete for
      inequality consequences, but not for integer consequences.
   *)
  val project_linset_onto_original:
    DimensionBinding.t -> IntFracValuation.t ->
    Linearized.p_linear_set -> Polyhedron.t * IntLattice.t

end = struct

  open Linearized

  let round_value ckind v =
    match ckind with
    | `Leq -> QQ.of_zz (QQ.ceiling v)
    | `Lt -> QQ.add (QQ.of_zz (QQ.floor v)) QQ.one

  let round_term binding cnstr_kind lower_bound m =
    let int_frac_m = IntFracValuation.of_assignment m in
    let ((inequalities, integral), rounded_term) =
      match cnstr_kind with
      | `Leq ->
         let (cond, v) = LinearizeTerm.ceiling binding int_frac_m
                           (fold_vector lower_bound)
         in
         (unfold_linear_formula cond, unfold_vector v)
      | `Lt ->
         let (cond, floored) = LinearizeTerm.floor binding int_frac_m
                                 (fold_vector lower_bound) in
         let v = unfold_vector floored
                 |> Linear.QQVector.add_term QQ.one Linear.const_dim
         in
         (unfold_linear_formula cond, v)
    (*
      | `Zero ->
         let (cond, v) =
           LinearizeTerm.floor binding int_frac_m (fold_vector lower_bound)
         in
         (unfold_linear_formula cond, unfold_vector v)
     *)
    in
    (rounded_term, inequalities, integral)

  let round_lower_bound binding: LatticePolyhedron.ceiling =
    {
      round_value = round_value
    ; round_term = round_term binding
    }

  let lira_project binding int_frac_m ~onto_original linset =
    let (p, l) = unfold_linear_set linset in
    let (ints_to_elim, fracs_to_elim) =
      DimensionBinding.fold
        (fun (ints_to_elim, fracs_to_elim) ~original_dim ~int_dim ~frac_dim ->
          if IntSet.mem original_dim onto_original then
            (ints_to_elim, fracs_to_elim)
          else
            (IntSet.add int_dim ints_to_elim, IntSet.add frac_dim fracs_to_elim))
        binding
        (IntSet.empty, IntSet.empty)
    in
    let all_inequalities =
      DimensionBinding.inequalities_for
        (fun ~original_dim ~frac_dim:_ ->
          not (IntSet.mem original_dim onto_original))
        binding
      |> BatEnum.append (Polyhedron.enum_constraints p)
    in
    let all_int_constraints =
      DimensionBinding.integer_constraints_for
        (fun ~original_dim ~int_dim:_ ->
          not (IntSet.mem original_dim onto_original))
        binding
      |> BatEnum.append (BatList.enum (IntLattice.basis l))
      |> BatEnum.append
           (BatList.enum [Linear.QQVector.of_term QQ.one Linear.const_dim])
    in
    (*
    let int_frac_defs =
      let defns = BatEnum.empty () in
      IntSet.iter (fun dim ->
          let (int_dim, frac_dim) = DimensionBinding.int_frac_dim_of dim binding in
          let v = Linear.QQVector.of_list
                    [(QQ.one, dim); (QQ.of_int (-1), int_dim); (QQ.of_int (-1), frac_dim)]
          in
          BatEnum.push defns (`Zero, v)
        ) onto_original;
      defns
    in
     *)
    let poly =
      (* Polyhedron.of_constraints (BatEnum.append all_inequalities int_frac_defs) *)
      Polyhedron.of_constraints all_inequalities
    in
    logf ~level:`trace "Polyhedron before projection: @[%a@]@;"
      (Polyhedron.pp Format.pp_print_int) poly;
    let poly_after_real =
      (* Integer constraints do not contain real variables *)
      Polyhedron.local_project (IntFracValuation.value_of int_frac_m)
        (BatList.of_enum (IntSet.enum fracs_to_elim))
        poly
    in
    (* [round_lower_bound] has to satisfy two properties:

     1. There exists a discrete subgroup of the reals that contains the
        { m(t): t a term in image(round_lower_bound), m a valuation }.
        This ensures that local projection has finite image.

     2. Each term in the image of [round_lower_bound] has to be free of
        fractional variables. This maintains the invariant that Int(-)
        atoms are pure, i.e., free of fractional variables, so that they
        can be left out of quantifier elimination for fractional variables.
     *)
    logf ~level:`trace "Polyhedron after real QE: @[%a@]@;"
      (Polyhedron.pp Format.pp_print_int) poly;
    let (poly_after_int, lattice_after_int, _) =
      LatticePolyhedron.local_project_cooper
        (IntFracValuation.value_of int_frac_m)
        ~eliminate:(BatArray.of_enum (IntSet.enum ints_to_elim))
        (`RoundLowerBound (round_lower_bound binding))
        ( poly_after_real
        , (IntLattice.hermitize (BatList.of_enum all_int_constraints))
        )
    in
    logf ~level:`debug "lira_local_project: onto_original: @[%a@]"
      IntSet.pp onto_original;
    logf ~level:`debug "Polyhedron after int QE: @[%a@]@;"
      (Polyhedron.pp Format.pp_print_int) poly_after_int;
    logf ~level:`debug "Lattice after int QE: @[%a@]@;"
      (IntLattice.pp Format.pp_print_int) lattice_after_int;
    fold_linear_set (poly_after_int, lattice_after_int)

  let hull m p l =
    let m = IntFracValuation.value_of m in
    logf ~level:`debug "Polyhedron before hull: @[%a@]@;"
      (Polyhedron.pp Format.pp_print_int) p;
    let hull = LatticePolyhedron.local_mixed_lattice_hull m (p, l) in
    logf ~level:`debug "Hull: @[%a@]@;"
      (Polyhedron.pp Format.pp_print_int) hull;
    hull

  let define_original binding original_dim =
    let (x_int, x_frac) =
      DimensionBinding.int_frac_dim_of original_dim binding
    in
    (`Zero, Linear.QQVector.of_list
              [ (QQ.one, original_dim)
              ; (QQ.of_int (-1), x_int)
              ; (QQ.of_int (-1), x_frac)])

  let collect_dimensions pred f cnstrs =
    BatEnum.fold
      (fun dims (_, v) ->
        (Linear.QQVector.fold
           (fun dim _ dims ->
             if dim <> Linear.const_dim && pred dim then
               let dims' =
                 IntSet.add (f dim) dims
               in dims'
             else dims)
           v dims
        )
      )
      IntSet.empty
      cnstrs

  let project_linset_onto_original binding m linset =
    (* [exists x_int, x_frac.
          x = x_int + x_frac /\ Int(x_int) /\ 0 <= x_frac < 1 /\ P /\ L]
       implies the same inequalities as
       [exists x_int, x_frac.
          x = x_int + x_frac /\ P /\ L]
       provided that [P |= 0 <= x_frac < 1] and [P] is the [L-hull] of itself.
     *)
    let (p, l) = Linearized.unfold_linear_set linset in
    let original_dims =
      collect_dimensions (fun _ -> true)
        (fun dim -> DimensionBinding.to_original_dim dim binding)
        (Polyhedron.enum_constraints p)
    in
    let x_frac_inequalities =
      DimensionBinding.inequalities_for
        (fun ~original_dim ~frac_dim:_ -> IntSet.mem original_dim original_dims)
        binding
      |> Polyhedron.of_constraints
    in
    let x_ints =
      DimensionBinding.integer_constraints_for
        (fun ~original_dim ~int_dim:_ -> IntSet.mem original_dim original_dims)
        binding
    in
    let p_with_bounds = Polyhedron.meet p x_frac_inequalities in
    let l_with_ints =
      List.rev_append (BatList.of_enum x_ints) (IntLattice.basis l)
      |> IntLattice.hermitize in
    let hulled = hull m p_with_bounds l_with_ints in
    let x_eq_int_frac =
      IntSet.fold (fun dim cnstrs -> define_original binding dim :: cnstrs)
        original_dims [] in
    let lineality =
      let open BatEnum in
      Polyhedron.enum_constraints hulled
      //@ (fun (ckind, v) ->
        match ckind with
        | `Zero -> Some v
        | _ -> None)
      |> BatList.of_enum
      |> List.rev_append (List.map (fun (_, v) -> v) x_eq_int_frac)
    in
    let pre_projection_p =
      Polyhedron.meet hulled
        (Polyhedron.of_constraints (BatList.enum x_eq_int_frac)) in
    let elim_dimensions =
      collect_dimensions
        (fun dim -> not (IntSet.mem dim original_dims))
        (fun x -> x)
        (Polyhedron.enum_constraints pre_projection_p)
    in
    logf ~level:`trace "local_project_linset_onto_original: original dimensions @[%a@], elim dimensions: @[%a@]"
      IntSet.pp original_dims IntSet.pp elim_dimensions;
    logf ~level:`trace "pre_projection: @[%a@]@;"
      (Polyhedron.pp Format.pp_print_int) pre_projection_p;
    let p_in_original =
      Polyhedron.project (IntSet.to_list elim_dimensions) pre_projection_p in
    let pre_projection_l =
      (* WARNING: This makes the lattice impure. *)
      IntLattice.basis l
      |> List.rev_append lineality
      |> IntLattice.hermitize
    in
    let l_in_original =
      IntLattice.project
        (fun dim -> IntSet.mem dim original_dims || dim = Linear.const_dim)
        pre_projection_l in
    logf ~level:`debug "Polyhedron in original dimensions: @[%a@]@;"
      (Polyhedron.pp Format.pp_print_int) p_in_original;
    logf ~level:`debug "Lattice before lineality: @[%a@]@;"
      (IntLattice.pp Format.pp_print_int) l;
    logf ~level:`debug "Lattice before projection: @[%a@]@;"
      (IntLattice.pp Format.pp_print_int) pre_projection_l;
    logf ~level:`debug "Lattice in original dimensions: @[%a@]@;"
      (IntLattice.pp Format.pp_print_int) l_in_original;
    (p_in_original, l_in_original)

end

module TermProjection : sig

  val project:
    'a Syntax.context -> 'a Syntax.formula -> ('a Syntax.arith_term) array ->
    DD.closed DD.t

end = struct

  (** P is a polyhedron in constrained dimensions [0, ..., len(term array)]. *)
  type t = DD.closed DD.t

  let join p1 p2 = DD.join p1 p2

  let bottom ambient_dim = Polyhedron.dd_of ambient_dim Polyhedron.bottom

  let top ambient_dim = Polyhedron.dd_of ambient_dim Polyhedron.top

  let original_dim_of_symbol base sym = base + Syntax.int_of_symbol sym

  let symbol_of_original_dim base dim =
    if dim >= base then Some (Syntax.symbol_of_int (dim - base))
    else None

  let term_of_dim terms i =
    if i >= 0 && i < Array.length terms then
      Some (terms.(i))
    else None

  let term_of srk terms v =
    Linear.term_of_vec srk
      (fun dim ->
        if dim >= 0 && dim < Array.length terms
        then terms.(dim)
        else if dim = Linear.const_dim then Syntax.mk_real srk QQ.one
        else assert false)
      v

  let formula_of_constraints srk terms cnstrs =
    let cnstrs = BatList.of_enum cnstrs in
    logf ~level:`trace "formula_of: blocking: %a"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
         (fun fmt (ckind, v) ->
           let pp_vector = Linear.QQVector.pp_term Format.pp_print_int in
           match ckind with
           | `Zero -> Format.fprintf fmt "@[%a = 0@]" pp_vector v
           | `Nonneg -> Format.fprintf fmt "@[%a >= 0@]" pp_vector v
           | `Pos -> Format.fprintf fmt "@[%a > 0@]" pp_vector v
         )
      )
      cnstrs;
    let inequalities =
      BatList.map
        (fun (ckind, v) ->
          let rhs = term_of srk terms v in
          let zero = Syntax.mk_real srk QQ.zero in
          match ckind with
          | `Zero -> Syntax.mk_eq srk zero rhs
          | `Nonneg -> Syntax.mk_leq srk zero rhs
          | `Pos -> Syntax.mk_lt srk zero rhs
        )
        cnstrs
    in
    let phi = Syntax.mk_and srk inequalities in
    logf ~level:`debug "formula_of: result: @[%a@]@;" (Syntax.Formula.pp srk) phi;
    phi

  let formula_of srk terms dd =
    formula_of_constraints srk terms (DD.enum_constraints dd)

  let make_binding phi terms =
    (* Reserve |terms| dimensions in both the original-dimension space and
       in the integer-fractional space.
       The former allows us to insert constraints defining each term,
       and the latter allows the client to interpret the result per the
       indices of terms in the array.
     *)
    let base = Array.length terms in
    let dim_binding =
      BatEnum.fold (fun binding i -> DimensionBinding.add i binding)
        (DimensionBinding.empty ~initial:base)
        (BatEnum.(--^) 0 (Array.length terms))
      |> Syntax.Symbol.Set.fold
           (fun sym binding ->
             DimensionBinding.add (original_dim_of_symbol base sym) binding)
           (Syntax.symbols phi)
    in
    let symbol_binding =
      {
        dim_of_symbol = (original_dim_of_symbol base)
      ; symbol_of_dim = (symbol_of_original_dim base)
      ; term_of_dim = (term_of_dim terms)
      }
    in
    Context.make symbol_binding dim_binding

  let define_terms srk binding terms interp =
    Array.fold_left (fun (linearized, i) term ->
        let (lincond, linterm) =
          LinearizeTerm.linearize srk binding term interp in
        let (int_dim, frac_dim) =
          DimensionBinding.int_frac_dim_of i
            (Context.dimension_binding binding) in
        let cnstr =
          ( `Zero
          , Linearized.unfold_vector linterm
            |> Linear.QQVector.add_term (QQ.of_int (-1)) int_dim
            |> Linear.QQVector.add_term (QQ.of_int (-1)) frac_dim
            |> Linearized.fold_vector
          )
        in
        ( LinearizeTerm.conjoin
            { lincond with inequalities = cnstr :: lincond.inequalities }
            linearized
        , i + 1 ))
      (Linearized.tru, 0) terms
    |> fst

  let symbols_in_terms terms =
    Array.fold_left
      (fun symbols term -> Syntax.Symbol.Set.union symbols (Syntax.symbols term))
      Syntax.Symbol.Set.empty
      terms

  let model_satisfies srk terms interp p =
    let term_symbols = symbols_in_terms terms in
    let solver = Smt.StdSolver.make srk in
    let formula_of_model =
      Syntax.Symbol.Set.fold (fun symbol conjuncts ->
          let r = Interpretation.real interp symbol in
          Syntax.mk_eq srk (Syntax.mk_const srk symbol) (Syntax.mk_real srk r) :: conjuncts)
        term_symbols []
      |> Syntax.mk_and srk
    in
    let phi = formula_of_constraints srk terms (Polyhedron.enum_constraints p) in
    Smt.StdSolver.add solver [formula_of_model; Syntax.mk_not srk phi];
    let check_model = match Smt.StdSolver.get_model solver with
      | `Sat _ ->
         Some
           (Format.asprintf "model @[%a@] does not satisfy @[%a@]@;"
              (Syntax.Formula.pp srk) formula_of_model
              (Syntax.Formula.pp srk) phi)

      | `Unsat -> None
      | `Unknown -> Some "unknown"
    in
    check_model

  let of_model srk binding terms phi = function
    | `LIRA interp ->
       let implicant = Interpretation.select_implicant interp phi in
       begin match implicant with
       | None -> failwith "Lira: Cannot produce implicant"
       | Some implicant ->
          logf ~level:`trace "Lira: of_model: binding: @[%a@]@;"
            DimensionBinding.pp (Context.dimension_binding binding);

          let () =
            Syntax.Symbol.Set.iter
              (fun symbol ->
                logf ~level:`trace "Lira: Binding @[%a@]:@[%a@] to original dimension %d@;"
                  (Syntax.pp_symbol srk) symbol
                  Syntax.pp_typ (Syntax.typ_symbol srk symbol)
                  (Context.dim_of_symbol binding symbol)
              )
              (Syntax.symbols phi)
          in

          let implicant =
            (* Int(1) is always implicit *)
            Syntax.mk_is_int srk (Syntax.mk_real srk QQ.one) :: implicant
          in
          let linset = LinearizeFormula.purify_implicant srk binding
                         interp implicant in
          let (p, l) = Linearized.unfold_linear_set linset in
          logf ~level:`trace "Lira: purified implicant: @[%a@]@; AND @[%a@]@;"
            (Polyhedron.pp Format.pp_print_int) p
            (IntLattice.pp Format.pp_print_int) l;
          let term_constraints = define_terms srk binding terms interp in
          let (inequalities, integral) =
            Linearized.unfold_linear_formula term_constraints in
          let linset_with_term_definitions =
            ( Polyhedron.meet
                (Polyhedron.of_constraints
                   (BatList.enum inequalities)) p
            , List.rev_append integral
                (IntLattice.basis l)
              |> IntLattice.hermitize
            )
            |> Linearized.fold_linear_set
          in
          let onto_original =
            BatEnum.(--^) 0 (Array.length terms)
            |> IntSet.of_enum in
          logf ~level:`trace "@\nonto_original: @[%a@]@;"
            IntSet.pp onto_original;
          let dim_binding = Context.dimension_binding binding in
          let valuation = Context.valuation_of binding interp in
          let (result, _l) =
            LocalProject.lira_project dim_binding valuation ~onto_original
              linset_with_term_definitions
            |> LocalProject.project_linset_onto_original dim_binding valuation
          in
          let () =
            if Log.level_leq !my_verbosity_level `debug then
              match model_satisfies srk terms interp result with
              | Some err -> failwith err
              | None -> ()
          in
          let dd = Polyhedron.dd_of (Array.length terms) result
          in
          dd
       end
    | _ -> assert false

  let project (srk: 'a Syntax.context) phi terms =
    let binding = make_binding phi terms in
    let of_model = of_model srk binding terms phi in
    let formula_of = formula_of srk terms in
    let domain: ('a, t) Abstract.domain =
      {
        join
      ; of_model
      ; formula_of
      ; top = top (Array.length terms)
      ; bottom = bottom (Array.length terms)
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

end

type dimension_binding = DimensionBinding.t
type 'a context = 'a Context.t

let empty = DimensionBinding.empty

let add_dimension = DimensionBinding.add

(*
let symbol_of binding dim =
  DimensionBinding.to_original_dim dim
    (Context.dimension_binding binding)
  |> Context.symbol_of_dim binding

let int_frac_dimensions_of binding sym =
  let open Context in
  DimensionBinding.int_frac_dim_of (dim_of_symbol binding sym)
    (dimension_binding binding)
 *)

let int_frac_dim_of = DimensionBinding.int_frac_dim_of
let original_dim_of = DimensionBinding.to_original_dim

let make = Context.make

let linearize srk binding interp term =
  let (linfml, v) =
    LinearizeTerm.linearize srk binding term interp in
  let (inequalities, integral) = Linearized.unfold_linear_formula linfml in
  let v = Linearized.unfold_vector v in
  let (p, l) = ( Polyhedron.of_constraints (BatList.enum inequalities)
               , IntLattice.hermitize integral ) in
  ((p, l), v)

let lira_implicant_of_implicant binding srk interp implicant =
  LinearizeFormula.purify_implicant binding srk interp implicant
  |> Linearized.unfold_linear_set

let local_project_int_frac binding m ~onto_original linset =
  LocalProject.lira_project binding (IntFracValuation.of_assignment m)
    ~onto_original:(IntSet.of_list onto_original)
    (Linearized.fold_linear_set linset)
  |> Linearized.unfold_linear_set

let local_project_onto_original binding m (p, l) =
  let linset = Linearized.fold_linear_set (p, l) in
  LocalProject.project_linset_onto_original binding
    (IntFracValuation.of_assignment m) linset

let project srk phi terms =
  TermProjection.project srk phi terms
