(** A LIRA vector is a vector where each coordinate is the coefficient of an
    integer-valued variable or the coefficient of a real-valued fractional
    variable.
    A LIRA vector exists in the context of an environment mapping "original"
    variables x to integer-valued floor(x) and fractional-valued frac(x)
    in the LIRA vector.

   - Syntax-vector conversion.
     Model-based term linearization: This turns LIRA terms into a LIRA vector.

     Given a term [t1] in LIRA, and a point [m], we can compute a term [t2]
     that is linear in integer and fractional variables
     and a condition [phi] such that m |= phi |= t1 = t2.
     There are finitely many such [phis], and these correspond to a case analysis
     on the whole space.

     For this to make sense, we should have a context that maps a variable in [t1]
     to integer and fractional variables in [t2].
     Moreover, this should be consistent over the whole formula, rather than
     having fresh variables created ad-hoc.
     The context is an implicit environment expressing the constraint
     [x = x_{floor(x)} + x_{frac(x)}] for each variable [x].

   - LIRA vector-standard vector conversion: Converting between a LIRA vector
     and a vector in the original variables.
 *)

module IntMap = SrkUtil.Int.Map
module IntSet = SrkUtil.Int.Set

type linear_formula =
  {
    inequalities: (Polyhedron.constraint_kind * Linear.QQVector.t) list
  ; integral: Linear.QQVector.t list
  }

let to_inequality srk (ckind, v) =
  let zero = Syntax.mk_zero srk in
  let op = match ckind with
    | `Zero -> Syntax.mk_eq srk zero
    | `Nonneg -> Syntax.mk_leq srk zero
    | `Pos -> Syntax.mk_lt srk zero
  in op (Linear.of_linterm srk v)

let tru = {inequalities = []; integral = []}

let bounds_for_frac_dim frac_dim =
  let lower_bound = (`Nonneg, Linear.QQVector.of_term QQ.one frac_dim) in
  let upper_bound = (`Pos,
                     Linear.QQVector.of_term (QQ.of_int (-1)) frac_dim
                     |> Linear.QQVector.add_term QQ.one Linear.const_dim)
  in
  [lower_bound; upper_bound]

module DimensionBinding : sig

  type t

  (** [add srk x t] adds a fresh integer symbol [x_int] and a fresh fractional
      symbol [x_frac] to the context if [x] is not already in [t], and binds
      (the dimension corresponding to) [x] to these symbols (corresponding
      dimensions).
   *)
  val add: 'a Syntax.context -> Syntax.symbol -> t -> t

  val of_formula: 'a Syntax.context -> 'a Syntax.formula -> t

  val int_frac_dim_of: int -> t -> int * int

  val to_original_dim: int -> t -> int

  val fold: ('a -> original_dim:int -> int_dim:int -> frac_dim:int -> 'a) -> t -> 'a -> 'a

  val integer_constraints: t -> Linear.QQVector.t BatEnum.t

  val inequalities: t -> (Polyhedron.constraint_kind * Linear.QQVector.t) BatEnum.t

  (** Produce an extended interpretation that also assigns integer and fractional
      variables
   *)
  val extend_interp: t -> 'a Interpretation.interpretation -> (int -> QQ.t)

end = struct

  type t =
    {
      to_int_frac: (int * int) IntMap.t
    ; from_int_frac: int IntMap.t
    }

  let empty: t =
    {
      to_int_frac = IntMap.empty
    ; from_int_frac = IntMap.empty
    }

  let add srk sym t =
    let original_dim = Syntax.int_of_symbol sym in
    try
      let _ = IntMap.find original_dim t.to_int_frac in
      t
    with Not_found ->
      let name = match Syntax.symbol_name srk sym with
          Some name -> name
        | None -> ""
      in
      let int_name = Format.sprintf "%s_int" name in
      let frac_name = Format.sprintf "%s_frac" name in
      let (int_dim, frac_dim) =
        ( Syntax.int_of_symbol (Syntax.mk_symbol srk ~name:int_name `TyInt)
        , Syntax.int_of_symbol (Syntax.mk_symbol srk ~name:frac_name `TyReal)
        ) in
      {
        to_int_frac = IntMap.add original_dim
                        (int_dim, frac_dim)
                        t.to_int_frac
      ; from_int_frac = IntMap.add int_dim original_dim t.from_int_frac
                        |> IntMap.add frac_dim original_dim
      }

  let of_formula srk phi =
    Syntax.Symbol.Set.fold (add srk) (Syntax.symbols phi) empty

  let int_frac_dim_of x t = IntMap.find x t.to_int_frac

  let to_original_dim x t = IntMap.find x t.from_int_frac

  (*
  let is_int_dim x t =
    try
      let original_dim = IntMap.find x t.from_int_frac in
      let (int_dim, _) = IntMap.find original_dim t.to_int_frac in
      x = int_dim
    with Not_found -> false

  let is_frac_dim x t =
    try
      let original_dim = IntMap.find x t.from_int_frac in
      let (_, frac_dim) = IntMap.find original_dim t.to_int_frac in
      x = frac_dim
    with Not_found -> false

  let is_original_dim x t =
    IntMap.mem x t.to_int_frac
   *)

  let fold (f: 'a -> original_dim:int -> int_dim:int -> frac_dim:int -> 'a) t initial =
    IntMap.fold
      (fun original_dim (int_dim, frac_dim) curr ->
        f curr ~original_dim:original_dim ~int_dim:int_dim ~frac_dim:frac_dim) t.to_int_frac initial

  let integer_constraints t =
    let cnstrs = BatEnum.empty () in
    fold (fun () ~original_dim:_ ~int_dim ~frac_dim:_ ->
        BatEnum.push cnstrs (Linear.QQVector.of_term QQ.one int_dim);
        ()) t ();
    cnstrs

  let inequalities t =
    fold (fun bds ~original_dim:_ ~int_dim:_ ~frac_dim ->
        BatEnum.append (BatList.enum (bounds_for_frac_dim frac_dim)) bds)
      t (BatEnum.empty ())

  let extend_interp binding interpretation x =
    let extended_interp =
      fold (fun curr ~original_dim ~int_dim ~frac_dim ->
          let original_value = Interpretation.real interpretation
                                 (Syntax.symbol_of_int original_dim) in
          let intval = QQ.of_zz (QQ.floor original_value) in
          Interpretation.add_real
            (Syntax.symbol_of_int int_dim) intval curr
          |> Interpretation.add_real (Syntax.symbol_of_int frac_dim)
               (QQ.sub original_value intval)
        )
        binding
        interpretation
    in
    Interpretation.real extended_interp (Syntax.symbol_of_int x)

end

let to_formula srk binding linear_phi =
  let to_isint v =
    Syntax.mk_is_int srk (Linear.of_linterm srk v)
  in
  let int_constraints =
    BatEnum.append (DimensionBinding.integer_constraints binding)
      (BatList.enum linear_phi.integral)
    |> BatEnum.map to_isint
  in
  let inequalities =
    BatEnum.append (DimensionBinding.inequalities binding)
      (BatList.enum linear_phi.inequalities)
    |> BatEnum.map (to_inequality srk) in
  BatList.of_enum (BatEnum.append int_constraints inequalities)

module VectorConversion : sig

  val to_int_frac: DimensionBinding.t -> Linear.QQVector.t -> Linear.QQVector.t

  val to_int_and_floor: DimensionBinding.t -> Linear.QQVector.t -> Linear.QQVector.t

end = struct

  let to_int_frac binding v =
    Linear.QQVector.fold (fun dim coeff v' ->
        try
          let (int_dim, frac_dim) = DimensionBinding.int_frac_dim_of dim binding
          in
          Linear.QQVector.add_term coeff int_dim v'
          |> Linear.QQVector.add_term coeff frac_dim
        with Not_found ->
          Linear.QQVector.add_term coeff dim v'
      )
      v
      Linear.QQVector.zero

  let to_int_and_floor binding v =
    Linear.QQVector.fold (fun dim coeff v' ->
        try
          let original_dim = DimensionBinding.to_original_dim dim binding in
          let (int_dim, frac_dim) =
            DimensionBinding.int_frac_dim_of original_dim binding in
          if dim = frac_dim then
            Linear.QQVector.add_term coeff original_dim v'
            |> Linear.QQVector.add_term (QQ.negate coeff) int_dim
          else
            v'
        with Not_found ->
          Linear.QQVector.add_term coeff dim v'
      )
      v
      Linear.QQVector.zero
end

module LinearizeTerm: sig

  type lincond = linear_formula

  exception Nonlinear

  (** [linearize srk binding term model = (phi, v)] where
      [model |= phi |= term = of_linterm(v)], where the entailment is modulo
      LIRA, the equalities [x = x_int + x_frac], bounds for [x_frac],
      and integrality constraints for [x_int], that appear in [binding].
   *)
  val linearize:
    'a Syntax.context -> DimensionBinding.t -> 'a Syntax.arith_term ->
    (int -> QQ.t) ->
    lincond * Linear.QQVector.t

  (** Given a LIRA vector [t] under LIRA context [binding],
      and a valuation [m] that has been extended to assign integer and fractional
      variables,
      [floor binding m t = (phi, t')] where [m |= phi] and
      [phi |= floor(t) = t'].
   *)
  val floor: DimensionBinding.t -> (int -> QQ.t) -> Linear.QQVector.t ->
             lincond * Linear.QQVector.t

  val ceiling: DimensionBinding.t -> (int -> QQ.t) -> Linear.QQVector.t ->
               lincond * Linear.QQVector.t

  val conjoin: lincond -> lincond -> lincond

end = struct

  module DB = DimensionBinding

  type lincond = linear_formula

  let conjoin phi1 phi2 =
    {
      inequalities = List.rev_append phi1.inequalities phi2.inequalities
    ; integral = List.rev_append phi1.integral phi2.integral
    }

  exception Nonlinear

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
                raise Nonlinear
            )
            v1
            outer_sop
      )
      v2
      Linear.QQVector.zero

  let floor binding m v =
    let (linearized_int, residue_to_floor, int_cond) =
      DB.fold (fun (linearized, v, cond) ~original_dim:_ ~int_dim ~frac_dim:_ ->
          let (a, v') = Linear.QQVector.pivot int_dim v in
          let remainder =
            let x = QQ.mul a (m int_dim) in
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
    in
    let (sum_of_fractional, fractional, residue_to_floor) =
      DB.fold (fun (sum, fractional, v) ~original_dim:_ ~int_dim:_ ~frac_dim ->
          let (coeff, v') = Linear.QQVector.pivot frac_dim v in
          let fraction = m frac_dim in
          ( QQ.add (QQ.mul coeff fraction) sum
          , Linear.QQVector.add_term coeff frac_dim fractional
          , v' )
        )
        binding
        (QQ.zero, Linear.QQVector.zero, residue_to_floor)
    in
    let y =
      Linear.QQVector.fold (fun dim coeff value ->
          if dim <> Linear.const_dim then
            invalid_arg "floor: cannot take the floor of a non-LIRA vector"
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
             (Linear.QQVector.add_term (QQ.sub frac_y n) Linear.const_dim fractional))
          ; (`Pos,
             Linear.QQVector.negate fractional
             |> Linear.QQVector.add_term
                  (QQ.add n (QQ.sub QQ.one frac_y)) Linear.const_dim) ]
      }
    in
    (cond, linearized)

  let ceiling binding m v =
    let (cond, v') = floor binding m (Linear.QQVector.negate v) in
    (cond, Linear.QQVector.negate v')

  let linearize srk binding term m =
    let open Syntax in
    ArithTerm.eval srk
      (function
       | `Real r -> (tru, Linear.QQVector.of_term r Linear.const_dim)
       | `App (x, l) when l = [] ->
          begin try
              let (int_dim, frac_dim) =
                DB.int_frac_dim_of (int_of_symbol x) binding in
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
          let (c, v2') = Linear.QQVector.pivot Linear.const_dim v2 in
          if Linear.QQVector.is_zero v2' then
            (conjoin phi1 phi2, (Linear.QQVector.scalar_mul (QQ.inverse c) v1))
          else
            invalid_arg "linearize: cannot divide by a non-constant"
       | `Binop (`Mod, (_phi1, _v1), (_phi2, _v2)) ->
          invalid_arg "linearize: Can't handle mod for now"
       | `Unop (`Floor, (phi, v)) ->
          let (floor_phi, v') = floor binding m v in
          (conjoin floor_phi phi, v')
       | `Unop (`Neg, (phi, v)) ->
          (phi, Linear.QQVector.negate v)
       | `Ite (_ite_cond, _, _) ->
          invalid_arg "linearize: ite should have been simplified away"
       | `Select _ ->
          invalid_arg "linearize: select not handled yet"
      )
      term

end

module LinearizeFormula : sig

  (** Given an [implicant] computed by [Interpretation.select_implicant],
      and [binding] that contains all variables in [implicant] in its support
      (for original variables),
      [purify_implicant srk binding m implicant = (P, L)] where
      - [P] is only in [x_int] and [x_frac] dimensions that occur in
        [binding].
      - [L] is only in [x_int] dimensions that occur in [binding].
      - m |= P /\ L, where [m] is extended to
        [x_int] and [x_frac] dimensions according to the expected semantics.
      - [P /\ L |= phi] modulo LIRA and
        equalities [x] = [x_int] + [x_frac] (and integrality and bound constraints).
   *)
  val purify_implicant:
    'a Syntax.context -> DimensionBinding.t ->
    'a Interpretation.interpretation ->
    'a Syntax.formula list ->
    linear_formula

end = struct

  open Syntax

  let linearize_inequality srk binding m (rel, t1, t2) =
    let (cond1, linear1) = LinearizeTerm.linearize srk binding t1 m in
    let (cond2, linear2) = LinearizeTerm.linearize srk binding t2 m in
    let v = Linear.QQVector.sub linear2 linear1 in
    let cond = LinearizeTerm.conjoin cond1 cond2 in
    let constrnt = match rel with
      | `Lt -> (`Pos, v)
      | `Leq -> (`Nonneg, v)
      | `Eq -> (`Zero, v)
    in
    (constrnt :: cond.inequalities, cond.integral)

  let purify_implicant srk binding interp implicant =
    let m = DimensionBinding.extend_interp binding interp in
    let adjoin (pcons, lcons) (polyhedral_cnstrs, lattice_cnstrs) =
      ( BatList.rev_append pcons polyhedral_cnstrs
      , BatList.rev_append lcons lattice_cnstrs
      )
    in
    let collect curr_cnstrs literal =
      match Formula.destruct srk literal with
      | `Proposition (`App (_, _))
        | `Proposition (`Var _) ->
         invalid_arg "purify: LIRA cannot handle propositional atoms"
      | `Atom (`ArrEq (_a1, _a2)) ->
         invalid_arg "purify: LIRA cannot handle array terms"
      | `Atom (`Arith ineq) ->
         let cnstrs = linearize_inequality srk binding m ineq in
         adjoin cnstrs curr_cnstrs
      | `Atom (`IsInt t) ->
         let cnstrs =
           linearize_inequality srk binding m (`Eq, t, mk_floor srk t)
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
              then
                linearize_inequality srk binding m (`Lt, t1, t2)
              else
                linearize_inequality srk binding m (`Lt, t2, t1)
            in
            adjoin cnstrs curr_cnstrs
         | `Atom (`Arith (`Leq, t1, t2)) ->
            let cnstrs =
              linearize_inequality srk binding m (`Lt, t2, t1) in
            adjoin cnstrs curr_cnstrs
         | `Atom (`Arith (`Lt, t1, t2)) ->
            let cnstrs =
              linearize_inequality srk binding m (`Leq, t2, t1) in
            adjoin cnstrs curr_cnstrs
         | `Atom (`IsInt t) ->
            let cnstrs =
              linearize_inequality srk binding m (`Eq, t, mk_floor srk t)
            in
            adjoin cnstrs curr_cnstrs
         | _ -> invalid_arg "purify: not a subformula of an implicant"
         end
      | _ -> invalid_arg "purify: not a subformula of an implicant"
    in
    let (pcons, lcons) = List.fold_left collect ([], []) implicant in
    { inequalities = pcons
    ; integral = lcons }

end

type dimension_binding = DimensionBinding.t

let mk_lira_context srk phi = DimensionBinding.of_formula srk phi

let fold = DimensionBinding.fold

let add_binding = DimensionBinding.add

let int_frac_dim_of = DimensionBinding.int_frac_dim_of

let to_int_frac = VectorConversion.to_int_frac

let to_int_and_floor = VectorConversion.to_int_and_floor

let floor = LinearizeTerm.floor

let ceiling = LinearizeTerm.ceiling

let lira_implicant_of_implicant = LinearizeFormula.purify_implicant

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

let round_lower_bound binding cnstr_kind lower_bound m =
  let (implicant, rounded_term) =
    match cnstr_kind with
    | `Nonneg -> LinearizeTerm.ceiling binding m lower_bound
    | `Pos -> let (cond, floored) = LinearizeTerm.floor binding m lower_bound in
              (cond, Linear.QQVector.add_term QQ.one Linear.const_dim floored)
    | `Zero ->
       assert false
  in
  (rounded_term, implicant.inequalities, implicant.integral)

let local_project srk binding interp ~eliminate_original implicant =
  let eliminate_original = IntSet.of_list eliminate_original in
  let (ints_to_eliminate, fracs_to_eliminate) =
    fold (fun (ints_to_elim, fracs_to_elim) ~original_dim ~int_dim ~frac_dim ->
        if IntSet.mem original_dim eliminate_original then
          (int_dim :: ints_to_elim, frac_dim :: fracs_to_elim)
        else
          (ints_to_elim, fracs_to_elim)
      )
      binding
      ([], [])
  in
  let all_inequalities =
    BatEnum.append
      (DimensionBinding.inequalities binding) (BatList.enum implicant.inequalities)
  in
  let all_ints =
    BatEnum.append (DimensionBinding.integer_constraints binding)
      (BatList.enum implicant.integral) in
  let m = DimensionBinding.extend_interp binding interp in
  let poly_after_real =
    Polyhedron.local_project m fracs_to_eliminate
      (Polyhedron.of_constraints all_inequalities)
  in
  (* Local projection eliminating integer dimensions must use mixed Cooper
     because fractional dimensions for variables to keep still exist.
     The difference between mixed Cooper and pure Cooper is that the greatest
     lower bound term [t] in [t <= x_int] is strengthened to
     [ceiling(t) <= x_int]; this ensures local projection has finite image.
   *)
  let (poly_after_int, lattice_after_int) =
    LatticePolyhedron.local_project_cooper m
      ~eliminate:ints_to_eliminate poly_after_real
      ~round_lower_bound:(round_lower_bound binding)
      (IntLattice.hermitize (BatList.of_enum all_ints))
  in
  (* We have to take the L-hull here to preserve strongest consequences.
     Taking L-hull after completing local projection is not the same as
     taking the L-hull at the end of each iteration; the former can introduce
     more L-points than necessary, even when L is the standard lattice.
   *)
  LatticePolyhedron.mixed_lattice_hull srk poly_after_int lattice_after_int
