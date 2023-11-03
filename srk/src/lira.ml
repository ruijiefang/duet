(** This module defines LIRA vectors (implicitly) and LIRA formulas.

    - A LIRA term (formula) is a term (formula) in the FOL with equality over
      (QQ; +, scalar multiplication, floor(-); >, >=, Int(-)).

    - A LIRA vector is a QQVector where every coordinate corresponds to either
      an integer-valued variable or a real-valued fractional variable
      (i.e., 0 <= x < 1).
      When coordinates mean coefficients, it represents a term
      [sum_i a_i (x_int)_i + sum_j b_j (x_frac)_j] that is linear in
      integer and fractional variables.

      A LIRA vector exists in the context of a [dimension_binding] ("context"),
      which maps "original" variables [x] in LIRA terms/formulas to an
      integer-valued variable [x_int] and a fractional-valued variable [x_frac]
      in the LIRA vector.
      The context corresponds to constraints between [x] and its
      integer-fractional counterparts: for each original variable [x],
      [x = x_int + x_frac /\ 0 <= x_frac < 1 /\ Int(x_int)].

      LIRA vectors represent only a subset of LIRA terms: those that are linear
      in floor(v) and frac(v) (= v - floor(v)), for variables v.
      Nevertheless, any LIRA term is semantically equal to a LIRA vector (the
      linear term it represents) modulo some conditions, which can be expressed
      as a formula over LIRA vectors (that we call a [linear_formula] below).

    - A LIRA formula ([linear_formula]) is a positive conjunction of
      inequalities and integrality constraints in (terms represented by)
      LIRA vectors.
 *)

module IntMap = SrkUtil.Int.Map
module IntSet = SrkUtil.Int.Set

type linear_formula =
  {
    inequalities: (Polyhedron.constraint_kind * Linear.QQVector.t) list
  ; integral: Linear.QQVector.t list
  }

let tru = {inequalities = []; integral = []}

let bounds_for_frac_dim frac_dim =
  let lower_bound = (`Nonneg, Linear.QQVector.of_term QQ.one frac_dim) in
  let upper_bound = (`Pos,
                     Linear.QQVector.of_term (QQ.of_int (-1)) frac_dim
                     |> Linear.QQVector.add_term QQ.one Linear.const_dim)
  in
  [lower_bound; upper_bound]

module DimensionBinding : sig
  (** A dimension binding associates a dimension [x] ("original dimension/variable") 
      with a pair of dimensions ([x_int], [x_frac]) ("integer dimension", 
      "fractional dimension"), such that:

      - The integer-fractional dimensions are guaranteed to be an initial segment
        of the natural numbers, starting from 0.
      - Each integer dimension is even.
      - Each fractional dimension is odd.
 *)
  type t

  (** An assignment of [x_int] and [x_frac] variables to [QQ.t] *)
  type int_frac_valuation

  val empty: t

  (** [add x t] assigns [x] to a fresh integer dimension [x_int] and a fresh 
      fractional dimension [x_frac].
   *)
  val add: int -> t -> t

  val int_frac_dim_of: int -> t -> int * int

  (* val to_original_dim: int -> t -> int *)

  val fold: ('a -> original_dim:int -> int_dim:int -> frac_dim:int -> 'a) -> t -> 'a -> 'a

  val integer_constraints_for:
    (original_dim:int -> int_dim:int -> bool) -> t -> Linear.QQVector.t BatEnum.t

  val inequalities_for:
    (original_dim:int -> frac_dim:int -> bool) ->
    t -> (Polyhedron.constraint_kind * Linear.QQVector.t) BatEnum.t

  val valuation: t -> 'a Interpretation.interpretation -> int_frac_valuation

  val value_of: int_frac_valuation -> int -> QQ.t

  val to_int_frac_valuation: (int -> QQ.t) -> int_frac_valuation

end = struct

  type t = { to_int_frac: int IntMap.t
           ; from_int_frac: int IntMap.t
           }

  type int_frac_valuation = (int -> QQ.t)

  let empty =
    { to_int_frac = IntMap.empty
    ; from_int_frac = IntMap.empty
    }

  let add original_dim t =
    match IntMap.find_opt original_dim t.to_int_frac with
    | None ->
       begin match IntMap.max_binding_opt t.from_int_frac with
       | None ->
          { to_int_frac = IntMap.add original_dim 0 t.to_int_frac
          ; from_int_frac = IntMap.add 0 original_dim t.from_int_frac
          }
       | Some (curr_max, _) ->
          { to_int_frac = IntMap.add original_dim (curr_max + 1) t.to_int_frac
          ; from_int_frac = IntMap.add (curr_max + 1) original_dim t.from_int_frac
          }
       end
    | Some _ -> t
       
  let int_frac_dim_of x t =
    match IntMap.find_opt x t.to_int_frac with
    | Some dim -> (2 * dim, 2 * dim + 1)
    | None -> raise Not_found

  let to_original_dim x t =
    if x mod 2 = 0 then IntMap.find (x mod 2) t.from_int_frac
    else IntMap.find ((x - 1) mod 2) t.from_int_frac

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

  let inequalities_for select t =
    fold (fun bds ~original_dim ~int_dim:_ ~frac_dim ->
        if select ~original_dim ~frac_dim then
          BatEnum.append (BatList.enum (bounds_for_frac_dim frac_dim)) bds
        else
          bds)
      t (BatEnum.empty ())

  let valuation t interpretation x =
    let v =
      Interpretation.real interpretation
        (Syntax.symbol_of_int (to_original_dim x t)) in
    let intval = QQ.of_zz (QQ.floor v) in
    if x mod 2 = 0 then intval else QQ.sub v intval

  let value_of valuation dim = valuation dim

  let to_int_frac_valuation m = m

end

module LinearizeTerm: sig

  (** A linear condition is a linear formula where Int(-) constraints are
      pure, i.e., they do not contain any real-valued variables.
   *)
  type lincond = linear_formula

  exception Nonlinear

  (** Given a [term] that is in original variables, a [binding] whose
      domain contains {int_of_symbol(x): x in symbols(term)}, 
      and an interpretation [m],
      [linearize srk binding ~int_of_symbol term m = (phi, v)] implies
      [m |= phi |= term = v], where the entailment is modulo
      LIRA, the equalities [x = x_int + x_frac], bounds for [x_frac],
      and integrality constraints for [x_int], that appear in [binding].
      Int literals in [phi] are pure, i.e., free of fractional variables.
   *)
  val linearize:
    'a Syntax.context -> DimensionBinding.t ->
    int_of_symbol: (Syntax.symbol -> int) ->
    'a Syntax.arith_term -> 'a Interpretation.interpretation ->
    lincond * Linear.QQVector.t

  (** Given a LIRA vector [t] under LIRA context [binding],
      and a valuation [m] for integer and fractional variables,
      [floor binding m t = (phi, t')] where [m |= phi],
      [phi |= floor(t) = t'], [t'] is free of fractional variables,
      and Int literals in [phi] are pure.
   *)
  val floor: DimensionBinding.t -> DimensionBinding.int_frac_valuation ->
             Linear.QQVector.t -> lincond * Linear.QQVector.t

  val ceiling: DimensionBinding.t -> DimensionBinding.int_frac_valuation ->
               Linear.QQVector.t -> lincond * Linear.QQVector.t

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
            let x = QQ.mul a (DimensionBinding.value_of m int_dim) in
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
          let fraction = (DimensionBinding.value_of m frac_dim) in
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

  let linearize srk binding ~int_of_symbol term interp =
    let m = DimensionBinding.valuation binding interp in
    Syntax.ArithTerm.eval srk
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
      a [binding] that contains {int_of_symbol(x): x in symbols(implicant)}
      in its domain, and an interpretation [interp] that satisfies [implicant],
      [lira_implicant srk ctx interp implicant = (p, l)] where:
    - [interp |= (p, l)].
    - [(p, l) |= implicant] modulo LIRA, equalities [x] = [x_int] + [x_frac],
      integrality constraints for [x_int], and bound constraints for [x_frac],
      for each variable x that occurs in [binding].
 *)  
  val purify_implicant:
    'a Syntax.context -> DimensionBinding.t ->
    int_of_symbol: (Syntax.symbol -> int) ->
    'a Interpretation.interpretation ->
    'a Syntax.formula list ->
    linear_formula

end = struct

  open Syntax

  let linearize_inequality srk binding int_of_symbol m (rel, t1, t2) =
    let (cond1, linear1) = LinearizeTerm.linearize srk binding ~int_of_symbol t1 m in
    let (cond2, linear2) = LinearizeTerm.linearize srk binding ~int_of_symbol t2 m in
    let v = Linear.QQVector.sub linear2 linear1 in
    let cond = LinearizeTerm.conjoin cond1 cond2 in
    let constrnt = match rel with
      | `Lt -> (`Pos, v)
      | `Leq -> (`Nonneg, v)
      | `Eq -> (`Zero, v)
    in
    (constrnt :: cond.inequalities, cond.integral)

  let purify_implicant srk binding ~int_of_symbol interp implicant =
    let adjoin (pcons, lcons) (polyhedral_cnstrs, lattice_cnstrs) =
      ( BatList.rev_append pcons polyhedral_cnstrs
      , BatList.rev_append lcons lattice_cnstrs
      )
    in
    let linearize_inequality = linearize_inequality srk binding int_of_symbol
                                 interp in
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
    { inequalities = pcons
    ; integral = lcons }

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

  (** [local_proj srk binding m onto implicant = (p, l)] where
      - [p] and [l] are in the integer and fractional dimensions corresponding to
        original dimensions in [domain(binding) - onto].
      - [m |= phi] and
      - [phi |=
             exists (integer and fractional variables x not in [onto]).
             (Int(x_int) /\ 0 <= x_frac < 1) /\ implicant]
      - If [implicant |= ax <= b], [phi |= ax <= b].
      Entailments are all modulo LIRA.
   *)
  val local_project:
    'a Syntax.context -> DimensionBinding.t ->
    DimensionBinding.int_frac_valuation -> onto_original:IntSet.t ->
    linear_formula -> DD.closed DD.t * IntLattice.t

end = struct

  let round_lower_bound binding cnstr_kind lower_bound m =
    let int_frac_m = DimensionBinding.to_int_frac_valuation m in
    let (implicant, rounded_term) =
      match cnstr_kind with
      | `Nonneg -> LinearizeTerm.ceiling binding int_frac_m lower_bound
      | `Pos -> let (cond, floored) = LinearizeTerm.floor binding int_frac_m
                                        lower_bound in
                (cond, Linear.QQVector.add_term QQ.one Linear.const_dim floored)
      | `Zero ->
         LinearizeTerm.floor binding int_frac_m lower_bound
    in
    (rounded_term, implicant.inequalities, implicant.integral)

  let local_project_linear binding int_frac_m ~onto_original implicant =
    (* TODO:
     - Bounds for fractional variables corresponding to variables to be kept
       should be left implicit. They come in only when we interface with SMT.

       (This doesn't look possible now, because we want everything in terms
       of original variables. An alternative is to include bounds only when
       they are used somewhere to linearize a term. They can then be left out
       of both the formula for QE and in the blocking clause for SMT.)

     - Model-based projection for L-hull may be interleaved with local
       projection; just use the same model, and block using the implicant
       for the hull, not the implicant in the outer loop.
     *)
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
      |> BatEnum.append (BatList.enum implicant.inequalities)
    in
    let all_int_constraints =
      DimensionBinding.integer_constraints_for
        (fun ~original_dim ~int_dim:_ ->
          not (IntSet.mem original_dim onto_original))
        binding
      |> BatEnum.append
           (BatList.enum implicant.integral)
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
    let poly_after_real =
      (* Integer constraints do not contain real variables *)
      Polyhedron.local_project (DimensionBinding.value_of int_frac_m)
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
    let (poly_after_int, lattice_after_int) =
      LatticePolyhedron.local_project_cooper
        (DimensionBinding.value_of int_frac_m)
        ~eliminate:(BatList.of_enum (IntSet.enum ints_to_elim))
        ~round_lower_bound:(round_lower_bound binding)
        poly_after_real
        (IntLattice.hermitize (BatList.of_enum all_int_constraints))
    in
    (poly_after_int, lattice_after_int)

  let local_project srk binding int_frac_m ~onto_original implicant =
    let (p, l) = local_project_linear binding int_frac_m ~onto_original
                   implicant in
    let lineality =
      let open BatEnum in
      Polyhedron.enum_constraints p
      //@ (fun (ckind, v) ->
        match ckind with
        | `Zero -> Some v
        | _ -> None)
      |> BatList.of_enum
    in
    let l' =
      IntLattice.basis l
      |> List.rev_append lineality
      |> IntLattice.hermitize
    in
    let hull = LatticePolyhedron.mixed_lattice_hull srk p l' in
    (hull, l')

end

module Projection : sig

  val project:
    'a Syntax.context -> 'a Syntax.formula -> ('a Syntax.arith_term) array ->
    DD.closed DD.t * IntLattice.t

end = struct

  (** (P, L) such that P is closed and P is the L-hull of P,
      and both are in dimensions 0, ... , 2 * len(term array) - 1,
      where an even offset from base corresponds to a term t in the array
      and an odd offset corresponds to floor(t).
      For term t = a[i], the dimension [2i] in the ambient
      space of [P] and [L] is the one for [t_int], and [2i + 1] is the one
      for [t_frac].

      [L] is a lattice of constraints, and always contains 1 
      (i.e., Int(1) is always implicit).
   *)
  type t = DD.closed DD.t * IntLattice.t

  let join (p1, l1) (p2, l2) =
    (DD.join p1 p2, IntLattice.intersect l1 l2)

  let bottom ambient_dim =
    ( Polyhedron.dd_of ambient_dim Polyhedron.bottom
    , IntLattice.hermitize [Linear.QQVector.of_term QQ.one Linear.const_dim]
    )

  let top ambient_dim =
    ( Polyhedron.dd_of ambient_dim Polyhedron.top
    , IntLattice.hermitize [Linear.QQVector.of_term QQ.one Linear.const_dim]
    )

  let original_dim_of_symbol base sym = base + Syntax.int_of_symbol sym

  (*
  let symbol_of_original_dim base dim =
    if dim >= base then Syntax.symbol_of_int (dim - base)
    else failwith "dimension corresponds to term in array"
   *)

  let of_model srk binding terms phi = function
    | `LIRA interp ->
       let implicant = Interpretation.select_implicant interp phi in
       begin match implicant with
       | None -> failwith "abstractLira: Cannot produce implicant"
       | Some implicant ->
          let lin_fml = LinearizeFormula.purify_implicant srk binding
                          ~int_of_symbol:(original_dim_of_symbol (Array.length terms))
                          interp implicant in
          let (term_constraints, onto, _) =
            Array.fold_left (fun (linearized, onto, i) term ->
                let (lincond, linterm) =
                  LinearizeTerm.linearize srk binding
                    ~int_of_symbol:(original_dim_of_symbol (Array.length terms))
                    term interp in
                let (int_dim, frac_dim) =
                  DimensionBinding.int_frac_dim_of i binding in
                let cnstr =
                  ( `Zero
                  , linterm
                    |> Linear.QQVector.add_term (QQ.of_int (-1)) int_dim
                    |> Linear.QQVector.add_term (QQ.of_int (-1)) frac_dim )
                in
                ( LinearizeTerm.conjoin
                    { lincond with inequalities = cnstr :: lincond.inequalities }
                    linearized
                , IntSet.add i onto
                , i + 1 ))
              (tru, IntSet.empty, 0) terms
          in
          let lin_fml = LinearizeTerm.conjoin term_constraints lin_fml in
          let int_frac_m = DimensionBinding.valuation binding interp in
          let (dd, l) =
            LocalProject.local_project srk binding int_frac_m ~onto_original:onto
              lin_fml in
          (dd, l)
       end
    | _ -> assert false

  let term_of srk binding terms v =
    let mk_multiple coeff term =
      if QQ.equal coeff QQ.zero then []
      else if QQ.equal coeff QQ.one then [term]
      else [Syntax.mk_mul srk [Syntax.mk_real srk coeff; term]]
    in
    let summands =
      Array.fold_left (fun (summands, i) term ->
          let (int_dim, frac_dim) =
            DimensionBinding.int_frac_dim_of i binding in
          let int_coeff = Linear.QQVector.coeff int_dim v in
          let frac_coeff = Linear.QQVector.coeff frac_dim v in
          let diff = QQ.sub int_coeff frac_coeff in
          let int_term = Syntax.mk_floor srk term in
          ( mk_multiple diff int_term @ mk_multiple frac_coeff term @ summands
          , i + 1)
        )
        ([], 0) terms
      |> (fun (l, _) -> List.rev l)
    in
    Syntax.mk_add srk summands

  let formula_of srk binding terms (p, l) =
    let inequalities =
      BatEnum.map
        (fun (ckind, v) ->
          let rhs = term_of srk binding terms v in
          let zero = Syntax.mk_real srk QQ.zero in
          match ckind with
          | `Zero -> Syntax.mk_eq srk zero rhs
          | `Nonneg -> Syntax.mk_eq srk zero rhs
          | `Pos -> Syntax.mk_lt srk zero rhs
        )
        (DD.enum_constraints p)
      |> BatList.of_enum
    in
    let integrality =
      List.map (fun v -> Syntax.mk_is_int srk (term_of srk binding terms v))
        (IntLattice.basis l)
    in
    Syntax.mk_and srk (List.rev_append integrality inequalities)

  let project (srk: 'a Syntax.context) phi terms =
    let base = Array.length terms in
    let binding =
      (* Dimensions for terms have to be added first, because dimensions for
         (P, L) are interpreted according to the array. *)
      BatEnum.fold (fun binding i -> DimensionBinding.add i binding)
        DimensionBinding.empty (BatEnum.(--^) 0 (Array.length terms))
      |> Syntax.Symbol.Set.fold
           (fun sym binding ->
             DimensionBinding.add (original_dim_of_symbol base sym) binding)
           (Syntax.symbols phi)
    in
    let of_model = of_model srk binding terms phi in
    let formula_of = formula_of srk binding terms in
    let domain: ('a, t) Abstract.domain =
      {
        join
      ; of_model
      ; formula_of
      ; top = top (Array.length terms * 2)
      ; bottom = bottom (Array.length terms * 2)
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    Abstract.Solver.abstract solver domain

end

type lira_context = DimensionBinding.t

let add_dimension = DimensionBinding.add

let lira_implicant_of_implicant srk binding
      ?(int_of_symbol = Syntax.int_of_symbol) interp phis =
  let linfml =
    LinearizeFormula.purify_implicant srk binding ~int_of_symbol interp phis in
  ( Polyhedron.of_constraints (BatList.enum (linfml.inequalities))
  , IntLattice.hermitize linfml.integral )

let linearize srk binding ?(int_of_symbol=Syntax.int_of_symbol) interp term =
  let (linfml, v) =
    LinearizeTerm.linearize srk binding ~int_of_symbol term interp in
  let (p, l) = ( Polyhedron.of_constraints (BatList.enum (linfml.inequalities))
               , IntLattice.hermitize linfml.integral ) in
  ((p, l), v)

let local_project srk binding interp ~onto_original (p, l) =
  let onto_original = IntSet.of_list onto_original in
  LocalProject.local_project srk binding
    (DimensionBinding.valuation binding interp) ~onto_original
    { inequalities = BatList.of_enum (Polyhedron.enum_constraints p)
    ; integral = IntLattice.basis l
    }

let project srk phi terms = Projection.project srk phi terms
