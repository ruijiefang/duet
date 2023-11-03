module V = Linear.QQVector
module P = Polyhedron
module L = IntLattice
module T = Linear.MakeLinearMap(QQ)(Int)(V)(V)

include Log.Make(struct let name = "srk.latticePolyhedron" end)

module MixedHull: sig

  val mixed_lattice_hull:
    'a Syntax.context -> Polyhedron.t -> IntLattice.t -> DD.closed DD.t

end = struct

  let to_inequality srk (ckind, v) =
    let zero = Syntax.mk_zero srk in
    let op = match ckind with
      | `Zero -> Syntax.mk_eq srk zero
      | `Nonneg -> Syntax.mk_leq srk zero
      | `Pos -> Syntax.mk_lt srk zero
    in op (Linear.of_linterm srk v)

  let translate_constraint var_to_ray_var v =
    BatEnum.fold (fun v (coeff, dim) ->
        if dim <> Linear.const_dim then
          Linear.QQVector.add_term
            coeff
            (SrkUtil.Int.Map.find dim var_to_ray_var)
            v
        else
          v
      )
      Linear.QQVector.zero
      (Linear.QQVector.enum v)

  let recession_extension var_to_ray_var p =
    let system = Polyhedron.enum_constraints p in
    BatEnum.iter (fun (ckind, v) ->
        let recession_ineq = match ckind with
          | `Pos -> `Nonneg
          | _ -> ckind in
        let ray_constraint = translate_constraint var_to_ray_var v in
        let subspace_point_constraint = Linear.QQVector.sub v ray_constraint in
        BatEnum.push system (recession_ineq, ray_constraint);
        BatEnum.push system (ckind, subspace_point_constraint))
      (Polyhedron.enum_constraints p);
    Polyhedron.of_constraints system

  let subspace_restriction srk var_to_ray_var l m =
    let constraints = BatEnum.empty () in
    BatList.iter
      (fun v ->
        let lhs =
          Linear.QQVector.sub v (translate_constraint var_to_ray_var v) in
        let rhs =
          Interpretation.evaluate_term m (Linear.of_linterm srk v) in
        let subspace_constraint =
          Linear.QQVector.add_term (QQ.negate rhs) Linear.const_dim lhs
        in
        BatEnum.push constraints (`Zero, subspace_constraint)
      )
      (IntLattice.basis l);
    Polyhedron.of_constraints constraints

  let non_constant_dimensions p =
    let dimensions =
      BatEnum.fold (fun dims (_kind, v) ->
          BatEnum.fold (fun dims (_, dim) ->
              SrkUtil.Int.Set.add dim dims)
            dims
            (Linear.QQVector.enum v))
        SrkUtil.Int.Set.empty
        (Polyhedron.enum_constraints p)
    in
    SrkUtil.Int.Set.remove Linear.const_dim dimensions

  let mixed_lattice_hull srk p l =
    let p_variables = non_constant_dimensions p in
    let var_to_ray_var =
      BatEnum.fold
        (fun ray_dims dim ->
          (SrkUtil.Int.Map.add
             dim
             (Syntax.int_of_symbol (Syntax.mk_symbol srk `TyReal))
             ray_dims))
        SrkUtil.Int.Map.empty
        (SrkUtil.Int.Set.enum p_variables)
    in
    let pre_abstraction = recession_extension var_to_ray_var p in
    let max_dim = Polyhedron.max_constrained_dim p in
    let solver = Smt.StdSolver.make srk in
    let lattice_constraints =
      List.map (fun v -> Syntax.mk_is_int srk (Linear.of_linterm srk v))
        (IntLattice.basis l) in
    let polyhedron_constraints =
      BatEnum.fold
        (fun l (ckind, v) -> to_inequality srk (ckind, v) :: l)
        []
        (Polyhedron.enum_constraints p)
    in
    let () = Smt.StdSolver.add solver
               (polyhedron_constraints @ lattice_constraints)
    in
    let rec go curr m =
      let abstraction =
        Polyhedron.meet pre_abstraction (subspace_restriction srk var_to_ray_var l m)
        |> Polyhedron.local_project
             (fun dim -> Interpretation.evaluate_term m
                           (Syntax.mk_const srk (Syntax.symbol_of_int dim)))
             (BatList.of_enum (SrkUtil.Int.Map.values var_to_ray_var))
        |> Polyhedron.dd_of max_dim
      in
      let next = DD.join curr abstraction in
      let atoms_of_abstraction =
        BatEnum.fold
          (fun l (ckind, v) -> to_inequality srk (ckind, v) :: l)
          []
          (DD.enum_constraints abstraction)
      in
      Smt.StdSolver.add solver
        [Syntax.mk_not srk (Syntax.mk_and srk atoms_of_abstraction)];
      match Smt.StdSolver.get_model solver with
      | `Sat m -> go next m
      | `Unsat -> curr
      | `Unknown -> failwith "LatticePolyhedron: Solver cannot decide"
    in
    match Smt.StdSolver.get_model solver with
    | `Sat m -> go (DD.of_constraints_closed max_dim (BatEnum.empty ())) m
    | `Unsat -> DD.of_constraints_closed max_dim (BatEnum.empty ())
    | `Unknown -> failwith "LatticePolyhedron: Solver cannot decide"

end

module CooperProjection : sig

  val local_project_cooper:
    (int -> QQ.t) -> eliminate: int list ->
    ?round_lower_bound: (P.constraint_kind -> V.t -> (int -> QQ.t) ->
                         V.t * (P.constraint_kind * V.t) list * V.t list) ->
    Polyhedron.t -> IntLattice.t ->
    Polyhedron.t * IntLattice.t

end = struct

  module V = Linear.QQVector
  module P = Polyhedron

  let lower_bound dim v =
    let (coeff, v') = V.pivot dim v in
    assert (QQ.lt QQ.zero coeff);
    V.scalar_mul (QQ.negate (QQ.inverse coeff)) v'

  let substitute_term t dim v =
    let (c, v') = V.pivot dim v in
    V.add v' (V.scalar_mul c t)

  let classify_constraints m dim constraints =
    BatEnum.fold
      (fun (glb, relevant, irrelevant, equality, has_upper_bound)
           (cnstr_kind, v) ->
        if QQ.equal (V.coeff dim v) QQ.zero then
          (glb, relevant, (cnstr_kind, v) :: irrelevant,
           equality, has_upper_bound)
        else if QQ.lt (V.coeff dim v) QQ.zero then
          begin match cnstr_kind with
          | `Zero ->
             (glb, (cnstr_kind, v) :: relevant, irrelevant,
              Some v, has_upper_bound)
          | `Nonneg | `Pos ->
             (glb, (cnstr_kind, v) :: relevant, irrelevant, equality, true)
          end
        else
          begin match cnstr_kind with
          | `Zero ->
             (glb, (cnstr_kind, v) :: relevant, irrelevant, Some v, has_upper_bound)
          | `Nonneg | `Pos ->
             let rounded_value =
               let value = Linear.evaluate_affine m (lower_bound dim v) in
               match cnstr_kind with
               | `Nonneg ->
                  QQ.ceiling value
               | `Pos ->
                  ZZ.add (QQ.floor value) ZZ.one
               | `Zero ->
                  assert false
             in
             begin match glb with
             | None ->
                (Some (rounded_value, cnstr_kind, v),
                 (cnstr_kind, v) :: relevant, irrelevant,
                 equality, has_upper_bound)
             | Some (curr_rounded_value, _, _) ->
                if ZZ.lt curr_rounded_value rounded_value
                then
                  (Some (rounded_value, cnstr_kind, v),
                   (cnstr_kind, v) :: relevant, irrelevant,
                   equality, has_upper_bound)
                else
                  (glb, (cnstr_kind, v) :: relevant, irrelevant, equality,
                   has_upper_bound)
             end
          end
      )
      (None, [], [], None, false)
      constraints

  let local_project_one m dim_to_elim ~round_lower_bound polyhedron lattice =
    let (glb, relevant, irrelevant, equality, has_upper_bound) =
      classify_constraints m dim_to_elim (P.enum_constraints polyhedron) in
    let substitute_and_adjoin_ineqs solution ineqs_cond =
      let cnstrs = BatList.enum irrelevant in
      List.iter (fun (kind, v) -> BatEnum.push cnstrs (kind, v))
          ineqs_cond;
        List.iter (fun (cnstr_kind, v) ->
            BatEnum.push cnstrs
              (cnstr_kind, substitute_term solution dim_to_elim v))
          relevant;
        P.of_constraints cnstrs
    in
    let substitute_and_adjoin_integral solution integral_cond =
      List.map (substitute_term solution dim_to_elim) (IntLattice.basis lattice)
      |> List.rev_append integral_cond
      |> IntLattice.hermitize
    in
    if Option.is_some equality then
      let v = Option.get equality in
      let (coeff, v') = V.pivot dim_to_elim v in
      let term = V.scalar_mul (QQ.negate (QQ.inverse coeff)) v' in
      let (rounded_term, inequalities, integrality) =
        round_lower_bound `Zero term m in
      let new_p = substitute_and_adjoin_ineqs rounded_term inequalities in
      let new_l = substitute_and_adjoin_integral rounded_term integrality in
      (new_p, new_l)
    else if not has_upper_bound || glb = None then
      ( P.of_constraints (BatList.enum irrelevant)
      , IntLattice.project (fun dim' -> dim' <> dim_to_elim) lattice)
    else
      let (rounded_value, cnstr_kind, glb_v) = Option.get glb in
      let modulus = BatList.fold_left
                      (fun m v ->
                        let coeff = Linear.QQVector.coeff dim_to_elim v in
                        if QQ.equal coeff QQ.zero then m
                        else QQ.lcm m (QQ.inverse coeff))
                      QQ.one
                      (IntLattice.basis lattice)
      in
      let (rounded_term, inequalities, integrality) =
        round_lower_bound cnstr_kind (lower_bound dim_to_elim glb_v) m in
      let delta = QQ.modulo (QQ.sub (m dim_to_elim) (QQ.of_zz rounded_value)) modulus in
      let solution = Linear.QQVector.add_term delta Linear.const_dim rounded_term in
      let new_p = substitute_and_adjoin_ineqs solution inequalities in
      let new_l = substitute_and_adjoin_integral solution integrality in
      (new_p, new_l)

  let local_project_cooper m ~eliminate
        ?(round_lower_bound=(fun _ lower_bound _ -> (lower_bound, [], [])))
        polyhedron lattice =
    BatList.fold_left
      (fun (p, l) dim_to_elim ->
        local_project_one m dim_to_elim ~round_lower_bound  p l
      )
      (polyhedron, lattice)
      eliminate

end

(*
module DeprecatedPureHull = struct

  let map_polyhedron map p =
    let q = BatEnum.empty () in
    BatEnum.iter (fun (kind, v) ->
        match T.apply map v with
        | None -> failwith "lattice is not full-dimensional"
        | Some image ->
           BatEnum.push q (kind, image)
      )
      (P.enum_constraints p);
    P.of_constraints q

  let pp_dim = fun fmt d -> Format.fprintf fmt "%d" d

  (* Compute the map [f] that sends [l] to a space where [f(l)] is the standard
   lattice. *)
  let make_map l =
    let basis = IntLattice.basis l in
    let map_one =
      let one = V.of_term QQ.one Linear.const_dim in
      T.may_add one one T.empty in
    let adjoin (f, b) fresh_dim v =
      let f' = T.may_add v (V.of_term QQ.one fresh_dim) f in
      let b' = T.may_add (V.of_term QQ.one fresh_dim) v b in
      (f', b')
    in
    let (forward, inverse) = BatList.fold_lefti adjoin (map_one, map_one) basis in
    (forward, inverse)
end
 *)

let mixed_lattice_hull = MixedHull.mixed_lattice_hull
let local_project_cooper = CooperProjection.local_project_cooper
