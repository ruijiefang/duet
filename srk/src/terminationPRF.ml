open Syntax

(* open BatPervasives *)
module Vec = Linear.QQVector
module TF = TransitionFormula
module CS = CoordinateSystem
module LIRR = LirrSolver
module P = Polynomial
module PC = PolynomialCone

include Log.Make (struct
  let name = "TerminationPRF"
end)

let pp_dim srk arr formatter i =
  try
    Format.fprintf formatter "%a" (Syntax.ArithTerm.pp srk) (BatArray.get arr i)
  with _ -> Format.fprintf formatter "1"

let zero_stable srk f pre_vars_arr post_vars_arr =
  let solver = Abstract.Solver.make srk ~theory:`LIRR f in
  let conseq_pre = Abstract.PolynomialCone.abstract solver pre_vars_arr in
  logf "computed conseq pre";
  logf "conseq pre: %a" (PC.pp (pp_dim srk pre_vars_arr)) conseq_pre;
  let rec work prev_cone prev_f =
    logf "finding zero guards for formula: %a" (Formula.pp srk) prev_f;
    let pre_zeros = PC.get_ideal prev_cone in
    let zero_guards = P.Rewrite.generators pre_zeros in
    let zero_guards_remain_zero =
      BatList.map
        (fun pre_poly ->
          (* let pre_term = P.QQXs.term_of srk (Array.get pre_vars_arr) pre_poly in *)
          let post_term =
            P.QQXs.term_of srk (Array.get post_vars_arr) pre_poly
          in
          mk_eq srk (mk_zero srk) post_term)
        zero_guards
    in
    let new_f = mk_and srk (prev_f :: zero_guards_remain_zero) in
    let new_solver = Abstract.Solver.make srk ~theory:`LIRR new_f in
    let new_cone = Abstract.PolynomialCone.abstract new_solver pre_vars_arr in
    if P.Rewrite.equal (PC.get_ideal prev_cone) (PC.get_ideal new_cone) then
      new_f
    else work new_cone new_f
    (* if PC.equal prev_cone new_cone then prev_f else work new_cone new_f *)
  in
  work conseq_pre f

let lin_conseq_over_diff_polys srk solver pre_vars_arr post_vars_arr
    positive_polys =
  let diffs_arr =
    Array.map
      (fun poly ->
        let pre_poly_term =
          P.QQXs.term_of srk (fun dim -> BatArray.get pre_vars_arr dim) poly
        in
        let post_poly_term =
          P.QQXs.term_of srk (fun dim -> BatArray.get post_vars_arr dim) poly
        in
        mk_sub srk pre_poly_term post_poly_term)
      positive_polys
  in
  logf "diffs array:";
  Array.iteri
    (fun i diff -> logf "dim: %d, term: %a" i (ArithTerm.pp srk) diff)
    diffs_arr;
  logf "lin solver made";
  let lin_conseq = Abstract.ConvexHull.abstract solver diffs_arr in
  logf "lin abstract complete";

  (* let positive_poly_terms =
       Array.map
         (fun poly ->
           P.QQXs.term_of srk (fun dim -> BatArray.get pre_vars_arr dim) poly)
         positive_polys
     in *)
  logf "lin conseq over positives: %a" (DD.pp (pp_dim srk diffs_arr)) lin_conseq;

  (lin_conseq, diffs_arr)

let has_prf srk tf =
  let tf = TF.map_formula (Syntax.eliminate_floor_mod_div srk) tf in
  let x_xp =
    Symbol.Set.fold
      (fun s xs -> (s, s) :: xs)
      (TF.symbolic_constants tf) (TF.symbols tf)
  in
  logf "Finding PRF for TF: %a" (Formula.pp srk) (TF.formula tf);
  (* let x_xp = TF.symbols tf in *)
  let pre_vars_arr =
    BatArray.of_list (BatList.map (fun (x, _) -> mk_const srk x) x_xp)
  in
  let post_vars_arr =
    BatArray.of_list (BatList.map (fun (_, xp) -> mk_const srk xp) x_xp)
  in
  let tf_formula = TF.formula tf in
  let zero_stable_formula =
    zero_stable srk tf_formula pre_vars_arr post_vars_arr
  in
  logf "zero-stable formula: %a" (Formula.pp srk) zero_stable_formula;
  let solver = Abstract.Solver.make srk ~theory:`LIRR zero_stable_formula in
  let pre_conseq_cone = Abstract.PolynomialCone.abstract solver pre_vars_arr in
  logf "conseq pre: %a" (PC.pp (pp_dim srk pre_vars_arr)) pre_conseq_cone;
  let pos_pre_polys = PC.get_cone_generators pre_conseq_cone in
  let dim = List.length pos_pre_polys in
  let phedral_new_terms, diffs_arr =
    lin_conseq_over_diff_polys srk solver pre_vars_arr post_vars_arr
      (Array.of_list pos_pre_polys)
  in
  (* logf "lin consequence complete"; *)
  let constraints_enum = DD.enum_constraints_closed phedral_new_terms in
  let new_generators =
    BatEnum.fold
      (fun gens cons ->
        match cons with
        | `Nonneg, v ->
            (* logf "nonneg constraint as generator: %a" Vec.pp v; *)
            let b, vv = Vec.pivot Linear.const_dim v in
            let vv = Vec.add_term b dim vv in
            logf "nonneg constraint as generator: %a" Vec.pp vv;

            (`Ray, vv) :: gens
        | `Zero, v ->
            let b, vv = Vec.pivot Linear.const_dim v in
            let vp = Vec.add_term b dim vv in
            let vm = Vec.negate vp in
            logf "zero constraint as generator: %a" Vec.pp vp;
            logf "zero constraint as generator: %a" Vec.pp vm;

            (`Ray, vp) :: (`Ray, vm) :: gens)
      [ (`Vertex, Vec.zero) ]
      constraints_enum
  in
  let gen_enum = BatList.enum new_generators in
  let new_polyhedron = DD.of_generators (dim + 1) gen_enum in
  logf "polyhedron of nonneg diff terms constructed";
  let const_dim_minus_1_cons =
    Vec.add_term QQ.one Linear.const_dim (Vec.add_term QQ.one dim Vec.zero)
  in
  let const_dim_cons = (`Zero, const_dim_minus_1_cons) in
  let other_dims_positive =
    let open BatEnum in
    0 -- (dim - 1)
    |> BatList.of_enum
    |> BatList.map (fun d ->
           let v = Vec.add_term QQ.one d Vec.zero in
           (`Nonneg, v))
  in
  logf "polyhedron of -1 const terms constructed";

  let result =
    DD.meet_constraints new_polyhedron (const_dim_cons :: other_dims_positive)
  in

  let diffs_arr = Array.append diffs_arr (Array.make 1 (mk_one srk)) in
  (* Array.set diffs_arr dim (mk_one srk); *)
  logf "after intersection: %a" (DD.pp (pp_dim srk diffs_arr)) result;
  let ans = not (BatEnum.is_empty (DD.enum_generators result)) in
  logf "has prf: %b" ans;
  ans

let has_plrf srk tf =
  let tf = TF.map_formula (Syntax.eliminate_floor_mod_div srk) tf in
  let x_xp =
    Symbol.Set.fold
      (fun s xs -> (s, s) :: xs)
      (TF.symbolic_constants tf) (TF.symbols tf)
  in
  logf "Begin PLRF for TF: %a" (Formula.pp srk) (TF.formula tf);
  (* let x_xp = TF.symbols tf in *)
  let pre_vars_arr =
    BatArray.of_list (BatList.map (fun (x, _) -> mk_const srk x) x_xp)
  in
  let post_vars_arr =
    BatArray.of_list (BatList.map (fun (_, xp) -> mk_const srk xp) x_xp)
  in
  let tf_formula = TF.formula tf in

  let find_qrfs f =
    logf "current TF: %a" (Formula.pp srk) f;
    let solver = Abstract.Solver.make srk ~theory:`LIRR f in
    let pre_conseq_cone =
      Abstract.PolynomialCone.abstract solver pre_vars_arr
    in
    logf "conseq pre: %a" (PC.pp (pp_dim srk pre_vars_arr)) pre_conseq_cone;
    (* let pos_polys = PC.get_cone_generators pre_conseq_cone in *)
    let pos_pre_polys = PC.get_cone_generators pre_conseq_cone in
    let dim = List.length pos_pre_polys in
    let phedral_new_terms, diffs_arr =
      lin_conseq_over_diff_polys srk solver pre_vars_arr post_vars_arr
        (Array.of_list pos_pre_polys)
    in
    let phedron =
      Polyhedron.of_constraints (DD.enum_constraints phedral_new_terms)
    in
    logf "phedron: %a" (Polyhedron.pp (pp_dim srk diffs_arr)) phedron;
    let dc = Polyhedron.dd_of dim (Polyhedron.dual_cone dim phedron) in
    let all_dims_positive =
      let open BatEnum in
      0 -- (dim - 1)
      |> BatList.of_enum
      |> BatList.map (fun d ->
             let v = Vec.add_term QQ.one d Vec.zero in
             (`Nonneg, v))
    in
    let dc = DD.meet_constraints dc all_dims_positive in
    logf "poly before qrfs: %a" (DD.pp (pp_dim srk diffs_arr)) dc;

    let qrfs =
      DD.enum_generators dc
      |> BatEnum.filter_map (fun (typ, vec) ->
             if typ = `Ray then
               let pre_exp =
                 Linear.term_of_vec srk
                   (fun d ->
                     let poly = BatList.nth pos_pre_polys d in
                     P.QQXs.term_of srk (Array.get pre_vars_arr) poly)
                   vec
               in
               let post_exp =
                 Linear.term_of_vec srk
                   (fun d ->
                     let poly = BatList.nth pos_pre_polys d in
                     P.QQXs.term_of srk (Array.get post_vars_arr) poly)
                   vec
               in
               Some (mk_eq srk pre_exp post_exp)
             else None)
      |> BatList.of_enum
    in
    qrfs
  in

  let rec termination_by_qrfs f =
    let zero_stable_formula = zero_stable srk f pre_vars_arr post_vars_arr in
    logf "zero-stable formula: %a" (Formula.pp srk) zero_stable_formula;
    let solver = Abstract.Solver.make srk ~theory:`LIRR zero_stable_formula in
    match Abstract.Solver.get_model solver with
    | `Unsat ->
        logf "has PLRF!!";
        true
    | _ -> (
        let qrfs = find_qrfs zero_stable_formula in
        List.iter (logf "qrf unchange: %a" (Formula.pp srk)) qrfs;
        let f_qrfs_dont_change = mk_and srk qrfs in
        let improvement = mk_and srk [ f; mk_not srk f_qrfs_dont_change ] in
        let ss = Abstract.Solver.make srk ~theory:`LIRR improvement in
        logf "improvement formula: %a" (Formula.pp srk) improvement;
        match Abstract.Solver.get_model ss with
        | `Unsat | `Unknown ->
            logf "does not have PLRF :( ";
            false
        | `Sat _ -> termination_by_qrfs (mk_and srk [f; f_qrfs_dont_change]))
  in

  termination_by_qrfs tf_formula
