module V = Linear.QQVector
module P = Polyhedron
module L = IntLattice
module T = Linear.MakeLinearMap(QQ)(Int)(V)(V)

module FV = FormulaVector

module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

include Log.Make(struct let name = "srk.latticePolyhedron" end)

let () = my_verbosity_level := `trace

let debug ?(level=`debug) f default =
    if Log.level_leq !my_verbosity_level level then
      f
    else
      (fun _ -> default)

let check_point_in_p srk ?(level=`debug) binding m p =
  let dimensions = FV.collect_dimensions (p, IntLattice.bottom) in
  if (debug ~level (Polyhedron.mem m) true) p then
    ()
  else
    let alpha = FV.formula_of_polyhedron srk binding p in
    let mphi = FV.formula_of_model srk binding dimensions m in
    logf ~level "model @[%a@] does not satisfy @[%a@]@;"
      (Syntax.Formula.pp srk) mphi
      (Syntax.Formula.pp srk) alpha

module Hull: sig

  val local_mixed_lattice_hull:
    (int -> QQ.t) -> P.t * L.t -> P.t

  (** Ambient dimension has to be at least the maximum constrained dimension
      (computed via dim_of_symbol in binding) + 1.
   *)
  val mixed_lattice_hull: 'a Syntax.context ->
    'a FV.binding -> ambient_dim: int ->
    (P.t * L.t) list -> DD.closed DD.t

  val partition_vertices_by_integrality:
    DD.closed DD.t -> L.t -> (V.t list * V.t list)

  (** `PureGomoryChvatal is guaranteed to work only when all variables are
      implied to be integer-valued, but this is not checked.
      Ambient dimension should be at least as large as the maximum dimension
      occurring in the formula (computed via [dim_of_symbol]) + 1.
   *)
  val abstract: 'a Syntax.context -> 'a FV.binding ->
                [`Mixed | `PureGomoryChvatal] -> ambient_dim:int ->
                'a Syntax.formula -> DD.closed DD.t

end = struct

  let partition_vertices_by_integrality dd l =
    BatEnum.fold (fun (integral, non_integral) (gkind, v) ->
        match gkind with
        | `Vertex ->
           if IntLattice.member v l then (v :: integral, non_integral)
           else (integral, v :: non_integral)
        | `Ray -> (integral, non_integral)
        | `Line -> (integral, non_integral)
      ) ([], []) (DD.enum_generators dd)

  let check_hull ?(level=`debug) ?srk_binding p l =
    let ambient = P.max_constrained_dim p + 1 in
    let dd = P.dd_of ambient p in
    let (_, non_integral) =
      debug ~level (partition_vertices_by_integrality dd) ([], []) l in
    match non_integral with
    | [] -> ()
    | _ ->
       begin
         match srk_binding with
         | Some (srk, binding) ->
            logf ~level:`debug "check_hull: lattice is: @[%a@]@;"
              (Syntax.Formula.pp srk)
              (FV.formula_of_lattice srk binding l);
            List.iter
              (fun v ->
                logf ~level:`debug
                  "Vertex @[%a@] is not in the lattice"
                  (Syntax.Formula.pp srk) (FV.formula_of_point srk binding v)
              )
              non_integral
         | None ->
            logf ~level:`debug "check_hull: lattice is: @[%a@]"
              (IntLattice.pp Format.pp_print_int) l;
            List.iter
              (fun v ->
                logf ~level:`debug
                  "Vertex @[%a@] is not in the lattice"
                  (Linear.QQVector.pp_term Format.pp_print_int) v
              )
              non_integral
       end

  let remap_vector f v =
    BatEnum.fold (fun v (coeff, dim) ->
        if dim <> Linear.const_dim then
          V.add_term coeff (f dim) v
        else v
      )
      V.zero
      (V.enum v)

  let recession_extension var_to_ray_var p =
    (* ax <= b, a'x < b' -->
       ax <= b, a'x < b', ar <= 0, a(x-r) <= b, a'(x - r) < b'
     *)
    let system = P.enum_constraints p in
    BatEnum.iter (fun (ckind, v) ->
        let recession_ineq = match ckind with
          | `Pos -> `Nonneg
          | _ -> ckind in
        let ray_constraint = remap_vector var_to_ray_var v in
        let subspace_point_constraint = V.sub v ray_constraint in
        BatEnum.push system (recession_ineq, ray_constraint);
        BatEnum.push system (ckind, subspace_point_constraint))
      (P.enum_constraints p);
    P.of_constraints system

  let subspace_restriction var_to_ray_var l m =
    (* Int(cx + d) --> c (x - r) = c x0 *)
    let constraints = BatEnum.empty () in
    logf ~level:`trace "subspace_restriction: lattice constraints: @[%a@]@;"
      (Format.pp_print_list (V.pp_term Format.pp_print_int))
      (L.basis l);
    BatList.iter
      (fun v ->
        let (_, x) = V.pivot Linear.const_dim v in
        let lhs =
          V.sub x (remap_vector var_to_ray_var x)
        in
        let rhs = V.fold (fun dim coeff sum ->
                      if dim <> Linear.const_dim then
                        QQ.add (QQ.mul coeff (m dim)) sum
                      else sum)
                    x
                    QQ.zero in
        let subspace_constraint =
          V.add_term (QQ.negate rhs) Linear.const_dim lhs
        in
        BatEnum.push constraints (`Zero, subspace_constraint)
      )
      (L.basis l);
    P.of_constraints constraints

  let ray_dim_of_dim start x = start + x
  (* let is_ray_dim start x = (x - start >= 0) *)

  let local_mixed_lattice_hull m (p, l) =
    let start = Int.max (P.max_constrained_dim p)
                  (L.max_dim l) + 1 in
    let pre_abstraction = recession_extension (ray_dim_of_dim start) p in
    let subspace = subspace_restriction (ray_dim_of_dim start) l m in
    let abstraction = P.meet pre_abstraction subspace
    in
    logf ~level:`trace "local_mixed_lattice_hull: input: @[%a@]@; start of recession dims: %d"
      (P.pp Format.pp_print_int) p start;
    logf ~level:`trace "local_mixed_lattice_hull: extension: @[%a@]@;"
      (P.pp Format.pp_print_int) pre_abstraction;
    logf ~level:`trace "local_mixed_lattice_hull: subspace: @[%a@]@;"
      (P.pp Format.pp_print_int) subspace;
    logf ~level:`trace "local_mixed_lattice_hull, before projection: @[%a@]@;"
      (P.pp Format.pp_print_int) abstraction;
    let projected =
      (* Local projection diverges if we do local projection here! *)
      (* P.local_project
        (fun dim -> if is_ray_dim start dim then QQ.zero else m dim)
        (BatList.of_enum (BatEnum.(--^) start (2 * start)))
        abstraction *)
      P.project (BatList.of_enum (BatEnum.(--^) start (2 * start)))
        abstraction
    in
    logf ~level:`trace "after projection: @[%a@]@;"
      (P.pp Format.pp_print_int) projected;
    logf ~level:`trace "max constrained dimension: %d"
      (P.max_constrained_dim projected);
    check_hull ~level:`debug p l;
    projected

  let mixed_lattice_hull srk binding ~ambient_dim conjuncts =
    let make_conjunct (p, l) =
      let p_phi = FV.formula_of_polyhedron srk binding p in
      let l_phi = FV.formula_of_lattice srk binding l
      in
      Syntax.mk_and srk [p_phi; l_phi]
    in
    let phi = Syntax.mk_and srk (List.map make_conjunct conjuncts)
    in
    let of_model =
      let abstract m (p, l) =
        let hull = local_mixed_lattice_hull m (p, l) in
        logf ~level:`debug "mixed_lattice_hull: Mixed hull is: @[%a@], ambient dimension %d@;"
          (P.pp Format.pp_print_int) hull ambient_dim;
        P.dd_of ambient_dim hull
      in
      FV.abstract_implicant srk binding (`ImplicantOnly abstract) phi
    in
    let domain: ('a, DD.closed DD.t) Abstract.domain =
      {
        join = DD.join
      ; of_model
      ; formula_of = (FV.formula_of_dd srk binding)
      ; top = P.dd_of ambient_dim P.top
      ; bottom = P.dd_of ambient_dim P.bottom
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    logf ~level:`debug "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    let hull = Abstract.Solver.abstract solver domain in
    debug ~level:`trace
      (fun hull_phi ->
        match Smt.entails srk phi hull_phi with
        | `Yes ->
           logf "mixed_lattice_hull: formula @[%a@] entails hull formula @[%a@]@;"
             (Syntax.Formula.pp srk) phi (Syntax.Formula.pp srk) hull_phi
        | `No ->
           logf "mixed_lattice_hull: formula @[%a@] does not entail hull formula @[%a@]@;"
             (Syntax.Formula.pp srk) phi
             (Syntax.Formula.pp srk) hull_phi
        | `Unknown -> logf "mixed_lattice_hull: unknown"
      )
      () (FV.formula_of_dd srk binding hull);
    hull

  let abstract srk binding how ~ambient_dim phi =
    logf ~level:`debug "ambient dimension is %d@;" ambient_dim;
    let alg =
      match how with
      | `Mixed -> local_mixed_lattice_hull
      | `PureGomoryChvatal ->
         (fun _m (p, _l) -> P.integer_hull `GomoryChvatal p)
    in
    let abstract m (p, l) =
      let hull = alg m (p, l) in
      logf "abstract: Mixed hull is: @[%a@], ambient dimension %d@;"
        (P.pp Format.pp_print_int) hull ambient_dim;
      P.dd_of ambient_dim hull
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join = DD.join
      ; of_model =
          FV.abstract_implicant srk binding (`ImplicantOnly abstract) phi
      ; formula_of = FV.formula_of_dd srk binding
      ; top = P.dd_of ambient_dim P.top
      ; bottom = P.dd_of ambient_dim P.bottom
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    ignore (Abstract.Solver.get_model solver);
    let hull = Abstract.Solver.abstract solver domain in
    debug ~level:`trace
      (fun hull_phi ->
        match Smt.entails srk phi hull_phi with
        | `Yes ->
           logf "mixed_lattice_hull: formula @[%a@] entails hull formula @[%a@]@;"
             (Syntax.Formula.pp srk) phi (Syntax.Formula.pp srk) hull_phi
        | `No ->
           logf "mixed_lattice_hull: formula @[%a@] does not entail hull formula @[%a@]@;"
             (Syntax.Formula.pp srk) phi
             (Syntax.Formula.pp srk) hull_phi
        | `Unknown -> logf "mixed_lattice_hull: unknown"
      )
      () (FV.formula_of_dd srk binding hull);
    hull

end

type ceiling =
  {
    round_value: [`Leq | `Lt] -> QQ.t -> QQ.t
  ; round_term:
      [`Leq | `Lt] -> V.t -> (int -> QQ.t) ->
      V.t * (P.constraint_kind * V.t) list * V.t list
  }

exception PositiveIneqOverRealVar of V.t * int

module CooperProjection : sig

  (** Given [P /\ L], a point [m] in [P /\ L], a sound [ceiling],
      and [elim] a dimension such that [P /\ L |= Int(elim)],
      compute [P'] and [L'] (and terms) such that
      (i)   [P'] and [L'] are in dimensions excluding [elim].
      (ii)  [m |= exists [elim]. P' /\ L'].
      (iii) [ts] are terms (corresponding order-wise to [elim]) such that
            [formula_of(P') = formula_of(P)[ts/elim]]
            and [formula_of(L') = formula_of(P)[ts/elim]].

      The procedure may not have finite image if some variable in the formula
      (not just one that is to be eliminated) can take on real
      values. A ceiling can be provided to make local projection image-finite.

      - [`NonstrictIneqsOnly] corresponds to a ceiling (the identity) that is
        sound when only non-strict inequalities occur, i.e. (i) --- (iii) hold,
        but may not be image-finite unless [P /\ L |= Int(x)] for all variables [x].
      - When strict inequalities are present and all variables are integer-valued,
        [`RoundStrictWhenVariablesIntegral] can be used to heuristically convert
        the strict inequality into a non-strict one.
        For [local-hull-and-project], if Cooper projection is used, we may
        possibly use LW's epsilon virtual substitution to handle strict inequalities.

      Notes:
      - [P /\ L |= Int(elim)] is more general than [L |= Int(elim)]; we don't
        require that [elim] is in the lattice of integer constraints.

      - The procedure is unsound if this condition doesn't hold, i.e., when [elim]
        can possibly take on real values. This may be an implementation issue:
        we may switch to Loos-Weispfenning term selection when [elim] is not in
        [L], but when a ceiling is provided, the rounded lower bound cannot
        be used as the Loos-Weispfenning term; we have to use the original
        lower bound instead.

      - A heuristic may be to use LW if [elim] is not in [L]. But this is not
        sound, e.g., eliminating x from Int(2x) /\ 1/3 <= x <= 1 using LW is
        unsound.
   *)
  val local_project:
    (int -> QQ.t) -> eliminate: int Array.t ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    P.t * L.t ->
    P.t * L.t * [`MinusInfinity | `PlusInfinity | `Term of V.t] Array.t

  val project:
    'a Syntax.context -> 'a FV.binding -> eliminate: int list ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t * L.t

  (** Identity ceiling. When all variables are guaranteed to be integer-valued
      (e.g., of integer type within a syntactic context), and all inequalities
      are non-strict, no rounding is needed for local projection to be image-finite.

      The ceiling is UNSOUND if strict inequalities are present (because identity
      rounding doesn't distinguish between strict and non-strict inequalities.)
   *)
  val all_variables_are_integral_and_no_strict_ineqs: ceiling

end = struct

  let lower_bound dim v =
    let (coeff, v') = V.pivot dim v in
    assert (QQ.lt QQ.zero coeff);
    V.scalar_mul (QQ.negate (QQ.inverse coeff)) v'

  let substitute_term t dim v =
    let (c, v') = V.pivot dim v in
    V.add v' (V.scalar_mul c t)

  let classify_constraints round m dim constraints =
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
             (*
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
              *)
             let rounded_value =
               let value = Linear.evaluate_affine m (lower_bound dim v) in
               let ckind = match cnstr_kind with
                 | `Nonneg -> `Leq
                 | `Pos -> `Lt
                 | `Zero -> assert false
               in
               round ckind value
             in
             begin match glb with
             | None ->
                (Some (rounded_value, cnstr_kind, v),
                 (cnstr_kind, v) :: relevant, irrelevant,
                 equality, has_upper_bound)
             | Some (curr_rounded_value, _, _) ->
                if QQ.lt curr_rounded_value rounded_value
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
      classify_constraints round_lower_bound.round_value
        m dim_to_elim (P.enum_constraints polyhedron) in
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
      List.map (substitute_term solution dim_to_elim) (L.basis lattice)
      |> List.rev_append integral_cond
      |> L.hermitize
    in
    if Option.is_some equality then
      let v = Option.get equality in
      let (coeff, v') = V.pivot dim_to_elim v in
      let solution = V.scalar_mul (QQ.negate (QQ.inverse coeff)) v' in
      logf ~level:`debug
        "local_project_one: term selected for %d using equality: @[%a@]@;"
        dim_to_elim
        (V.pp_term Format.pp_print_int) solution;
      let new_p = substitute_and_adjoin_ineqs solution [] in
      let new_l = substitute_and_adjoin_integral solution [] in
      (new_p, new_l, `Term solution)
    else if (not has_upper_bound) || glb = None then
      begin
        logf ~level:`debug "local_project_one: No upper/lower bounds for %d@;"
          dim_to_elim;
        ( P.of_constraints (BatList.enum irrelevant)
        , L.project (fun dim' -> dim' <> dim_to_elim) lattice
        , if not has_upper_bound then `PlusInfinity else `MinusInfinity
        )
      end
    else
      let (rounded_value, cnstr_kind, glb_v) = Option.get glb in
      let modulus = BatList.fold_left
                      (fun m v ->
                        let coeff = V.coeff dim_to_elim v in
                        if QQ.equal coeff QQ.zero then m
                        else QQ.lcm m (QQ.inverse coeff))
                      QQ.one (* [P /\ L |= Int(x)] is assumed *)
                      (L.basis lattice)
      in
      let (rounded_term, inequalities, integrality) =
        round_lower_bound.round_term
          (match cnstr_kind with
           | `Nonneg -> `Leq
           | `Pos -> `Lt
           | `Zero -> assert false
          )
          (lower_bound dim_to_elim glb_v)
          m in
      let delta =
        QQ.modulo (QQ.sub (m dim_to_elim) rounded_value) modulus in
      let solution = V.add_term delta Linear.const_dim rounded_term in
      let new_p = substitute_and_adjoin_ineqs solution inequalities in
      let new_l = substitute_and_adjoin_integral solution integrality in
      logf ~level:`debug
        "local_project_one (1): Eliminating %d from polyhedron @[%a@] and lattice: @[%a@]@;"
        dim_to_elim
        (P.pp Format.pp_print_int) polyhedron
        (L.pp Format.pp_print_int) lattice;
      logf ~level:`debug
        "local_project_one (2): \
         m(var to elim) = @[%a@], \
         glb term before rounding: @[%a@], \
         rounded_value: @[%a@], \
         modulus: @[%a@], \
         delta: @[%a@], \
         rounded_term: @[%a@]@;"
        QQ.pp (m dim_to_elim)
        (V.pp_term Format.pp_print_int) (lower_bound dim_to_elim glb_v)
        QQ.pp rounded_value
        QQ.pp modulus
        QQ.pp delta
        (V.pp_term Format.pp_print_int) rounded_term;
      logf ~level:`debug
        "local_project_one (3): new polyhedron: @[%a@], new lattice: @[%a@], term selected: @[%a@]@;"
        (P.pp Format.pp_print_int) new_p
        (L.pp Format.pp_print_int) new_l
        (V.pp_term Format.pp_print_int) solution;
      (new_p, new_l, `Term solution)

  let all_variables_are_integral_and_no_strict_ineqs =
    {
      round_value = (fun _ x -> x)
    ; round_term =
        (fun _ lower_bound _m -> (lower_bound, [], []))
    }

  let clear_strict_asssuming_integral (ckind, v) =
    match ckind with
    | `Pos ->
       let v' = V.sub (V.scalar_mul (QQ.of_zz (V.common_denominator v)) v)
                  (V.of_term QQ.one Linear.const_dim) in
       logf ~level:`trace "Normalized strict inequality @[%a > 0@]@;"
         (V.pp_term Format.pp_print_int) v;
       (`Nonneg, v')
    | _ -> (ckind, v)

  let normalize_strict_ineqs p l =
    let cnstrs = BatEnum.empty () in
    BatEnum.iter
      (fun (ckind, v) ->
        match ckind with
        | `Pos ->
           let dimensions =
             FV.collect_dimensions_from_constraints snd
               (BatList.enum [(ckind, v)]) in
           let real_dim =
             try
               Some
                 (BatEnum.find
                    (fun dim -> not (L.member (V.of_term QQ.one dim) l))
                    (IntSet.enum dimensions))
             with Not_found ->
               None
           in
           begin match real_dim with
           | None ->
              BatEnum.push cnstrs (clear_strict_asssuming_integral (ckind, v))
           | Some _dim ->
              (*
              begin
                logf ~level:`debug "normalize_strict_ineqs: unsound to normalize > into >=";
                raise (PositiveIneqOverRealVar (v, dim))
              end
               *)
              BatEnum.push cnstrs (clear_strict_asssuming_integral (ckind, v))
           end
        | _ -> BatEnum.push cnstrs (ckind, v)
      )
      (P.enum_constraints p);
    P.of_constraints cnstrs

  let local_project m ~eliminate round_lower_bound (p, l) =
    logf "local_project_cooper: eliminating @[%a@] from @[%a@]@; and @[%a@]@;@;"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space Format.pp_print_int)
      (Array.to_list eliminate)
      (P.pp Format.pp_print_int) p
      (L.pp Format.pp_print_int) l;
    let (rounded_p, round_lower_bound) =
      match round_lower_bound with
      | `NonstrictIneqsOnly -> (p, all_variables_are_integral_and_no_strict_ineqs)
      | `RoundLowerBound round_lower_bound ->
         (p, round_lower_bound)
      | `RoundStrictWhenVariablesIntegral ->
         ( normalize_strict_ineqs p l
         , all_variables_are_integral_and_no_strict_ineqs)
    in
    let (p, l, ts) =
      Array.fold_left
        (fun (p, l, ts) dim_to_elim ->
          let (p', l', t') = local_project_one m dim_to_elim ~round_lower_bound p l in
          logf ~level:`debug
            "local_project_cooper: eliminated %d to get result: @[%a@]@;"
            dim_to_elim
            (P.pp Format.pp_print_int) p';
          (p', l', t' :: ts)
        )
        (rounded_p, l, [])
        eliminate
    in
    (p, l, Array.of_list (List.rev ts))

  let default_lattice = L.hermitize [Linear.const_linterm QQ.one]

  let top ambient_dim =
    (P.dd_of ambient_dim P.top, default_lattice)

  let bottom ambient_dim =
    (P.dd_of ambient_dim P.bottom, default_lattice)

  let join (p1, l1) (p2, l2) =
    (DD.join p1 p2, L.intersect l1 l2)

  let formula_of srk binding (dd, l) =
    let p_phi = FV.formula_of_dd srk binding dd in
    let l_phi = FV.formula_of_lattice srk binding l in
    let fml = Syntax.mk_and srk [p_phi; l_phi] in
    logf ~level:`debug "project_cooper: blocking @[%a@]@;" (Syntax.Formula.pp srk) fml;
    fml

  let project srk binding ~eliminate round_lower_bound conjuncts =
    let make_conjunct (p, l) =
      let p_phi = FV.formula_of_polyhedron srk binding p in
      let l_phi = FV.formula_of_lattice srk binding l
      in
      Syntax.mk_and srk [p_phi; l_phi]
    in
    let phi = Syntax.mk_or srk (List.map make_conjunct conjuncts) in
    let ambient_dim = FV.ambient_dim conjuncts ~except:eliminate in
    let eliminate = Array.of_list eliminate in
    let abstract m (p, l) =
      let (p', l', _) = local_project m ~eliminate round_lower_bound (p, l) in
      (P.dd_of ambient_dim p', l')
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join
      ; of_model =
          FV.abstract_implicant srk binding (`ImplicantOnly abstract) phi
      ; formula_of = formula_of srk binding
      ; top = top ambient_dim
      ; bottom = bottom ambient_dim
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

end

module ProjectHull : sig
  (** These procedures compute the projection of the lattice hull by
      interleaving local procedures for hulling and projection.
   *)

  val project_cooper_and_hull: 'a Syntax.context ->
    'a FV.binding -> eliminate: int list ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t

  val hull_and_project_cooper: 'a Syntax.context ->
    'a FV.binding -> eliminate: int list ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t

  val hull_and_project_real: 'a Syntax.context ->
    'a FV.binding ->
    eliminate: int list -> (P.t * L.t) list -> DD.closed DD.t

  (** When projecting onto terms using variable elimination and Cooper's method,
      one has to be careful about what variables get eliminated.

      - [`OnePhaseElim]: Abstract by first defining terms, i.e., by adding a new
        dimension and a term equality for each term, and then eliminating the
        original variables. When an original dimension corresponds to a variable
        that may take on real values, this procedure is UNSOUND (not just
        diverge), because Cooper projection is sound only when the variable to
        be eliminated takes on integer values.

      - [`TwoPhaseElim]: First eliminate redundant variables to project onto those
        occurring in terms, and then project onto the terms themselves by real
        QE. This limits the soundness problem in [`OnePhaseElim] to the case
        where variables not occurring in [terms] are real-valued,
        also because Cooper projection is limited to integer-valued variables.

      In both cases, [`NoRounding] is unsound when strict inequalities are
      present (even if all variables are integer-valued).
      When all variables are guaranteed to be integer-valued, use
      [`RoundStrictWhenVariablesIntegral] instead.

      In summary, the preconditions are:
      - For [`OnePhaseElim], all variables have to be integer-valued.
      - For [`TwoPhaseElim], all variables not occurring in terms have to be
        integer-valued.
      - All variables that are integer-valued have to be asserted as integral
        via the lattice. (Mixed hull computation requires it explicitly, and
        Cooper projection requires care if they are implicit.)
   *)

  val abstract_by_local_hull_and_project_cooper:
    'a Syntax.context ->
    [`OnePhaseElim | `TwoPhaseElim] ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    'a Syntax.formula -> ('a Syntax.arith_term) array -> DD.closed DD.t

  val abstract_by_local_project_cooper_and_hull:
    'a Syntax.context ->
    [`OnePhaseElim | `TwoPhaseElim] ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    'a Syntax.formula -> ('a Syntax.arith_term) array -> DD.closed DD.t

  (** Real elimination after hulling is always sound. *)
  val abstract_by_local_hull_and_project_real:
    'a Syntax.context ->
    [`OnePhaseElim | `TwoPhaseElim] ->
    'a Syntax.formula -> ('a Syntax.arith_term) array -> DD.closed DD.t

end = struct

  (**
      F := (Ax + b >= 0 /\ Int(Cx + d) /\ Int(y))
      local_project_cooper(F) |= exists y. F.
      The procedure may diverge when there are real-valued variables in the
      formula.

      If F |= ez + f >= 0, (exists y. F) |= ez + f >= 0, so
      local_project_cooper(F) |= ez + f >= 0.
      So local_hull(local_project_cooper(F)) |= ez + f >= 0.
   *)
  let local_project_cooper_and_hull m ~eliminate round_lower_bound (p, l) =
    let eliminate = Array.of_list eliminate in
    let (projected_p, projected_l, _terms) =
      CooperProjection.local_project m ~eliminate round_lower_bound
        (p, l) in
    Hull.local_mixed_lattice_hull m (projected_p, projected_l)

  (**
      F := (Ax + b >= 0 /\ Int(Cx + d) /\ Int(y)) |= hull(F).
      For all ex + f >= 0, if F |= ex + f >= 0, mixed_hull(F) |= ex + f >= 0.

      local_project_cooper(local_hull(F), Int(Cx + d), Int(y))
      |= exists y. local_hull(F) /\ Int(Cx + d) /\ Int(y)
      |= exists y. hull(F) /\ Int(Cx + d) /\ Int(y)

      F |= ez + f >= 0 implies mixed_hull(F) |= ez + f >= 0.
      Since RHS is free of y,
      (exists y. mixed_hull(F)) |= ez + f >= 0,
      so
      (exists y. mixed_hull(F) /\ Int(Cx + d) /\ Int(y)) |= ez + f >= 0,
      so
      (exists y. local_hull(F) /\ Int(Cx + d) /\ Int(y)) |= ez + f >= 0,
      so
      local_project_cooper(local_hull(F), Int(Cx + d), Int(y)) |= ez + f >= 0.
   *)
  let local_hull_and_project_cooper m ~eliminate round_lower_bound (p, l) =
    let hulled = Hull.local_mixed_lattice_hull m (p, l) in
    let eliminate = Array.of_list eliminate in
    let (projected, _, _) =
      CooperProjection.local_project m ~eliminate round_lower_bound (hulled, l)
    in
    projected

  (* Same logic as above *)
  let local_hull_and_project_real m ~eliminate (p, l) =
    let hulled = Hull.local_mixed_lattice_hull m (p, l) in
    let projected = Polyhedron.local_project m eliminate hulled in
    projected

  let formula_of srk binding dd =
    let p_phi = FV.formula_of_polyhedron srk binding (P.of_dd dd) in
    logf ~level:`debug "ProjectHull: blocking @[%a@]@;"
      (Syntax.Formula.pp srk) p_phi;
    p_phi

  let top ambient_dim = P.dd_of ambient_dim P.top
  let bottom ambient_dim = P.dd_of ambient_dim P.bottom

  let saturate srk binding ambient_dim op conjuncts =
    let make_conjunct (p, l) =
      let p_phi = FV.formula_of_polyhedron srk binding p in
      let l_phi = FV.formula_of_lattice srk binding l
      in
      Syntax.mk_and srk [p_phi; l_phi]
    in
    let phi = Syntax.mk_or srk
                (List.map make_conjunct conjuncts)
    in
    let abstract m (p, l) = op m (p, l) |> P.dd_of ambient_dim in
    let domain: ('a, 'b) Abstract.domain =
      {
        join = DD.join
      ; of_model = FV.abstract_implicant srk binding
                     (`ImplicantOnly abstract) phi
      ; formula_of = formula_of srk binding
      ; top = top ambient_dim
      ; bottom = bottom ambient_dim
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

  let project_cooper_and_hull srk binding ~eliminate round_lower_bound conjuncts =
    let ambient_dim = FV.ambient_dim conjuncts ~except:eliminate in
    let op m (p, l) = local_project_cooper_and_hull m ~eliminate round_lower_bound (p, l) in
    saturate srk binding ambient_dim op conjuncts

  let hull_and_project_cooper srk binding ~eliminate round_lower_bound conjuncts =
    let ambient_dim = FV.ambient_dim conjuncts ~except:eliminate in
    let op m (p, l) = local_hull_and_project_cooper m ~eliminate round_lower_bound (p, l) in
    saturate srk binding ambient_dim op conjuncts

  let hull_and_project_real srk binding ~eliminate conjuncts =
    let ambient_dim = FV.ambient_dim conjuncts ~except:eliminate in
    let op m (p, l) = local_hull_and_project_real m ~eliminate (p, l) in
    saturate srk binding ambient_dim op conjuncts

  let abstract_terms_by_one_phase_elim srk proj_alg phi terms =
    let ambient_dim = Array.length terms in
    logf ~level:`debug "abstract_terms_by_one_phase_elim: Terms are @[%a@], base is %d@;"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space (Syntax.ArithTerm.pp srk))
      (Array.to_list terms)
      (Array.length terms);
    let binding = FV.mk_standard_binding srk ~project_onto:terms phi in
    logf ~level:`debug "Symbol to dimensions: @[%a@]"
      (FV.pp_symbol_to_dimension srk (Syntax.symbols phi)) binding;
    let abstract ~term_defs ~dimensions_in_terms m (p, l) =
      let eliminate = FV.collect_dimensions (p, l)
                      |> IntSet.union dimensions_in_terms
                      |> IntSet.to_list
      in
      let p_with_terms = P.of_constraints (BatList.enum term_defs)
                         |> P.meet p in
      let abstracted = proj_alg m ~eliminate (p_with_terms, l) in
      logf ~level:`debug "abstract_terms_by_one_phase_elim: Abstracted: @[%a@]@; ambient dimension = %d@;"
        (P.pp Format.pp_print_int) abstracted
        ambient_dim;
      let dd = P.dd_of ambient_dim abstracted in
      logf ~level:`debug "abstract_terms_by_one_phase_elim: abstracted DD: @[%a@]@;"
        (DD.pp Format.pp_print_int) dd;
      dd
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join = DD.join
      ; of_model = FV.abstract_implicant srk binding (`WithTerms abstract) phi
      ; formula_of = formula_of srk binding
      ; top = top ambient_dim
      ; bottom = bottom ambient_dim
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

  let abstract_terms_by_two_phase_elim
        srk proj_alg phi terms =
    let ambient_dim = Array.length terms in
    let binding = FV.mk_standard_binding srk ~project_onto:terms phi in

    logf ~level:`debug "Symbol to dimensions: @[%a@]"
      (FV.pp_symbol_to_dimension srk (Syntax.symbols phi)) binding;

    let abstract ~term_defs ~dimensions_in_terms m (p, l) =
      let original_dimensions = FV.collect_dimensions (p, l) in
      let eliminate = IntSet.diff original_dimensions dimensions_in_terms
                      |> IntSet.to_list in
      let projected = proj_alg m ~eliminate (p, l) in
      let p' = P.meet projected (P.of_constraints (BatList.enum term_defs))
      in
      let () = check_point_in_p srk ~level:`debug binding m p' in
      logf ~level:`debug
        "abstract_terms_by_two_phase_elim: Eliminating dimensions @[%a@] using real QE for @[%a@]@;"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space Format.pp_print_int)
        (IntSet.to_list dimensions_in_terms)
        (P.pp Format.pp_print_int) p';
      P.local_project m (IntSet.to_list dimensions_in_terms) p'
      |> P.dd_of ambient_dim
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join = DD.join
      ; of_model = FV.abstract_implicant srk binding (`WithTerms abstract) phi
      ; formula_of = formula_of srk binding
      ; top = top ambient_dim
      ; bottom = bottom ambient_dim
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

  let abstract_by_local_hull_and_project_cooper
        srk how round_lower_bound phi terms =
    match how with
    | `OnePhaseElim ->
       abstract_terms_by_one_phase_elim srk
         (fun m ~eliminate (p, l) ->
           local_hull_and_project_cooper m ~eliminate round_lower_bound (p, l))
         phi terms
    | `TwoPhaseElim ->
       abstract_terms_by_two_phase_elim srk
         (fun m ~eliminate (p, l) ->
           local_hull_and_project_cooper m ~eliminate round_lower_bound (p, l))
         phi terms

  let abstract_by_local_hull_and_project_real srk how phi terms =
    match how with
    | `OnePhaseElim ->
       abstract_terms_by_one_phase_elim srk local_hull_and_project_real
         phi terms
    | `TwoPhaseElim ->
       abstract_terms_by_two_phase_elim srk local_hull_and_project_real
         phi terms

  let abstract_by_local_project_cooper_and_hull srk how round_lower_bound phi terms =
    match how with
    | `OnePhaseElim ->
       abstract_terms_by_one_phase_elim srk
         (fun m ~eliminate (p, l) ->
           local_project_cooper_and_hull m ~eliminate round_lower_bound (p, l))
         phi terms
    | `TwoPhaseElim ->
       abstract_terms_by_two_phase_elim srk
         (fun m ~eliminate (p, l) ->
           local_project_cooper_and_hull m ~eliminate round_lower_bound (p, l))
         phi terms

end

let local_mixed_lattice_hull = Hull.local_mixed_lattice_hull
let mixed_lattice_hull = Hull.mixed_lattice_hull
let abstract_lattice_hull = Hull.abstract
let partition_vertices_by_integrality = Hull.partition_vertices_by_integrality

let local_project_cooper = CooperProjection.local_project
let project_cooper = CooperProjection.project

let all_variables_are_integral_and_no_strict_ineqs =
  CooperProjection.all_variables_are_integral_and_no_strict_ineqs

let project_cooper_and_hull srk binding ~eliminate round_lower_bound =
  ProjectHull.project_cooper_and_hull srk binding ~eliminate round_lower_bound

let hull_and_project_cooper srk binding ~eliminate
      round_lower_bound =
  ProjectHull.hull_and_project_cooper srk binding ~eliminate round_lower_bound

let hull_and_project_real = ProjectHull.hull_and_project_real

let abstract_by_local_hull_and_project_cooper =
  ProjectHull.abstract_by_local_hull_and_project_cooper

let abstract_by_local_hull_and_project_real =
  ProjectHull.abstract_by_local_hull_and_project_real

let abstract_by_local_project_cooper_and_hull =
  ProjectHull.abstract_by_local_project_cooper_and_hull

let _formula_of_point = FV.formula_of_point
