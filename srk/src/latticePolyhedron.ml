module V = Linear.QQVector
module P = Polyhedron
module L = IntLattice
module T = Linear.MakeLinearMap(QQ)(Int)(V)(V)

module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "srk.latticePolyhedron" end)

let () = my_verbosity_level := `trace

module FormulaVectorInterface: sig

  (* TODO: Generalize [of_linterm] etc. to not assume standard
     symbol-dimension binding; then remove translation here. *)

  val to_inequality:
    'a Syntax.context -> symbol_of_dim:(int -> Syntax.symbol option) ->
    ?term_of_dim:(int -> 'a Syntax.arith_term option) ->
    [< `Nonneg | `Pos | `Zero ] * V.t -> 'a Syntax.formula

  val to_is_int:
    'a Syntax.context -> symbol_of_dim:(int -> Syntax.symbol option) ->
    ?term_of_dim:(int -> 'a Syntax.arith_term option) ->
    V.t -> 'a Syntax.formula

  val make_conjunct:
    'a Syntax.context -> symbol_of_dim:(int -> Syntax.symbol option) ->
    P.t * L.t -> 'a Syntax.formula

  val ambient_dim: (P.t * L.t) list -> except:int list -> int

  (** Lift a local abstraction procedure for a polyhedron-lattice pair into an
      local abstraction procedure for a formula.
   *)
  val abstract_implicant:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) ->
    ?term_of_dim:(int -> 'a Syntax.arith_term option) ->
    dim_of_symbol:(Syntax.symbol -> int) ->
    abstract: ((int -> Q.t) -> P.t * L.t -> 'b) ->
    'a Syntax.formula ->
    [> `LIRA of 'a Interpretation.interpretation ] -> 'b

  type 'a bindings =
    {
      sym_of_dim: int -> Syntax.symbol option
    ; term_of_dim: int -> 'a Syntax.arith_term option
    ; dim_of_sym: Syntax.symbol -> int
    }

  val bindings_for_term_abstraction:
    'a Syntax.arith_term array -> 'a bindings

  (* Given a local projection algorithm [proj] that eliminates variables,
     [make_term_abstraction terms proj = proj']
     where [proj'] is a local projection algorithm that projects its input
     that are (must be) in dimensions >= length(terms) onto dimensions
     [0 ... length(terms)] corresponding to [terms].
     That is, the output is the abstraction of the input in terms of [terms].
   *)
  val make_term_abstraction:
    'a Syntax.context ->
    'a Syntax.arith_term array ->
    (eliminate:int list -> (int -> QQ.t) -> P.t * L.t -> 'c) ->
    ((int -> QQ.t) -> P.t * L.t -> 'c)

end = struct
    
  let substitute f v =
    BatEnum.fold (fun v (coeff, dim) ->
        V.add v (V.scalar_mul coeff (f dim)))
      V.zero
      (V.enum v)

  let term_of_vector srk ~symbol_of_dim ?(term_of_dim=fun _ -> None) v =
    let open Syntax in
    let summands =
      V.fold (fun dim coeff l ->
          match symbol_of_dim dim with
          | Some s -> mk_mul srk [mk_real srk coeff; Syntax.mk_const srk s] :: l
          | None ->
             begin match term_of_dim dim with
             | Some term -> term :: l
             | None ->
                if dim <> Linear.const_dim then
                  failwith
                    (Format.sprintf
                       "cannot translate dimension %d to a symbol or term" dim)
                else
                  mk_real srk coeff :: l
             end
        ) v []
      |> List.rev
    in
    mk_add srk summands

  let to_inequality srk ~symbol_of_dim ?(term_of_dim=fun _ -> None) (ckind, v) =
    let zero = Syntax.mk_zero srk in
    let op = match ckind with
      | `Zero -> Syntax.mk_eq srk zero
      | `Nonneg -> Syntax.mk_leq srk zero
      | `Pos -> Syntax.mk_lt srk zero
    in
    let term = term_of_vector srk ~symbol_of_dim ~term_of_dim v in
    op term

  let to_is_int srk ~symbol_of_dim ?(term_of_dim = fun _ -> None) v =
    Syntax.mk_is_int srk (term_of_vector srk ~symbol_of_dim ~term_of_dim v)

  let vector_of_term srk ~dim_of_symbol t =
    let dim_of_original_dim orig_dim =
      if orig_dim = Linear.const_dim then
        Linear.const_linterm QQ.one
      else
        dim_of_symbol (Syntax.symbol_of_int orig_dim)
        |> V.of_term QQ.one
    in
    Linear.linterm_of srk t |> substitute dim_of_original_dim

  let constraints_of_implicant srk ~dim_of_symbol atoms =
    let collect (pcons, lcons) literal =
      match Syntax.Formula.destruct srk literal with
      | `Atom (`Arith (sign, t1, t2)) ->
         let (v1, v2) =
           ( vector_of_term srk ~dim_of_symbol t1
           , vector_of_term srk ~dim_of_symbol t2 )
         in
         let v = V.sub v2 v1 in
         let cnstr = match sign with
           | `Eq -> (`Zero, v)
           | `Leq -> (`Nonneg, v)
           | `Lt -> (`Pos, v) in
         (cnstr :: pcons, lcons)
      | `Atom (`IsInt t) ->
         (pcons, Linear.linterm_of srk t :: lcons)
      | _ -> assert false
    in
    List.fold_left collect ([], []) atoms

  let make_conjunct srk ~symbol_of_dim (p, l) =
    let inequalities =
      BatEnum.fold
        (fun l (ckind, v) -> to_inequality srk ~symbol_of_dim (ckind, v) :: l)
        []
        (Polyhedron.enum_constraints p)
    in
    let integral =
      List.fold_left
        (fun ints v -> Syntax.mk_is_int srk (Linear.of_linterm srk v) :: ints)
        []
        (IntLattice.basis l)
    in Syntax.mk_and srk (List.rev_append integral inequalities)

  let collect_dimensions_from_constraints to_vector cnstrs =
    BatEnum.fold
      (fun dims cnstr ->
        let v = to_vector cnstr in
        V.fold
          (fun dim _coeff dims ->
            if dim <> Linear.const_dim then IntSet.add dim dims
            else dims
          )
          v dims)
      IntSet.empty
      cnstrs

  let collect_dimensions (p, l) =
    let p_dims =
      (Polyhedron.enum_constraints p)
      |> collect_dimensions_from_constraints (fun (_, v) -> v)
    in
    let l_dims =
      IntLattice.basis l |> BatList.enum
      |> collect_dimensions_from_constraints (fun v -> v)
    in
    IntSet.union p_dims l_dims

  let ambient_dim conjuncts ~except =
    let except = IntSet.of_list except in
    List.fold_left (fun curr_max (p, l) ->
        let p_dims =
          collect_dimensions_from_constraints
            (fun (_, v) -> v) (Polyhedron.enum_constraints p)
        in
        let l_dims =
          collect_dimensions_from_constraints
            (fun x -> x) (BatList.enum (IntLattice.basis l)) in
        let dims = IntSet.diff (IntSet.union p_dims l_dims) except in
        let curr = IntSet.max_elt dims + 1 in
        Int.max curr curr_max)
      0
      conjuncts

  let abstract_implicant
        srk ~symbol_of_dim ?(term_of_dim = fun _ -> None) ~dim_of_symbol ~abstract phi model =
    match model with
    | `LIRA interp ->
       let m dim =
         if dim = Linear.const_dim then QQ.one
         else
           match symbol_of_dim dim, term_of_dim dim with
           | None, None ->
              failwith
                (Format.sprintf "Cannot translate dimension %d to a symbol for evaluation" dim)
           | Some s, _ -> Interpretation.real interp s
           | _, Some t ->
              Interpretation.evaluate_term interp t
       in
       let implicant = Interpretation.select_implicant interp phi in
       let (pcons, lcons) = match implicant with
         | None -> assert false
         | Some atoms -> constraints_of_implicant srk ~dim_of_symbol atoms
       in
       let (p, l) =
         ( Polyhedron.of_constraints (BatList.enum pcons)
         , IntLattice.hermitize lcons )
       in
       abstract m (p, l)
    | _ -> assert false

  type 'a bindings =
    {
      sym_of_dim: int -> Syntax.symbol option
    ; term_of_dim: int -> 'a Syntax.arith_term option
    ; dim_of_sym: Syntax.symbol -> int
    }

  let bindings_for_term_abstraction terms =
    let base = Array.length terms in
    let dim_of_symbol sym = base + (Syntax.int_of_symbol sym) in
    let symbol_of_dim dim =
      if dim >= base then
        Some (Syntax.symbol_of_int (dim - base))
      else None
    in
    let term_of_dim dim =
      if 0 <= dim && dim < base then
        Some (Array.get terms dim)
      else None
    in
    { sym_of_dim = symbol_of_dim
    ; term_of_dim
    ; dim_of_sym = dim_of_symbol
    }

  let make_term_abstraction srk terms projection =
    let term_vectors =
      let base = Array.length terms in
      Array.fold_left
        (fun (vs, idx) term ->
          let v = vector_of_term srk
                    ~dim_of_symbol:(fun sym -> base + Syntax.int_of_symbol sym)
                    term in
          ((`Zero, V.add_term (QQ.of_int (-1)) idx v) :: vs, idx + 1)
        )
        ([], 0) terms
      |> fst
    in
    let project_terms projection m (p, l) =
      let eliminate = collect_dimensions (p, l) |> IntSet.to_list in
      let p_with_terms = Polyhedron.of_constraints (BatList.enum term_vectors)
                         |> Polyhedron.meet p in
      projection ~eliminate m (p_with_terms, l)
    in
    project_terms projection
    
end

module MixedHull: sig

  val local_mixed_lattice_hull:
    (int -> QQ.t) -> Polyhedron.t * IntLattice.t -> Polyhedron.t

  val mixed_lattice_hull:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) ->
    dim_of_symbol:(Syntax.symbol -> int) ->
    (Polyhedron.t * IntLattice.t) list -> DD.closed DD.t

  val abstract:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    'a Syntax.formula -> DD.closed DD.t

end = struct

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
       ax <= b, ax' < b', ar <= 0, a(x-r) <= b, a'(x - r) < b'
     *)
    let system = Polyhedron.enum_constraints p in
    BatEnum.iter (fun (ckind, v) ->
        let recession_ineq = match ckind with
          | `Pos -> `Nonneg
          | _ -> ckind in
        let ray_constraint = remap_vector var_to_ray_var v in
        let subspace_point_constraint = V.sub v ray_constraint in
        BatEnum.push system (recession_ineq, ray_constraint);
        BatEnum.push system (ckind, subspace_point_constraint))
      (Polyhedron.enum_constraints p);
    Polyhedron.of_constraints system

  let subspace_restriction var_to_ray_var l m =
    (* Int(cx + d) --> c (x - r) = c x0 *)
    let constraints = BatEnum.empty () in
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
      (IntLattice.basis l);
    Polyhedron.of_constraints constraints

  let ray_dim_of_dim start x = start + x
  (* let is_ray_dim start x = (x - start >= 0) *)

  let local_mixed_lattice_hull m (p, l) =
    let start = Int.max (Polyhedron.max_constrained_dim p)
                  (IntLattice.max_dim l) + 1 in
    let pre_abstraction = recession_extension (ray_dim_of_dim start) p in
    let abstraction = Polyhedron.meet pre_abstraction
                        (subspace_restriction (ray_dim_of_dim start) l m)
    in
    logf ~level:`debug "local_mixed_lattice_hull, before projection: @[%a@]@;"
      (Polyhedron.pp Format.pp_print_int) abstraction;
    let projected =
      (* Local projection diverges if we do local projection here! *)
      (* Polyhedron.local_project
        (fun dim -> if is_ray_dim start dim then QQ.zero else m dim)
        (BatList.of_enum (BatEnum.(--^) start (2 * start)))
        abstraction *)
      Polyhedron.project (BatList.of_enum (BatEnum.(--^) start (2 * start)))
        abstraction
    in
    logf ~level:`debug "after projection: @[%a@]@;"
      (Polyhedron.pp Format.pp_print_int) projected;
    projected

  let formula_of srk ~symbol_of_dim dd =
    BatEnum.fold
      (fun l (ckind, v) -> FormulaVectorInterface.to_inequality srk ~symbol_of_dim (ckind, v) :: l)
      []
      (DD.enum_constraints dd)
    |> Syntax.mk_and srk

  let mixed_lattice_hull srk ~symbol_of_dim ~dim_of_symbol conjuncts =
    let open FormulaVectorInterface in
    let phi = Syntax.mk_or srk (List.map (make_conjunct srk ~symbol_of_dim) conjuncts) in
    let ambient_dim = ambient_dim conjuncts ~except:[] in
    let of_model =
      let abstract m (p, l) =
        local_mixed_lattice_hull m (p, l)
        |> Polyhedron.dd_of ambient_dim
      in
      FormulaVectorInterface.abstract_implicant srk ~symbol_of_dim ~dim_of_symbol ~abstract phi
    in
    let domain: ('a, DD.closed DD.t) Abstract.domain =
      {
        join = DD.join
      ; of_model
      ; formula_of = formula_of srk ~symbol_of_dim
      ; top = Polyhedron.dd_of ambient_dim Polyhedron.top
      ; bottom = Polyhedron.dd_of ambient_dim Polyhedron.bottom
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

  let abstract srk ~symbol_of_dim ~dim_of_symbol phi =
    let ambient_dim =
      let dims = Syntax.Symbol.Set.fold
                   (fun sym dims -> IntSet.add (dim_of_symbol sym) dims)
                   (Syntax.symbols phi) IntSet.empty in
      (IntSet.max_elt dims) + 1
    in
    let abstract m (p, l) =
      local_mixed_lattice_hull m (p, l) |> Polyhedron.dd_of ambient_dim in
    let domain: ('a, 'b) Abstract.domain =
      {
        join = DD.join
      ; of_model =
          FormulaVectorInterface.abstract_implicant srk ~symbol_of_dim ~dim_of_symbol
            ~abstract phi
      ; formula_of = formula_of srk ~symbol_of_dim
      ; top = Polyhedron.dd_of ambient_dim Polyhedron.top
      ; bottom = Polyhedron.dd_of ambient_dim Polyhedron.bottom
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

end

type ceiling =
  {
    round_value: [`Nonneg | `Pos] -> QQ.t -> QQ.t
  ; round_term:
      [`Nonneg | `Pos] -> V.t -> (int -> QQ.t) ->
      V.t * (P.constraint_kind * V.t) list * V.t list
  }

module CooperProjection : sig

  val local_project:
    (int -> QQ.t) -> eliminate: int Array.t ->
    [`RoundLowerBound of ceiling | `AssumeVariablesIntegral] ->
    P.t * L.t ->
    P.t * L.t * [`MinusInfinity | `PlusInfinity | `Term of V.t] Array.t

  val project:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    eliminate: int list ->
    [`RoundLowerBound of ceiling | `AssumeVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t * L.t

  val abstract:
    'a Syntax.context ->
    [`RoundLowerBound of ceiling | `AssumeVariablesIntegral] ->
    'a Syntax.formula -> ('a Syntax.arith_term) array ->
    DD.closed DD.t * L.t

  (** Identity ceiling. When all variables are guaranteed to be integer-valued
      (e.g., of integer type within a syntactic context), and all inequalities
      are loose, no rounding is needed for local projection to be image-finite.
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
                 | `Nonneg -> `Nonneg
                 | `Pos -> `Pos
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
      List.map (substitute_term solution dim_to_elim) (IntLattice.basis lattice)
      |> List.rev_append integral_cond
      |> IntLattice.hermitize
    in
    if Option.is_some equality then
      let v = Option.get equality in
      let (coeff, v') = V.pivot dim_to_elim v in
      let solution = V.scalar_mul (QQ.negate (QQ.inverse coeff)) v' in
      let new_p = substitute_and_adjoin_ineqs solution [] in
      let new_l = substitute_and_adjoin_integral solution [] in
      (new_p, new_l, `Term solution)
    else if (not has_upper_bound) || glb = None then
      ( P.of_constraints (BatList.enum irrelevant)
      , IntLattice.project (fun dim' -> dim' <> dim_to_elim) lattice
      , if not has_upper_bound then `PlusInfinity else `MinusInfinity
      )
    else
      let (rounded_value, cnstr_kind, glb_v) = Option.get glb in
      let modulus = BatList.fold_left
                      (fun m v ->
                        let coeff = V.coeff dim_to_elim v in
                        if QQ.equal coeff QQ.zero then m
                        else QQ.lcm m (QQ.inverse coeff))
                      QQ.one (* [P /\ L |= Int(x)] is assumed *)
                      (IntLattice.basis lattice)
      in
      let (rounded_term, inequalities, integrality) =
        round_lower_bound.round_term
          (match cnstr_kind with
           | `Nonneg -> `Nonneg
           | `Pos -> `Pos
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
        (Polyhedron.pp Format.pp_print_int) polyhedron
        (IntLattice.pp Format.pp_print_int) lattice;
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
        (Polyhedron.pp Format.pp_print_int) new_p
        (IntLattice.pp Format.pp_print_int) new_l
        (V.pp_term Format.pp_print_int) solution;
      (new_p, new_l, `Term solution)


  (* When strict inequalities are present, we leave it to the user to clear
     denominators and normalize to a form with only loose inequalities.
   *)
  let all_variables_are_integral_and_no_strict_ineqs =
    {
      round_value = (fun _ x -> x)
    ; round_term =
        (fun _ lower_bound _m -> (lower_bound, [], []))
    }

  let clear_strict_asssuming_integral (ckind, v) =
    match ckind with
    | `Pos ->
       (`Nonneg, V.sub (V.scalar_mul (QQ.of_zz (V.common_denominator v)) v)
                   (V.of_term QQ.one Linear.const_dim))
    | _ -> (ckind, v)

  let normalize_strict_ineqs p =
    let cnstrs = BatEnum.empty () in
    BatEnum.iter
      (fun (ckind, v) ->
        BatEnum.push cnstrs
          (clear_strict_asssuming_integral (ckind, v)))
      (Polyhedron.enum_constraints p);
    Polyhedron.of_constraints cnstrs

  let local_project m ~eliminate
        round_lower_bound
        (p, l) =
    let (rounded_p, round_lower_bound) =
      match round_lower_bound with
      | `RoundLowerBound round_lower_bound ->
         (p, round_lower_bound)
      | `AssumeVariablesIntegral ->
         ( normalize_strict_ineqs p
         , all_variables_are_integral_and_no_strict_ineqs)
    in
    let (p, l, ts) =
      Array.fold_left
        (fun (p, l, ts) dim_to_elim ->
          let (p', l', t') = local_project_one m dim_to_elim ~round_lower_bound p l in
          logf ~level:`debug
            "local_project_cooper: eliminated %d to get result: @[%a@]@;"
            dim_to_elim
            (Polyhedron.pp Format.pp_print_int) p';
          (p', l', t' :: ts)
        )
        (rounded_p, l, [])
        eliminate
    in
    (p, l, Array.of_list (List.rev ts))

  let default_lattice = IntLattice.hermitize [Linear.const_linterm QQ.one]

  let top ambient_dim =
    (Polyhedron.dd_of ambient_dim Polyhedron.top, default_lattice)

  let bottom ambient_dim =
    (Polyhedron.dd_of ambient_dim Polyhedron.bottom, default_lattice)

  let join (p1, l1) (p2, l2) =
    (DD.join p1 p2, IntLattice.intersect l1 l2)

  let formula_of ~symbol_of_dim ?(term_of_dim=fun _ -> None) srk (dd, l) =
    let pcons =
      BatEnum.fold
        (fun l (ckind, v) ->
          FormulaVectorInterface.to_inequality srk ~symbol_of_dim ~term_of_dim (ckind, v) :: l)
        []
        (DD.enum_constraints dd)
    in
    let lcons =
      List.fold_left (fun fml v ->
          FormulaVectorInterface.to_is_int srk ~symbol_of_dim ~term_of_dim v :: fml)
        []
        (IntLattice.basis l)
    in
    let fml = Syntax.mk_and srk (List.rev_append lcons pcons) in
    logf ~level:`debug "project_cooper: blocking @[%a@]@;" (Syntax.Formula.pp srk) fml;
    fml

  let project srk ~symbol_of_dim ~dim_of_symbol ~eliminate
        round_lower_bound
        conjuncts =
    let open FormulaVectorInterface in
    let phi = Syntax.mk_or srk (List.map (make_conjunct srk ~symbol_of_dim) conjuncts) in
    let ambient_dim = ambient_dim conjuncts ~except:eliminate in
    let eliminate = Array.of_list eliminate in
    let abstract m (p, l) =
      let (p', l', _) = local_project m ~eliminate round_lower_bound (p, l) in
      (Polyhedron.dd_of ambient_dim p', l')
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join
      ; of_model = FormulaVectorInterface.abstract_implicant srk ~symbol_of_dim ~dim_of_symbol
                     ~abstract phi
      ; formula_of = formula_of srk ~symbol_of_dim
      ; top = top ambient_dim
      ; bottom = bottom ambient_dim
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

  let abstract srk round_lower_bound phi terms =
    let module FVI = FormulaVectorInterface in
    let ambient_dim = Array.length terms in
    let FVI.{sym_of_dim ; term_of_dim; dim_of_sym} =
      FVI.bindings_for_term_abstraction terms
    in
    let abstract_terms =
      let variable_projection ~eliminate m (p, l) =
        let eliminate = Array.of_list eliminate in
        local_project m ~eliminate round_lower_bound (p, l)
      in
      FVI.make_term_abstraction srk terms variable_projection
    in
    let abstract m (p, l) =
      let (p', l', _) = abstract_terms m (p, l) in
      (Polyhedron.dd_of ambient_dim p', l')
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join
      ; of_model =
          FVI.abstract_implicant srk ~symbol_of_dim:sym_of_dim
            ~term_of_dim ~dim_of_symbol:dim_of_sym
            ~abstract phi
      ; formula_of = formula_of srk ~symbol_of_dim:sym_of_dim ~term_of_dim
      ; top = top ambient_dim
      ; bottom = bottom ambient_dim
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

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

let local_mixed_lattice_hull = MixedHull.local_mixed_lattice_hull
let mixed_lattice_hull = MixedHull.mixed_lattice_hull
let abstract_lattice_hull = MixedHull.abstract
let local_project_cooper = CooperProjection.local_project
let project_cooper = CooperProjection.project
let abstract_cooper = CooperProjection.abstract

let all_variables_are_integral_and_no_strict_ineqs =
  CooperProjection.all_variables_are_integral_and_no_strict_ineqs

module ProjectHull : sig
  (** These procedures compute the projection of the lattice hull by
      interleaving local procedures for hulling and projection.
   *)

  val project_and_hull:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    eliminate: int list ->
    [`RoundLowerBound of ceiling | `AssumeVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t

  val hull_and_project:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    eliminate: int list ->
    [`RoundLowerBound of ceiling | `AssumeVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t

  val abstract_by_local_project_and_hull:
    'a Syntax.context ->
    [`RoundLowerBound of ceiling | `AssumeVariablesIntegral] ->
    'a Syntax.formula -> ('a Syntax.arith_term) array -> DD.closed DD.t

  val abstract_by_local_hull_and_project:
    'a Syntax.context ->
    [`RoundLowerBound of ceiling | `AssumeVariablesIntegral] ->
    'a Syntax.formula -> ('a Syntax.arith_term) array -> DD.closed DD.t

end = struct

  let local_project_and_hull m ~eliminate round_lower_bound (p, l) =
    let eliminate = Array.of_list eliminate in
    let (projected_p, projected_l, _terms) =
      local_project_cooper m ~eliminate round_lower_bound
        (p, l) in
    local_mixed_lattice_hull m (projected_p, projected_l)

  let local_hull_and_project m ~eliminate round_lower_bound (p, l) =
    let hulled = local_mixed_lattice_hull m (p, l) in
    let eliminate = Array.of_list eliminate in
    let (projected, _, _) =
      local_project_cooper m ~eliminate round_lower_bound (hulled, l)
    in
    projected

  let formula_of srk symbol_of_dim ?(term_of_dim=(fun _ -> None)) dd =
    let pcons =
      BatEnum.fold
        (fun l (ckind, v) ->
          FormulaVectorInterface.to_inequality srk ~symbol_of_dim ~term_of_dim
            (ckind, v) :: l)
        []
        (DD.enum_constraints dd)
    in
    let fml = Syntax.mk_and srk pcons in
    logf ~level:`debug "ProjectHull: blocking @[%a@]@;" (Syntax.Formula.pp srk) fml;
    fml

  let top ambient_dim = Polyhedron.dd_of ambient_dim Polyhedron.top
  let bottom ambient_dim = Polyhedron.dd_of ambient_dim Polyhedron.bottom

  let saturate
        srk ~symbol_of_dim ~dim_of_symbol ~eliminate round_lower_bound
        op conjuncts =
    let open FormulaVectorInterface in
    let phi = Syntax.mk_or srk
                (List.map (make_conjunct srk ~symbol_of_dim) conjuncts)
    in
    let ambient_dim = ambient_dim conjuncts ~except:eliminate in
    let abstract m (p, l) =
      op m ~eliminate round_lower_bound (p, l)
      |> Polyhedron.dd_of ambient_dim
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join = DD.join
      ; of_model = FormulaVectorInterface.abstract_implicant srk
                     ~symbol_of_dim ~dim_of_symbol ~abstract phi
      ; formula_of = formula_of srk symbol_of_dim
      ; top = top ambient_dim
      ; bottom = bottom ambient_dim
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

  let project_and_hull srk ~symbol_of_dim ~dim_of_symbol ~eliminate
        round_lower_bound =
    saturate srk ~symbol_of_dim ~dim_of_symbol ~eliminate round_lower_bound
      local_project_and_hull

  let hull_and_project srk ~symbol_of_dim ~dim_of_symbol ~eliminate
        round_lower_bound =
    saturate srk ~symbol_of_dim ~dim_of_symbol ~eliminate round_lower_bound
      local_hull_and_project

  let abstract_terms srk local_project round_lower_bound phi terms =
    let module FVI = FormulaVectorInterface in
    let ambient_dim = Array.length terms in
    Format.printf "abstract_terms: Terms are @[%a@], base is %d@;"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space (Syntax.ArithTerm.pp srk))
      (Array.to_list terms)
      (Array.length terms);
    let FVI.{ sym_of_dim; term_of_dim; dim_of_sym } =
      FVI.bindings_for_term_abstraction terms in
    let abstract_terms =
      let proj ~eliminate m (p, l) =
        local_project m ~eliminate round_lower_bound (p, l)
      in
      FVI.make_term_abstraction srk terms proj
    in    
    let abstract m (p, l) =
      let abstracted = abstract_terms m (p, l) in
      Format.printf "Abstracted: @[%a@]@;" (Polyhedron.pp Format.pp_print_int)
        abstracted;
      Polyhedron.dd_of ambient_dim abstracted
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join = DD.join
      ; of_model = FVI.abstract_implicant srk
                     ~symbol_of_dim:sym_of_dim
                     ~term_of_dim
                     ~dim_of_symbol:dim_of_sym ~abstract phi
      ; formula_of = formula_of srk sym_of_dim ~term_of_dim
      ; top = top ambient_dim
      ; bottom = bottom ambient_dim
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

  let abstract_by_local_project_and_hull srk round_lower_bound phi terms =
    abstract_terms srk local_project_and_hull round_lower_bound phi terms

  let abstract_by_local_hull_and_project srk round_lower_bound phi terms =
    abstract_terms srk local_hull_and_project round_lower_bound phi terms

end

(*
let local_project_and_hull m ~eliminate
      ?(round_lower_bound = CooperProjection.all_variables_are_integral_and_no_strict_ineqs) =
  ProjectHull.local_project_and_hull m ~eliminate ~round_lower_bound
 *)

let project_and_hull srk ~symbol_of_dim ~dim_of_symbol ~eliminate round_lower_bound =
  ProjectHull.project_and_hull srk ~symbol_of_dim ~dim_of_symbol ~eliminate
    round_lower_bound
  
let hull_and_project srk ~symbol_of_dim ~dim_of_symbol ~eliminate round_lower_bound =
  ProjectHull.hull_and_project srk ~symbol_of_dim ~dim_of_symbol ~eliminate
    round_lower_bound
  
let abstract_by_local_hull_and_project =
  ProjectHull.abstract_by_local_hull_and_project
let abstract_by_local_project_and_hull =
  ProjectHull.abstract_by_local_project_and_hull
