module V = Linear.QQVector
module P = Polyhedron
module L = IntLattice
module T = Linear.MakeLinearMap(QQ)(Int)(V)(V)

module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

include Log.Make(struct let name = "srk.latticePolyhedron" end)

let () = my_verbosity_level := `trace

let debug ?(level=`debug) f default =
    if Log.level_leq !my_verbosity_level level then
      f
    else
      (fun _ -> default)

module FormulaVectorInterface: sig

  type 'a binding

  (** [symbol_of_dim] and [term_of_adjoined_dim] need to have disjoint domains,
      and [symbol_of_dim (dim_of_symbol s) = s] for all symbols [s].
   *)
  val mk_binding:
    'a Syntax.context ->
    symbol_of_dim: (int -> Syntax.symbol option) ->
    term_of_adjoined_dim: (int -> 'a Syntax.arith_term option) ->
    dim_of_symbol: (Syntax.symbol -> int) -> 'a binding

  val pp_symbol_to_dimension:
    Syntax.Symbol.Set.t -> Format.formatter -> 'a binding -> unit

  val context_in: 'a binding -> 'a Syntax.context

  val formula_of_dd: 'a binding -> DD.closed DD.t -> 'a Syntax.formula

  val formula_of_polyhedron: 'a binding -> P.t -> 'a Syntax.formula

  val formula_of_lattice: 'a binding -> L.t -> 'a Syntax.formula

  val formula_of_point: 'a binding -> Linear.QQVector.t -> 'a Syntax.formula

  val ambient_dim: (P.t * L.t) list -> except:int list -> int

  val collect_dimensions_from_constraints:
    ('a -> V.t) -> 'a BatEnum.t -> IntSet.t

  val collect_dimensions: (P.t * L.t) -> IntSet.t

  (** Lift a local abstraction procedure for a polyhedron-lattice pair into an
      local abstraction procedure for a formula.
      All symbols in the formula must be in the domain of [dim_of_symbol]
      in [binding].
   *)
  val abstract_implicant:
    'a binding ->
    abstract: ((int -> Q.t) -> P.t * L.t -> 'b) -> 'a Syntax.formula ->
    [> `LIRA of 'a Interpretation.interpretation ] -> 'b

  (** A term context consists of a binding and auxiliary data for term
      projection
   *)
  type 'a term_context

  val put_terms_in_initial_segment:
    'a Syntax.context -> 'a Syntax.arith_term array -> 'a term_context

  val binding_in: 'a term_context -> 'a binding
  val dimensions_in_terms: 'a term_context -> IntSet.t
  val constraints_defining_terms:
    'a term_context -> (P.constraint_kind * V.t) list

  val extend_assignment_to_adjoined_dimensions:
    'a term_context -> (int -> QQ.t) -> (int -> QQ.t)

  (** Given a local projection algorithm [proj] that eliminates variables,
      [project_onto_terms term_context proj = proj']
      where [proj'] is a local projection algorithm that projects its input,
      whose constrained dimensions are in the image of [dim_of_symbol] in
      [term_context], onto the dimensions of the terms ([term_of_adjoined_dim])
      in [term_context].
   *)
  val project_onto_terms: 'a term_context ->
    (eliminate: int list -> (int -> QQ.t) -> P.t * L.t -> 'c) ->
    ((int -> QQ.t) -> P.t * L.t -> 'c)

  val check_point_in_p:
    ?level:Log.level -> 'a binding -> (int -> Q.t) -> P.t -> unit

end = struct

  type 'a binding =
    {
      context: 'a Syntax.context
    ; symbol_of_dim: int -> Syntax.symbol option
    ; term_of_adjoined_dim: int -> 'a Syntax.arith_term option
    ; dim_of_symbol: Syntax.symbol -> int
    }

  let mk_binding srk ~symbol_of_dim ~term_of_adjoined_dim ~dim_of_symbol =
    { context = srk
    ; symbol_of_dim
    ; term_of_adjoined_dim
    ; dim_of_symbol
    }

  let pp_symbol_to_dimension symbols fmt binding =
    let srk = binding.context in
    let dim_of_symbol = binding.dim_of_symbol in
    Syntax.Symbol.Set.iter
      (fun symbol ->
        Format.fprintf fmt "binding @[%a@]:@[%a@] to %d@;"
          (Syntax.pp_symbol srk) symbol
          Syntax.pp_typ (Syntax.typ_symbol srk symbol)
          (dim_of_symbol symbol)
      )
      symbols

  let context_in binding = binding.context

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
      (P.enum_constraints p)
      |> collect_dimensions_from_constraints (fun (_, v) -> v)
    in
    let l_dims =
      L.basis l |> BatList.enum
      |> collect_dimensions_from_constraints (fun v -> v)
    in
    IntSet.union p_dims l_dims

  let substitute f v =
    BatEnum.fold (fun v (coeff, dim) ->
        V.add v (V.scalar_mul coeff (f dim)))
      V.zero
      (V.enum v)

  (* TODO: Generalize [of_linterm] etc. to not assume standard
     symbol-dimension binding; then remove translation here. *)
  let vector_of_term srk ~dim_of_symbol t =
    let dim_of_original_dim orig_dim =
      if orig_dim = Linear.const_dim then
        Linear.const_linterm QQ.one
      else
        dim_of_symbol (Syntax.symbol_of_int orig_dim)
        |> V.of_term QQ.one
    in
    Linear.linterm_of srk t |> substitute dim_of_original_dim

  let term_of_dimension binding dim =
    let srk = binding.context in
    let symbol_of_dim = binding.symbol_of_dim in
    let term_of_adjoined_dim = binding.term_of_adjoined_dim in
    if dim = Linear.const_dim then Syntax.mk_real srk QQ.one
    else
      match symbol_of_dim dim with
      | Some s -> Syntax.mk_const srk s
      | None ->
         begin match term_of_adjoined_dim dim with
         | Some term -> term
         | None ->
            failwith
              (Format.sprintf
                 "cannot translate dimension %d to a symbol or term" dim)
         end

  let term_of_vector binding v =
    Linear.term_of_vec binding.context (term_of_dimension binding) v

  let to_inequality binding (ckind, v) =
    let srk = binding.context in
    let zero = Syntax.mk_zero srk in
    let op = match ckind with
      | `Zero -> Syntax.mk_eq srk zero
      | `Nonneg -> Syntax.mk_leq srk zero
      | `Pos -> Syntax.mk_lt srk zero
    in
    let term = term_of_vector binding v in
    op term

  let to_is_int binding v =
    Syntax.mk_is_int binding.context (term_of_vector binding v)

  let formula_of_p_constraints binding enum_constraints p =
    BatEnum.fold
      (fun l (ckind, v) ->
        to_inequality binding (ckind, v) :: l)
      []
      (enum_constraints p)
    |> Syntax.mk_and binding.context

  let formula_of_polyhedron binding p =
    formula_of_p_constraints binding P.enum_constraints p

  let formula_of_dd binding dd =
    formula_of_p_constraints binding DD.enum_constraints dd

  let formula_of_lattice binding l =
    List.fold_left (fun fml v -> to_is_int binding v :: fml) []
      (L.basis l)
    |> Syntax.mk_and binding.context

  let formula_of_point binding v =
    let srk = binding.context in
    let symbol_of_dim = binding.symbol_of_dim in
    let term_of_adjoined_dim = binding.term_of_adjoined_dim in
    let conjuncts =
      V.fold
        (fun dim scalar conjuncts ->
          let r = Syntax.mk_real srk scalar in
          let s = match symbol_of_dim dim with
            | Some s -> Syntax.mk_const srk s
            | None -> begin match term_of_adjoined_dim dim with
                      | Some term -> term
                      | None -> assert false
                      end
          in
          Syntax.mk_eq srk s r :: conjuncts)
        v []
    in
    Syntax.mk_and srk conjuncts

  let formula_of_model binding dimensions m =
    let v = IntSet.fold (fun dim v -> V.add_term (m dim) dim v) dimensions V.zero
    in
    formula_of_point binding v

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
         (pcons, vector_of_term srk ~dim_of_symbol t :: lcons)
      | _ -> assert false
    in
    List.fold_left collect ([], []) atoms

  let ambient_dim conjuncts ~except =
    let except = IntSet.of_list except in
    List.fold_left (fun curr_max (p, l) ->
        let p_dims =
          collect_dimensions_from_constraints
            (fun (_, v) -> v) (P.enum_constraints p)
        in
        let l_dims =
          collect_dimensions_from_constraints
            (fun x -> x) (BatList.enum (L.basis l)) in
        let dims = IntSet.diff (IntSet.union p_dims l_dims) except in
        let curr = IntSet.max_elt dims + 1 in
        Int.max curr curr_max)
      0
      conjuncts

  let mk_assignment binding interp dim =
    let symbol_of_dim = binding.symbol_of_dim in
    let term_of_adjoined_dim = binding.term_of_adjoined_dim in
    if dim = Linear.const_dim then QQ.one
    else
      match symbol_of_dim dim, term_of_adjoined_dim dim with
      | None, None ->
         failwith
           (Format.sprintf "Cannot translate dimension %d to a symbol for evaluation" dim)
      | Some s, _ -> Interpretation.real interp s
      | _, Some t ->
         Interpretation.evaluate_term interp t

  let abstract_implicant binding ~abstract phi model =
    let srk = binding.context in
    match model with
    | `LIRA interp ->
       logf ~level:`debug "abstract_implicant: model is: @[%a@]@;"
         (fun fmt interp ->
           let symbols = Syntax.symbols phi in
           Syntax.Symbol.Set.iter (fun symbol ->
               match Syntax.typ_symbol srk symbol with
               | `TyReal
                 | `TyInt ->
                  let value = Interpretation.real interp symbol in
                  Format.fprintf fmt "(%a: %a, %a) "
                    (Syntax.pp_symbol srk) symbol
                    Syntax.pp_typ (Syntax.typ_symbol srk symbol)
                    QQ.pp value
               | _ -> ()
             )
             symbols
         )
         interp;
       let m = mk_assignment binding interp in
       let implicant = Interpretation.select_implicant interp phi in
       let dim_of_symbol = binding.dim_of_symbol in
       let (pcons, lcons) = match implicant with
         | None -> assert false
         | Some atoms -> constraints_of_implicant srk ~dim_of_symbol atoms
       in
       let (p, l) =
         ( P.of_constraints (BatList.enum pcons)
         , L.hermitize lcons )
       in
       abstract m (p, l)
    | _ -> assert false

  type 'a term_context =
    { terms: 'a Syntax.arith_term Array.t
    ; binding: 'a binding
    ; dimensions_in_terms: IntSet.t
    ; term_definitions: V.t IntMap.t
    }

  let binding_in context = context.binding
  let dimensions_in_terms term_context = term_context.dimensions_in_terms

  let definition_to_constraint (dim, v) =
    (`Zero, V.add_term (QQ.of_int (-1)) dim v)

  let constraints_defining_terms term_ctx =
    IntMap.fold (fun dim v l ->
        definition_to_constraint (dim, v) :: l)
      term_ctx.term_definitions
      []

  let put_terms_in_initial_segment srk terms =
    let base = Array.length terms in
    let dim_of_symbol sym = base + (Syntax.int_of_symbol sym) in
    let symbol_of_dim dim =
      if dim >= base then
        Some (Syntax.symbol_of_int (dim - base))
      else None
    in
    let term_of_adjoined_dim dim =
      if 0 <= dim && dim < base then
        Some (terms.(dim))
      else None
    in
    let binding = { context = srk
                  ; symbol_of_dim
                  ; term_of_adjoined_dim
                  ; dim_of_symbol
                  }
    in
    let (term_definitions, dimensions_in_terms, _) =
      Array.fold_left
        (fun (defs, dims_in_terms, idx) term ->
          let v = vector_of_term srk ~dim_of_symbol term in
          let dimensions =
            collect_dimensions_from_constraints (fun x -> x) (BatList.enum [v])
          in
          (IntMap.add idx v defs, IntSet.union dimensions dims_in_terms, idx + 1)
        )
        (IntMap.empty, IntSet.empty, 0) terms
    in
    { terms
    ; binding
    ; dimensions_in_terms
    ; term_definitions
    }

  let extend_assignment_to_adjoined_dimensions term_context m dim =
    try
      let v = IntMap.find dim term_context.term_definitions in
      Linear.evaluate_affine m v
    with
    | Not_found -> m dim

  let project_onto_terms term_ctx projection =
    let term_equalities = constraints_defining_terms term_ctx in
    let project_onto_terms projection m (p, l) =
      let eliminate = collect_dimensions (p, l)
                      |> IntSet.union term_ctx.dimensions_in_terms
                      |> IntSet.to_list
      in
      let p_with_terms = P.of_constraints (BatList.enum term_equalities)
                         |> P.meet p in
      projection ~eliminate m (p_with_terms, l)
    in
    project_onto_terms projection

  let check_point_in_p ?(level=`debug) binding m p =
    let srk = binding.context in
    let dimensions = collect_dimensions (p, IntLattice.bottom) in
    if (debug ~level (Polyhedron.mem m) true) p then
      ()
    else
      let alpha = formula_of_polyhedron binding p in
      let mphi = formula_of_model binding dimensions m in
      logf ~level "model @[%a@] does not satisfy @[%a@]@;"
        (Syntax.Formula.pp srk) mphi
        (Syntax.Formula.pp srk) alpha

end

module Hull: sig

  val local_mixed_lattice_hull:
    (int -> QQ.t) -> P.t * L.t -> P.t

  (** Ambient dimension has to be at least the maximum constrained dimension
      (computed via dim_of_symbol in binding) + 1.
   *)
  val mixed_lattice_hull:
    'a FormulaVectorInterface.binding -> ambient_dim: int ->
    (P.t * L.t) list -> DD.closed DD.t

  val partition_vertices_by_integrality:
    DD.closed DD.t -> L.t -> (V.t list * V.t list)

  (** `PureGomoryChvatal is guaranteed to work only when all variables are
      implied to be integer-valued, but this is not checked.
      Ambient dimension should be at least as large as the maximum dimension
      occurring in the formula (computed via [dim_of_symbol]) + 1.
   *)
  val abstract: 'a FormulaVectorInterface.binding ->
                [`Mixed | `PureGomoryChvatal] -> ambient_dim:int ->
                'a Syntax.formula -> DD.closed DD.t

end = struct

  module FVI = FormulaVectorInterface

  let partition_vertices_by_integrality dd l =
    BatEnum.fold (fun (integral, non_integral) (gkind, v) ->
        match gkind with
        | `Vertex ->
           if IntLattice.member v l then (v :: integral, non_integral)
           else (integral, v :: non_integral)
        | `Ray -> (integral, non_integral)
        | `Line -> (integral, non_integral)
      ) ([], []) (DD.enum_generators dd)

  let check_hull ?(level=`debug) ?binding p l =
    let ambient = P.max_constrained_dim p + 1 in
    let dd = P.dd_of ambient p in
    let (_, non_integral) =
      debug ~level (partition_vertices_by_integrality dd) ([], []) l in
    match non_integral with
    | [] -> ()
    | _ ->
       begin
         match binding with
         | Some binding ->
            let srk = FVI.context_in binding in
            logf ~level:`debug "check_hull: lattice is: @[%a@]@;"
              (Syntax.Formula.pp srk)
              (FVI.formula_of_lattice binding l);
            List.iter
              (fun v ->
                logf ~level:`debug
                  "Vertex @[%a@] is not in the lattice"
                  (Syntax.Formula.pp srk) (FVI.formula_of_point binding v)
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
    check_hull ~level:`trace p l;
    projected

  let mixed_lattice_hull binding ~ambient_dim conjuncts =
    let module FVI = FormulaVectorInterface in
    let srk = FVI.context_in binding in
    let make_conjunct (p, l) =
      let p_phi = FVI.formula_of_polyhedron binding p in
      let l_phi = FVI.formula_of_lattice binding l
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
      FVI.abstract_implicant binding ~abstract phi
    in
    let domain: ('a, DD.closed DD.t) Abstract.domain =
      {
        join = DD.join
      ; of_model
      ; formula_of = (FVI.formula_of_dd binding)
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
      () (FVI.formula_of_dd binding hull);
    hull

  let abstract binding how ~ambient_dim phi =
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
          FVI.abstract_implicant binding ~abstract phi
      ; formula_of = FVI.formula_of_dd binding
      ; top = P.dd_of ambient_dim P.top
      ; bottom = P.dd_of ambient_dim P.bottom
      }
    in
    let srk = FVI.context_in binding in
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
      () (FVI.formula_of_dd binding hull);
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

  val project: 'a FormulaVectorInterface.binding -> eliminate: int list ->
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
             FormulaVectorInterface.collect_dimensions_from_constraints snd
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

  let formula_of binding (dd, l) =
    let module FVI = FormulaVectorInterface in
    let p_phi = FVI.formula_of_dd binding dd in
    let l_phi = FVI.formula_of_lattice binding l in
    let srk = FVI.context_in binding in
    let fml = Syntax.mk_and srk [p_phi; l_phi] in
    logf ~level:`debug "project_cooper: blocking @[%a@]@;" (Syntax.Formula.pp srk) fml;
    fml

  let project binding ~eliminate round_lower_bound conjuncts =
    let module FVI = FormulaVectorInterface in
    let srk = FVI.context_in binding in
    let make_conjunct (p, l) =
      let p_phi = FVI.formula_of_polyhedron binding p in
      let l_phi = FVI.formula_of_lattice binding l
      in
      Syntax.mk_and srk [p_phi; l_phi]
    in
    let phi = Syntax.mk_or srk (List.map make_conjunct conjuncts) in
    let ambient_dim = FVI.ambient_dim conjuncts ~except:eliminate in
    let eliminate = Array.of_list eliminate in
    let abstract m (p, l) =
      let (p', l', _) = local_project m ~eliminate round_lower_bound (p, l) in
      (P.dd_of ambient_dim p', l')
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join
      ; of_model = FVI.abstract_implicant binding ~abstract phi
      ; formula_of = formula_of binding
      ; top = top ambient_dim
      ; bottom = bottom ambient_dim
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

end

let local_mixed_lattice_hull = Hull.local_mixed_lattice_hull
let mixed_lattice_hull = Hull.mixed_lattice_hull
let abstract_lattice_hull = Hull.abstract
let partition_vertices_by_integrality = Hull.partition_vertices_by_integrality

let local_project_cooper = CooperProjection.local_project
let project_cooper = CooperProjection.project

let all_variables_are_integral_and_no_strict_ineqs =
  CooperProjection.all_variables_are_integral_and_no_strict_ineqs

module ProjectHull : sig
  (** These procedures compute the projection of the lattice hull by
      interleaving local procedures for hulling and projection.
   *)

  val project_cooper_and_hull:
    'a FormulaVectorInterface.binding -> eliminate: int list ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t

  val hull_and_project_cooper:
    'a FormulaVectorInterface.binding -> eliminate: int list ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t

  val hull_and_project_real:
    'a FormulaVectorInterface.binding ->
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

  module FVI = FormulaVectorInterface

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
      local_project_cooper m ~eliminate round_lower_bound
        (p, l) in
    local_mixed_lattice_hull m (projected_p, projected_l)

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
    let hulled = local_mixed_lattice_hull m (p, l) in
    let eliminate = Array.of_list eliminate in
    let (projected, _, _) =
      local_project_cooper m ~eliminate round_lower_bound (hulled, l)
    in
    projected

  (* Same logic as above *)
  let local_hull_and_project_real m ~eliminate (p, l) =
    let hulled = local_mixed_lattice_hull m (p, l) in
    let projected = Polyhedron.local_project m eliminate hulled in
    projected

  let formula_of binding dd =
    let p_phi = FVI.formula_of_polyhedron binding (P.of_dd dd) in
    let srk = FVI.context_in binding in
    logf ~level:`debug "ProjectHull: blocking @[%a@]@;"
      (Syntax.Formula.pp srk) p_phi;
    p_phi

  let top ambient_dim = P.dd_of ambient_dim P.top
  let bottom ambient_dim = P.dd_of ambient_dim P.bottom

  let saturate binding ambient_dim op conjuncts =
    let srk = FVI.context_in binding in
    let make_conjunct (p, l) =
      let p_phi = FVI.formula_of_polyhedron binding p in
      let l_phi = FVI.formula_of_lattice binding l
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
      ; of_model = FVI.abstract_implicant binding ~abstract phi
      ; formula_of = formula_of binding
      ; top = top ambient_dim
      ; bottom = bottom ambient_dim
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

  let project_cooper_and_hull binding ~eliminate round_lower_bound conjuncts =
    let ambient_dim = FVI.ambient_dim conjuncts ~except:eliminate in
    let op m (p, l) = local_project_cooper_and_hull m ~eliminate round_lower_bound (p, l) in
    saturate binding ambient_dim op conjuncts

  let hull_and_project_cooper binding ~eliminate round_lower_bound conjuncts =
    let ambient_dim = FVI.ambient_dim conjuncts ~except:eliminate in
    let op m (p, l) = local_hull_and_project_cooper m ~eliminate round_lower_bound (p, l) in
    saturate binding ambient_dim op conjuncts

  let hull_and_project_real binding ~eliminate conjuncts =
    let ambient_dim = FVI.ambient_dim conjuncts ~except:eliminate in
    let op m (p, l) = local_hull_and_project_real m ~eliminate (p, l) in
    saturate binding ambient_dim op conjuncts

  let abstract_terms_by_one_phase_elim srk proj_alg phi terms =
    let ambient_dim = Array.length terms in
    logf ~level:`debug "abstract_terms_by_one_phase_elim: Terms are @[%a@], base is %d@;"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space (Syntax.ArithTerm.pp srk))
      (Array.to_list terms)
      (Array.length terms);
    let term_context = FVI.put_terms_in_initial_segment srk terms in
    let binding = FVI.binding_in term_context in

    logf ~level:`debug "Symbol to dimensions: @[%a@]"
      (FVI.pp_symbol_to_dimension (Syntax.symbols phi)) binding;

    let abstract_terms m (p, l) =
      let proj ~eliminate m (p, l) = proj_alg m ~eliminate (p, l)
      in
      FVI.project_onto_terms term_context proj m (p, l)
    in
    let abstract m (p, l) =
      let abstracted = abstract_terms m (p, l) in
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
      ; of_model = FVI.abstract_implicant binding ~abstract phi
      ; formula_of = formula_of binding
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
    let module FVI = FormulaVectorInterface in
    let ambient_dim = Array.length terms in
    let term_context = FVI.put_terms_in_initial_segment srk terms in
    let binding = FVI.binding_in term_context in
    let dimensions_in_terms = FVI.dimensions_in_terms term_context in

    logf ~level:`debug "Symbol to dimensions: @[%a@]"
      (FVI.pp_symbol_to_dimension (Syntax.symbols phi)) binding;

    let abstract m (p, l) =
      let original_dimensions = FVI.collect_dimensions (p, l) in
      let eliminate = IntSet.diff original_dimensions
                        (FVI.dimensions_in_terms term_context)
                      |> IntSet.to_list in
      let projected = proj_alg m ~eliminate (p, l) in
      let term_definitions = FVI.constraints_defining_terms term_context in
      let p' = P.meet projected (P.of_constraints (BatList.enum term_definitions))
      in
      let extended_m =
        FVI.extend_assignment_to_adjoined_dimensions term_context m in

      let () = FVI.check_point_in_p ~level:`debug binding extended_m p' in
      logf ~level:`debug
        "abstract_terms_by_two_phase_elim: Eliminating dimensions @[%a@] using real QE for @[%a@]@;"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space Format.pp_print_int)
        (IntSet.to_list dimensions_in_terms)
        (P.pp Format.pp_print_int) p';

      (* Previously: P.local_project m (IntSet.to_list dimensions_in_terms) p'
         without extending model; that should have been a bug
       *)
      P.local_project extended_m (IntSet.to_list dimensions_in_terms) p'
      |> P.dd_of ambient_dim
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join = DD.join
      ; of_model = FVI.abstract_implicant binding ~abstract phi
      ; formula_of = formula_of binding
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

type 'a binding = 'a FormulaVectorInterface.binding

let mk_binding = FormulaVectorInterface.mk_binding

let project_cooper_and_hull binding ~eliminate round_lower_bound =
  ProjectHull.project_cooper_and_hull binding ~eliminate round_lower_bound

let hull_and_project_cooper binding ~eliminate
      round_lower_bound =
  ProjectHull.hull_and_project_cooper binding ~eliminate round_lower_bound

let hull_and_project_real = ProjectHull.hull_and_project_real

let abstract_by_local_hull_and_project_cooper =
  ProjectHull.abstract_by_local_hull_and_project_cooper

let abstract_by_local_hull_and_project_real =
  ProjectHull.abstract_by_local_hull_and_project_real

let abstract_by_local_project_cooper_and_hull =
  ProjectHull.abstract_by_local_project_cooper_and_hull

let _formula_of_point = FormulaVectorInterface.formula_of_point
