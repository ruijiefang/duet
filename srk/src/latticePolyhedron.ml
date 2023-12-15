module V = Linear.QQVector
module P = Polyhedron
module L = IntLattice
module T = Linear.MakeLinearMap(QQ)(Int)(V)(V)

module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

include Log.Make(struct let name = "srk.latticePolyhedron" end)

(* let () = my_verbosity_level := `trace *)

module FormulaVectorInterface: sig

  (* TODO: Generalize [of_linterm] etc. to not assume standard
     symbol-dimension binding; then remove translation here. *)

  val formula_of_dd:
    'a Syntax.context -> symbol_of_dim:(int -> Syntax.symbol option) ->
    ?term_of_dim:(int -> 'a Syntax.arith_term option) -> DD.closed DD.t ->
    'a Syntax.formula

  val formula_of_polyhedron:
    'a Syntax.context -> symbol_of_dim:(int -> Syntax.symbol option) ->
    ?term_of_dim:(int -> 'a Syntax.arith_term option) -> P.t ->
    'a Syntax.formula

  val formula_of_lattice:
    'a Syntax.context -> symbol_of_dim:(int -> Syntax.symbol option) ->
    ?term_of_dim:(int -> 'a Syntax.arith_term option) -> L.t ->
    'a Syntax.formula

  val ambient_dim: (P.t * L.t) list -> except:int list -> int

  val collect_dimensions_from_constraints:
    ('a -> V.t) -> 'a BatEnum.t -> IntSet.t

  val collect_dimensions: (P.t * L.t) -> IntSet.t

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

  val term_definitions_and_dimensions_in_terms:
    'a Syntax.context -> 'a Syntax.arith_term Array.t ->
    (P.constraint_kind * V.t) List.t * IntSet.t

  (* Given a local projection algorithm [proj] that eliminates variables,
     [project_onto_terms terms proj = proj']
     where [proj'] is a local projection algorithm that projects its input
     that are (must be) in dimensions >= length(terms) onto dimensions
     [0 ... length(terms)] corresponding to [terms].
     That is, the output is the abstraction of the input in terms of [terms].
   *)
  val project_onto_terms:
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
    Linear.term_of_vec srk
      (fun dim ->
        if dim = Linear.const_dim then mk_real srk QQ.one
        else
          match symbol_of_dim dim with
          | Some s -> mk_const srk s
          | None ->
             begin match term_of_dim dim with
             | Some term -> term
             | None ->
                failwith
                  (Format.sprintf
                     "cannot translate dimension %d to a symbol or term" dim)
             end
      )
      v

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

  let formula_of_p_constraints srk ~symbol_of_dim ?(term_of_dim = fun _ -> None)
        enum_constraints p =
    BatEnum.fold
      (fun l (ckind, v) ->
        to_inequality srk ~symbol_of_dim ~term_of_dim (ckind, v) :: l)
      []
      (enum_constraints p)
    |> Syntax.mk_and srk

  let formula_of_polyhedron srk ~symbol_of_dim ?(term_of_dim = fun _ -> None) p =
    formula_of_p_constraints srk ~symbol_of_dim ~term_of_dim P.enum_constraints p

  let formula_of_dd srk ~symbol_of_dim ?(term_of_dim = fun _ -> None) dd =
    formula_of_p_constraints srk ~symbol_of_dim ~term_of_dim DD.enum_constraints dd

  let formula_of_lattice srk ~symbol_of_dim ?(term_of_dim = fun _ -> None) l =
    List.fold_left (fun fml v ->
        to_is_int srk ~symbol_of_dim ~term_of_dim v :: fml)
      []
      (L.basis l)
    |> Syntax.mk_and srk

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
         (pcons, vector_of_term srk ~dim_of_symbol t :: lcons)
      | _ -> assert false
    in
    List.fold_left collect ([], []) atoms

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

  let abstract_implicant
        srk ~symbol_of_dim ?(term_of_dim = fun _ -> None) ~dim_of_symbol
        ~abstract phi model =
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
         ( P.of_constraints (BatList.enum pcons)
         , L.hermitize lcons )
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

  let term_definitions_and_dimensions_in_terms srk terms =
    let base = Array.length terms in
      Array.fold_left
        (fun (vs, dims_in_terms, idx) term ->
          let v = vector_of_term srk
                    ~dim_of_symbol:(fun sym -> base + Syntax.int_of_symbol sym)
                    term in
          let dimensions =
            collect_dimensions_from_constraints (fun x -> x) (BatList.enum [v])
          in
          let equality = (`Zero, V.add_term (QQ.of_int (-1)) idx v) in
          (equality :: vs, IntSet.union dimensions dims_in_terms, idx + 1)
        )
        ([], IntSet.empty, 0) terms
      |> (fun (vs, dims, _) -> (vs, dims))

  let project_onto_terms srk terms projection =
    let (term_equalities, dimensions_in_terms) =
      term_definitions_and_dimensions_in_terms srk terms in
    let project_onto_terms projection m (p, l) =
      let eliminate = collect_dimensions (p, l)
                      |> IntSet.union dimensions_in_terms
                      |> IntSet.to_list
      in
      let p_with_terms = P.of_constraints (BatList.enum term_equalities)
                         |> P.meet p in
      projection ~eliminate m (p_with_terms, l)
    in
    project_onto_terms projection

end

module Testing = struct

  let print_symbol_dimension_bindings srk dim_of_sym phi () =
    Syntax.Symbol.Set.iter
      (fun symbol ->
        logf ~level:`trace "Binding @[%a@]:@[%a@] to %d@;"
          (Syntax.pp_symbol srk) symbol
          Syntax.pp_typ (Syntax.typ_symbol srk symbol)
          (dim_of_sym symbol);
      )
      (Syntax.symbols phi)

  let model_satisfies srk symbol_of_dim term_of_dim m (p, l) abstraction =
    let open FormulaVectorInterface in
    let solver = Smt.StdSolver.make srk in
    let alpha = formula_of_polyhedron srk ~symbol_of_dim ~term_of_dim
                  abstraction in
    let formula_of_model =
      let dimensions = FormulaVectorInterface.collect_dimensions (p, l) in
      IntSet.fold (fun dim conjuncts ->
          let r = Syntax.mk_real srk (m dim) in
          let s = match symbol_of_dim dim with
            | Some s -> Syntax.mk_const srk s
            | None -> begin match term_of_dim dim with
                      | Some term -> term
                      | None -> assert false
                      end
          in
          Syntax.mk_eq srk s r :: conjuncts)
        dimensions []
      |> Syntax.mk_and srk
    in
    Smt.StdSolver.add solver [formula_of_model; Syntax.mk_not srk alpha];
    let check_model =
      match Smt.StdSolver.get_model solver with
      | `Sat _ ->
         Some
           (Format.asprintf "model @[%a@] does not satisfy @[%a@]@;"
              (Syntax.Formula.pp srk) formula_of_model
              (Syntax.Formula.pp srk) alpha)

      | `Unsat -> None
      | `Unknown -> Some "unknown"
    in check_model

  let test_implication srk err phi1 phi2 =
    let solver = Smt.StdSolver.make srk in
    Smt.StdSolver.add solver [phi1; Syntax.mk_not srk phi2];
    match Smt.StdSolver.get_model solver with
    | `Sat _ ->
       Some (Format.asprintf err
               (Syntax.Formula.pp srk) phi1
               (Syntax.Formula.pp srk) phi2)
    | `Unsat -> None
    | `Unknown -> Some "unknown"

  let _abstraction_implies_implicant
        srk symbol_of_dim term_of_dim (p, l) abstraction =
    let open FormulaVectorInterface in
    let p_phi = formula_of_polyhedron srk ~symbol_of_dim ~term_of_dim p in
    let l_phis = formula_of_lattice srk ~symbol_of_dim ~term_of_dim l in
    let phi = Syntax.mk_and srk [p_phi; l_phis] in
    let alpha = formula_of_polyhedron srk ~symbol_of_dim ~term_of_dim abstraction
    in
    test_implication srk
      "Fail: abstraction @[%a@] does not imply implicant @[%a@]@;"
      alpha phi

  (* Can only be used to test (the final result of) projection,
     not local projection.
   *)
  let _implies_abstraction
        srk symbol_of_dim term_of_dim (p, l) abstraction =
    let open FormulaVectorInterface in
    let p_phi = formula_of_polyhedron srk ~symbol_of_dim ~term_of_dim p in
    let l_phis = formula_of_lattice srk ~symbol_of_dim ~term_of_dim l in
    let phi = Syntax.mk_and srk [p_phi; l_phis] in
    let alpha = formula_of_polyhedron srk ~symbol_of_dim ~term_of_dim abstraction
    in
    test_implication srk
      "Fail: @[%a@] does not imply abstraction @[%a@]@;"
      phi alpha

end

module Hull: sig

  val local_mixed_lattice_hull:
    (int -> QQ.t) -> P.t * L.t -> P.t

  val mixed_lattice_hull:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) ->
    ?term_of_dim:(int -> 'a Syntax.arith_term option) ->
    dim_of_symbol:(Syntax.symbol -> int) ->
    ambient_dim: int ->
    (P.t * L.t) list -> DD.closed DD.t

  (** `PureGomoryChvatal is guaranteed to work only when all variables are
      implied to be integer-valued, but this is not checked.
      Ambient dimension should be at least as large as the maximum dimension
      occurring in the formula (computed via [dim_of_symbol]) + 1.
   *)
  val abstract:
    'a Syntax.context ->
    how:[`Mixed | `PureGomoryChvatal] ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    ambient_dim:int ->
    'a Syntax.formula -> DD.closed DD.t

end = struct

  module FVI = FormulaVectorInterface

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
    projected

  let formula_of srk ~symbol_of_dim dd =
    FormulaVectorInterface.formula_of_dd srk ~symbol_of_dim dd

  let mixed_lattice_hull
        srk ~symbol_of_dim ?(term_of_dim=fun _ -> None) ~dim_of_symbol ~ambient_dim conjuncts =
    let module FVI = FormulaVectorInterface in
    let make_conjunct (p, l) =
      let p_phi = FVI.formula_of_polyhedron srk ~symbol_of_dim ~term_of_dim p in
      let l_phi = FVI.formula_of_lattice srk ~symbol_of_dim ~term_of_dim l
      in
      Syntax.mk_and srk [p_phi; l_phi]
    in
    let phi = Syntax.mk_and srk (List.map make_conjunct conjuncts) in
    let of_model =
      let abstract m (p, l) =
        let hull = local_mixed_lattice_hull m (p, l) in
        logf ~level:`debug "mixed_lattice_hull: Mixed hull is: @[%a@], ambient dimension %d@;"
          (P.pp Format.pp_print_int) hull ambient_dim;
        P.dd_of ambient_dim hull
      in
      FVI.abstract_implicant srk ~symbol_of_dim ~dim_of_symbol ~abstract phi
    in
    let domain: ('a, DD.closed DD.t) Abstract.domain =
      {
        join = DD.join
      ; of_model
      ; formula_of = formula_of srk ~symbol_of_dim
      ; top = P.dd_of ambient_dim P.top
      ; bottom = P.dd_of ambient_dim P.bottom
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    logf ~level:`debug "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

  let abstract srk ~how ~symbol_of_dim ~dim_of_symbol ~ambient_dim phi =
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
          FVI.abstract_implicant srk ~symbol_of_dim ~dim_of_symbol
            ~abstract phi
      ; formula_of = formula_of srk ~symbol_of_dim
      ; top = P.dd_of ambient_dim P.top
      ; bottom = P.dd_of ambient_dim P.bottom
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

      Notes:
      - [P /\ L |= Int(elim)] is more general than [L |= Int(elim)]; we don't
        require that [elim] is in the lattice of integer constraints.

      - The procedure is unsound if this condition doesn't hold, i.e., when [elim]
        can possibly take on real values. This may be an implementation issue:
        we may switch to Loos-Weispfenning term selection when [elim] is not in
        [L], but when a ceiling is provided, the rounded lower bound cannot
        be used as the Loos-Weispfenning term; we have to use the original
        lower bound instead.

        TODO: write a [local_project_general] that dispatches to LW first
        if [elim] is not in [L]. Check if LW still works in this more general
        setting (the language includes Int() constraints), and whether it
        works whether [P /\ L] entails [Int(elim)] or not.
   *)
  val local_project:
    (int -> QQ.t) -> eliminate: int Array.t ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    P.t * L.t ->
    P.t * L.t * [`MinusInfinity | `PlusInfinity | `Term of V.t] Array.t

  val project:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) ->
    ?term_of_dim:(int -> 'a Syntax.arith_term option) ->
    dim_of_symbol:(Syntax.symbol -> int) ->
    eliminate: int list ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t * L.t

  (* TODO: Eliminating original variables may not be sound because they may be
     real-valued.
  val abstract:
    'a Syntax.context ->
    [`RoundLowerBound of ceiling | `NoRounding | `RoundStrictWhenVariablesIntegral] ->
    'a Syntax.formula -> ('a Syntax.arith_term) array ->
    DD.closed DD.t * L.t
   *)

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

  let local_project m ~eliminate
        round_lower_bound
        (p, l) =
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

  let formula_of ~symbol_of_dim ?(term_of_dim=fun _ -> None) srk (dd, l) =
    let open FormulaVectorInterface in
    let p_phi = formula_of_polyhedron srk ~symbol_of_dim ~term_of_dim (P.of_dd dd)
    in
    let l_phi = formula_of_lattice srk ~symbol_of_dim ~term_of_dim l
    in
    let fml = Syntax.mk_and srk [p_phi; l_phi] in
    logf ~level:`debug "project_cooper: blocking @[%a@]@;" (Syntax.Formula.pp srk) fml;
    fml

  let project srk ~symbol_of_dim ?(term_of_dim = fun _ -> None)
        ~dim_of_symbol ~eliminate round_lower_bound conjuncts =
    let module FVI = FormulaVectorInterface in
    let make_conjunct (p, l) =
      let p_phi = FVI.formula_of_polyhedron srk ~symbol_of_dim ~term_of_dim p in
      let l_phi = FVI.formula_of_lattice srk ~symbol_of_dim ~term_of_dim l
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
      ; of_model = FVI.abstract_implicant srk ~symbol_of_dim ~dim_of_symbol
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

  (*
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
      FVI.project_onto_terms srk terms variable_projection
    in
    let abstract m (p, l) =
      let (p', l', _) = abstract_terms m (p, l) in
      (P.dd_of ambient_dim p', l')
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
  *)

end

let local_mixed_lattice_hull = Hull.local_mixed_lattice_hull
let mixed_lattice_hull = Hull.mixed_lattice_hull
let abstract_lattice_hull = Hull.abstract
let local_project_cooper = CooperProjection.local_project
let project_cooper = CooperProjection.project

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
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t

  val hull_and_project_cooper:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    eliminate: int list ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t

  val hull_and_project:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    eliminate: int list -> (P.t * L.t) list -> DD.closed DD.t

  (** When projecting onto terms using variable elimination, one has to be
      careful about what variables get eliminated.

      - [`DefineTerms]: Abstract by first defining terms, i.e., by adding a new
        dimension and a term equality for each term, and then eliminating the
        original variables. When an original dimension corresponds to a variable
        that may take on real values, this procedure is UNSOUND (not just
        diverge), because Cooper projection is sound only when the variable to
        be eliminated takes on integer values.

      - [`RealQe]: First eliminate redundant variables to project onto those
        occurring in terms, and then project onto the terms themselves by real
        QE. This avoids the soundness problem in [`DefineTerms], but is itself
        UNSOUND if variables not occurring in [terms] may be real-valued,
        also because Cooper projection is limited to integer-valued variables.

      In both cases, [`NoRounding] is unsound when strict inequalities are
      present (even if all variables are integer-valued).
      When all variables are guaranteed to be integer-valued, use
      [`RoundStrictWhenVariablesIntegral] instead.

      In summary, the preconditions are:
      - For [`DefineTerms], all variables have to be integer-valued.
      - For [`RealQe], all variables not occurring in terms have to be
        integer-valued.
      - All variables that are integer-valued have to be asserted as integral
        via the lattice. (Mixed hull computation requires it explicitly, and
        Cooper projection requires care if they are implicit.)
   *)

  val abstract_by_local_hull_and_project_cooper:
    'a Syntax.context ->
    [`DefineTerms | `RealQe] ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    'a Syntax.formula -> ('a Syntax.arith_term) array -> DD.closed DD.t

  val abstract_by_local_hull_and_project:
    'a Syntax.context ->
    'a Syntax.formula -> ('a Syntax.arith_term) array -> DD.closed DD.t

  val abstract_by_local_project_and_hull:
    'a Syntax.context ->
    [`DefineTerms | `RealQe] ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
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
  let local_project_and_hull m ~eliminate round_lower_bound (p, l) =
    let eliminate = Array.of_list eliminate in
    let (projected_p, projected_l, _terms) =
      local_project_cooper m ~eliminate round_lower_bound
        (p, l) in
    local_mixed_lattice_hull m (projected_p, projected_l)

  (**
      F := (Ax + b >= 0 /\ Int(Cx + d) /\ Int(y)) |= local_hull(F)
      For all ex + f >= 0, if F |= ex + f >= 0, local_hull(F) |= ex + f >= 0.

      local_project_cooper(local_hull(F), Int(Cx + d), Int(y))
      |= exists y. local_hull(F) /\ Int(Cx + d) /\ Int(y).

      If F |= ez + f >= 0, then G |= ez + f >= 0 (and G is free of y).
      F |= ez + f >= 0 implies local_hull(F) |= ez + f >= 0.
      Since RHS is free of y,
      (exists y. local_hull(F)) |= ez + f >= 0,
      and
      (exists y. local_hull(F) /\ Int(Cx + d) /\ Int(y)) |= ez + f >= 0.
      So local_project_cooper(local_hull(F), Int(Cx + d), Int(y)) |= ez + f >= 0.
   *)
  let local_hull_and_project_cooper m ~eliminate round_lower_bound (p, l) =
    let hulled = local_mixed_lattice_hull m (p, l) in
    let eliminate = Array.of_list eliminate in
    let (projected, _, _) =
      local_project_cooper m ~eliminate round_lower_bound (hulled, l)
    in
    projected

  let local_hull_and_project m ~eliminate (p, l) =
    let hulled = local_mixed_lattice_hull m (p, l) in
    let projected = Polyhedron.local_project m eliminate hulled in
    projected

  let formula_of srk symbol_of_dim ?(term_of_dim=(fun _ -> None)) dd =
    let p_phi = FormulaVectorInterface.formula_of_polyhedron
                  srk ~symbol_of_dim ~term_of_dim (P.of_dd dd) in
    logf ~level:`debug "ProjectHull: blocking @[%a@]@;"
      (Syntax.Formula.pp srk) p_phi;
    p_phi

  let top ambient_dim = P.dd_of ambient_dim P.top
  let bottom ambient_dim = P.dd_of ambient_dim P.bottom

  let saturate
        srk ~symbol_of_dim ?(term_of_dim= fun _ -> None) ~dim_of_symbol
        ~eliminate round_lower_bound op conjuncts =
    let module FVI = FormulaVectorInterface in
    let make_conjunct (p, l) =
      let p_phi = FVI.formula_of_polyhedron srk ~symbol_of_dim ~term_of_dim p in
      let l_phi = FVI.formula_of_lattice srk ~symbol_of_dim ~term_of_dim l
      in
      Syntax.mk_and srk [p_phi; l_phi]
    in
    let phi = Syntax.mk_or srk
                (List.map make_conjunct conjuncts)
    in
    let ambient_dim = FVI.ambient_dim conjuncts ~except:eliminate in
    let abstract m (p, l) =
      op m ~eliminate round_lower_bound (p, l)
      |> P.dd_of ambient_dim
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

  let hull_and_project_cooper srk ~symbol_of_dim ~dim_of_symbol ~eliminate
        round_lower_bound =
    saturate srk ~symbol_of_dim ~dim_of_symbol ~eliminate round_lower_bound
      local_hull_and_project_cooper

  let hull_and_project srk ~symbol_of_dim ~dim_of_symbol ~eliminate =
    saturate srk ~symbol_of_dim ~dim_of_symbol ~eliminate None
      (fun m ~eliminate _ (p, l) -> local_hull_and_project m ~eliminate (p, l))

  let abstract_terms_by_define_then_project
        srk proj_alg round_lower_bound phi terms =
    let module FVI = FormulaVectorInterface in
    let ambient_dim = Array.length terms in
    logf ~level:`debug "abstract_terms: Terms are @[%a@], base is %d@;"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space (Syntax.ArithTerm.pp srk))
      (Array.to_list terms)
      (Array.length terms);
    let FVI.{ sym_of_dim; term_of_dim; dim_of_sym } =
      FVI.bindings_for_term_abstraction terms in

    Testing.print_symbol_dimension_bindings srk dim_of_sym phi ();

    let abstract_terms =
      let proj ~eliminate m (p, l) =
        proj_alg m ~eliminate round_lower_bound (p, l)
      in
      FVI.project_onto_terms srk terms proj
    in
    let abstract m (p, l) =
      let abstracted = abstract_terms m (p, l) in
      logf ~level:`debug "abstract_terms: Abstracted: @[%a@]@; ambient dimension = %d@;"
        (P.pp Format.pp_print_int) abstracted
        ambient_dim;
      let dd = P.dd_of ambient_dim abstracted in
      logf ~level:`debug "abstract_terms: abstracted DD: @[%a@]@;"
        (DD.pp Format.pp_print_int) dd;
      dd
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

  let abstract_terms_by_project_and_real_qe
        srk proj_alg round_lower_bound phi terms =
    let module FVI = FormulaVectorInterface in
    let ambient_dim = Array.length terms in
    let FVI.{ sym_of_dim; term_of_dim; dim_of_sym } =
      FVI.bindings_for_term_abstraction terms in

    Testing.print_symbol_dimension_bindings srk dim_of_sym phi ();

    let abstract m (p, l) =
      let (term_definitions, dimensions_in_terms) =
        FVI.term_definitions_and_dimensions_in_terms srk terms in
      let original_dimensions =
        FVI.collect_dimensions (p, l)
      in
      let eliminate = IntSet.diff original_dimensions dimensions_in_terms
                      |> IntSet.to_list in
      let projected = proj_alg m ~eliminate round_lower_bound (p, l) in
      let p' = P.meet projected (P.of_constraints (BatList.enum term_definitions)) in
      let () =
        if Log.level_leq !my_verbosity_level `debug then
          match Testing.model_satisfies srk sym_of_dim term_of_dim m (p, l) p'
          with
          | Some model_err ->
             let s = Format.asprintf "%s" model_err in
             logf "%s" s;
             failwith s
          | None -> ()
        else
          ()
      in
      logf ~level:`debug
        "abstract_terms_by_project_and_real_qe: Eliminating dimensions @[%a@] using real QE for @[%a@]@;"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space Format.pp_print_int)
        (IntSet.to_list dimensions_in_terms)
        (P.pp Format.pp_print_int) p';
      P.local_project m (IntSet.to_list dimensions_in_terms) p'
      |> P.dd_of ambient_dim
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

  let abstract_by_local_hull_and_project_cooper
        srk how round_lower_bound phi terms =
    match how with
    | `DefineTerms ->
       abstract_terms_by_define_then_project srk
         local_hull_and_project_cooper round_lower_bound phi terms
    | `RealQe ->
       abstract_terms_by_project_and_real_qe srk
         local_hull_and_project_cooper round_lower_bound phi terms

  let abstract_by_local_hull_and_project srk phi terms =
    abstract_terms_by_project_and_real_qe srk
      (fun m ~eliminate _ (p, l) -> local_hull_and_project m ~eliminate (p, l))
      None
      phi terms

  let abstract_by_local_project_and_hull srk how round_lower_bound phi terms =
    match how with
    | `DefineTerms ->
       abstract_terms_by_define_then_project srk
         local_project_and_hull round_lower_bound phi terms
    | `RealQe ->
       abstract_terms_by_project_and_real_qe srk
         local_project_and_hull round_lower_bound
         phi terms

end

(*
let local_project_and_hull m ~eliminate
      ?(round_lower_bound = CooperProjection.all_variables_are_integral_and_no_strict_ineqs) =
  ProjectHull.local_project_and_hull m ~eliminate ~round_lower_bound
 *)

let project_and_hull srk ~symbol_of_dim ~dim_of_symbol ~eliminate round_lower_bound =
  ProjectHull.project_and_hull srk ~symbol_of_dim ~dim_of_symbol ~eliminate
    round_lower_bound

let hull_and_project_cooper srk ~symbol_of_dim ~dim_of_symbol ~eliminate
      round_lower_bound =
  ProjectHull.hull_and_project_cooper srk ~symbol_of_dim ~dim_of_symbol
    ~eliminate round_lower_bound

let hull_and_project = ProjectHull.hull_and_project

let abstract_by_local_hull_and_project_cooper srk how =
  match how with
  | `DefineThenProject ->
     ProjectHull.abstract_by_local_hull_and_project_cooper srk `DefineTerms
  | `ProjectThenRealQe ->
     ProjectHull.abstract_by_local_hull_and_project_cooper srk `RealQe

let abstract_by_local_hull_and_project =
  ProjectHull.abstract_by_local_hull_and_project

let abstract_by_local_project_and_hull srk how =
  match how with
  | `DefineThenProject ->
     ProjectHull.abstract_by_local_project_and_hull srk `DefineTerms
  | `ProjectThenRealQe ->
     ProjectHull.abstract_by_local_project_and_hull srk `RealQe
