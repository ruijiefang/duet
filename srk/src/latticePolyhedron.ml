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

  (** Preconditions:
      - [symbol_of_dim] and [term_of_adjoined_dim] need to be consistent on
        the intersection of their domains, in that
        [mk_const (symbol_of_dim dim) = term_of_adjoined_dim dim] for all [dim]
        in the intersection of domains.
      - [symbol_of_dim (dim_of_symbol s) = s] for all symbols [s]
      - [free_dims_start] is any dimension larger than the dimensions
        that occur in:
        - The domain of [symbol_of_dim]; strictly, any dimension larger than the
          dimension of a symbol that can occur in a formula for
          conversion or abstraction, and larger than the dimension of a symbol
          that occurs in a term in the image of [term_of_adjoined_dim].
        - The domain of [term_of_adjoined_dim].
   *)
  val mk_binding:
    'a Syntax.context ->
    (int -> Syntax.symbol option) ->
    ?term_of_adjoined_dim: 'a Syntax.arith_term IntMap.t ->
    (Syntax.symbol -> int) ->
    free_dims_start: int -> 'a binding

  val add_mod_term_dimensions:
    'a Syntax.context -> 'a binding -> 'a Syntax.formula -> 'a binding

  (** Given [srk], [terms], and [phi],
      a standard binding places [terms] in the dimensions 0 through
      length(terms) (exclusive), followed by the image of symbols in [phi]
      under [Syntax.int_of_symbol], followed by additional dimensions for
      mod terms in [phi] (terms of the form [t % r] for constant rational r
      and term t); there is one for each such term.
   *)
  val mk_standard_binding:
    'a Syntax.context -> ?project_onto:'a Syntax.arith_term array ->
    'a Syntax.formula -> 'a binding

  val mod_term_dimensions: 'a binding -> int list

  val pp_symbol_to_dimension:
    'a Syntax.context -> Syntax.Symbol.Set.t -> Format.formatter -> 'a binding -> unit

  val formula_of_dd:
    'a Syntax.context -> 'a binding -> DD.closed DD.t -> 'a Syntax.formula

  val formula_of_polyhedron:
    'a Syntax.context -> 'a binding -> P.t -> 'a Syntax.formula

  val formula_of_lattice:
    'a Syntax.context -> 'a binding -> L.t -> 'a Syntax.formula

  val formula_of_point:
    'a Syntax.context -> 'a binding -> Linear.QQVector.t -> 'a Syntax.formula

  val ambient_dim: (P.t * L.t) list -> except:int list -> int

  val collect_dimensions_from_constraints:
    ('a -> V.t) -> 'a BatEnum.t -> IntSet.t

  val collect_dimensions: (P.t * L.t) -> IntSet.t

  (** Lift a local abstraction procedure for a polyhedron-lattice pair into an
      local abstraction procedure for a formula.
      All symbols in the formula must be in the domain of [dim_of_symbol]
      in [binding], and the space of dimensions in [binding] has to contain
      dimensions corresponding to mod terms in the formula.
   *)
  val abstract_implicant:
    'a Syntax.context -> 'a binding ->
    [ `ImplicantOnly of ((int -> Q.t) -> P.t * L.t -> 'b)
    | `WithTerms of
        term_defs: (P.constraint_kind * V.t) list -> dimensions_in_terms: IntSet.t ->
        (int -> QQ.t) -> (P.t * L.t) -> 'b
    ] ->
    'a Syntax.formula ->
    [> `LIRA of 'a Interpretation.interpretation ] -> 'b

  (*
  val extend_assignment_to_adjoined_dimensions:
    'a binding -> (int -> QQ.t) -> (int -> QQ.t)
   *)

  (*
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
   *)

  val check_point_in_p:
    'a Syntax.context ->
    ?level:Log.level -> 'a binding -> (int -> Q.t) -> P.t -> unit

end = struct

  (* [t mod b |-> (q, r)], where b > 0 and
     [t = qb + r /\ Int(q) /\ 0 <= r < b] for all valuations.
   *)
  type mod_term_map =
    ((V.t * QQ.t), (int * int)) BatMap.t

  type 'a binding =
    {
      (* Main components supporting conversion between syntax and dimensions *)
      symbol_of_dim: int -> Syntax.symbol option
    ; term_of_adjoined_dim: 'a Syntax.arith_term IntMap.t
    ; dim_of_symbol: Syntax.symbol -> int
    (* Components for mod-term conversion *)
    ; next_fresh_dim: int
    ; first_mod_term_dimension: int
    ; dims_of_mod_term: mod_term_map
    (* Data for initial [term_of_adjoined_dim] before extension with terms for
       mod-term conversion; supports projection onto terms
     *)
    ; dimensions_in_initial_terms: IntSet.t
    ; vector_of_initial_adjoined_dim: V.t IntMap.t
    }

  type 'a eval_linear =
    {
      eval_real: QQ.t -> 'a
    ; eval_symbol: Syntax.symbol -> 'a
    ; eval_add: ('a -> 'a -> 'a) * 'a
    ; eval_mul: ('a -> 'a -> 'a) * 'a
    ; eval_div: 'a -> 'a -> 'a
    ; eval_mod: 'a -> 'a -> 'a
    ; eval_floor: 'a -> 'a
    ; eval_neg: 'a -> 'a
    }

  let eval_linear_term srk eval_linear term =
    Syntax.ArithTerm.eval srk
      (function
       | `Real r -> eval_linear.eval_real r
       | `App (k, []) -> eval_linear.eval_symbol k
       | `Var (_, _) | `App (_, _) -> raise Linear.Nonlinear
       | `Add xs ->
          List.fold_left (fst eval_linear.eval_add) (snd eval_linear.eval_add) xs
       | `Mul xs ->
          List.fold_left (fst eval_linear.eval_mul) (snd eval_linear.eval_mul) xs
       | `Binop (`Div, v1, v2) -> eval_linear.eval_div v1 v2
       | `Binop (`Mod, v1, v2) -> eval_linear.eval_mod v1 v2
       | `Unop (`Floor, v) -> eval_linear.eval_floor v
       | `Unop (`Neg, v) -> V.negate v
       | `Ite (_, _, _) -> raise Linear.Nonlinear
       | `Select _ -> assert false
      )
      term

  let qq_of term =
    let (k, rest) = Linear.QQVector.pivot Linear.const_dim term in
    if Linear.QQVector.equal rest Linear.QQVector.zero then k
    else raise Linear.Nonlinear

  let nonzero_qq_of term =
    let qq = qq_of term in
    if QQ.equal qq QQ.zero then
      invalid_arg "linearize: division or mod by 0"
    else qq

  let multiply_vectors v1 v2 =
    V.fold (fun dim2 scalar2 outer_sop ->
        if dim2 = Linear.const_dim then
          V.scalar_mul scalar2 v1
          |> V.add outer_sop
        else
          V.fold (fun dim1 scalar1 inner_sop ->
              if dim1 = Linear.const_dim then
                V.add_term (QQ.mul scalar1 scalar2) dim2 inner_sop
              else
                raise Linear.Nonlinear
            )
            v1
            outer_sop
      )
      v2
      V.zero

  let pre_vector_of dim_of_symbol =
    {
      eval_real = (fun r -> Linear.const_linterm r)
    ; eval_symbol = (fun symbol -> V.of_term QQ.one (dim_of_symbol symbol))
    ; eval_add = (V.add, V.zero)
    ; eval_mul = (multiply_vectors, Linear.const_linterm QQ.one)
    ; eval_div =
        (fun v1 v2 ->
          let c = nonzero_qq_of v2 in
          V.scalar_mul (QQ.inverse c) v1)
    ; eval_mod = (fun _ _ -> failwith "not implemented")
    ; eval_floor =
        (fun v -> Linear.const_linterm (QQ.of_zz (QQ.floor (qq_of v))))
    ; eval_neg = (fun v -> V.negate v)
    }

  let normalize_mod v1 v2 =
    let r = nonzero_qq_of v2 in
    if QQ.equal r QQ.zero then
      invalid_arg "vector_of: mod by 0"
    else if QQ.lt r QQ.zero then
      (V.negate v1, QQ.negate r)
    else (v1, r)

  let vector_of dim_of_symbol mod_term_to_dims substitutions_used =
    let eval = pre_vector_of dim_of_symbol in
    { eval with
      eval_mod =
        (fun v1 v2 ->
          let (v1', r2) = normalize_mod v1 v2 in
          match BatMap.find_opt (v1', r2) mod_term_to_dims with
          | None -> invalid_arg "vector_of: binding incomplete to translate mod"
          | Some (_q_dim, r_dim) ->
             substitutions_used := (v1', r2) :: !substitutions_used;
             V.of_term QQ.one r_dim
        )
    }

  let define_quotient_remainder (a, b) mod_term_to_dims =
    (* a = bq + r /\ 0 <= r < b /\ Int(q) *)
    let (quotient_dim, remainder_dim) = BatMap.find (a, b) mod_term_to_dims in
    let defining_equality =
      let v =
        V.of_list [(QQ.negate b, quotient_dim); (QQ.of_int (-1), remainder_dim)]
        |> V.add a
      in
      (`Zero, v)
    in
    ( [ defining_equality
      ; (`Nonneg, V.of_term QQ.one remainder_dim)
      ; (`Pos, V.of_list [(b, Linear.const_dim); (QQ.of_int (-1), remainder_dim)] )
      ]
    , [ V.of_term QQ.one quotient_dim ]
    )

  (** [linearize_term srk binding term = v]
      where [v] is a vector representing [term], such that in all interpretations
      [interp],
      [evaluate term interp = evaluate_affine v (valuation_of binding interp)].
   *)
  let linearize_term srk dim_of_symbol mod_term_to_dims term =
    let substitutions_used = ref [] in
    let linterm =
      eval_linear_term srk
        (vector_of dim_of_symbol mod_term_to_dims substitutions_used) term in
    let lincond =
      List.fold_left (fun (pcons, lcons) (a, b) ->
          let (pcons', lcons') =
            define_quotient_remainder (a, b) mod_term_to_dims
          in
          (pcons' @ pcons, lcons' @ lcons)
        )
        ([], []) !substitutions_used
    in
    (lincond, linterm)

  let get_term_dimensions dim_of_symbol term_of_adjoined_dim =
    IntMap.fold
      (fun _dim term dims ->
        Syntax.Symbol.Set.fold
          (fun symbol dimensions ->
            IntSet.add (dim_of_symbol symbol) dimensions
          )
          (Syntax.symbols term)
          dims
      )
      term_of_adjoined_dim
      IntSet.empty

  let mk_binding srk
        symbol_of_dim ?(term_of_adjoined_dim=IntMap.empty) dim_of_symbol
        ~free_dims_start =
    let dims_of_mod_term = BatMap.empty in
    let vectors_of_terms =
      IntMap.fold
        (fun dim term map ->
          let (_, v) = linearize_term srk dim_of_symbol dims_of_mod_term term in
          IntMap.add dim v map
        )
        term_of_adjoined_dim
        IntMap.empty
    in
    let next_fresh_dim =
      (* Dimensions for quotient and remainder are even and odd respectively *)
      if free_dims_start mod 2 = 0 then free_dims_start else free_dims_start + 1
    in
    {
      symbol_of_dim
    ; term_of_adjoined_dim
    ; dim_of_symbol
    ; next_fresh_dim
    ; first_mod_term_dimension = next_fresh_dim
    ; dims_of_mod_term
    ; dimensions_in_initial_terms =
        get_term_dimensions dim_of_symbol term_of_adjoined_dim
    ; vector_of_initial_adjoined_dim = vectors_of_terms
    }

  let mod_term_dimensions binding =
    BatEnum.(binding.first_mod_term_dimension --^ binding.next_fresh_dim)
    |> BatList.of_enum

  let term_of_dimension_opt srk binding dim =
    let symbol_of_dim = binding.symbol_of_dim in
    let term_of_adjoined_dim = binding.term_of_adjoined_dim in
    if dim = Linear.const_dim then Some (Syntax.mk_real srk QQ.one)
    else
      match symbol_of_dim dim with
      | Some s -> Some (Syntax.mk_const srk s)
      | None -> IntMap.find_opt dim term_of_adjoined_dim

  let term_of_dimension srk binding dim =
    match term_of_dimension_opt srk binding dim with
    | Some term -> term
    | None ->
       failwith
         (Format.sprintf
            "cannot translate dimension %d to a symbol or term" dim)

  let term_of_vector srk binding v =
    Linear.term_of_vec srk (term_of_dimension srk binding) v

  (** Preconditions:
      - (v, r) is not in the domain of [mod_term_to_dims], [symbol_of_dim] and
        [term_of_adjoined_dim] in [binding]
      - r > 0
      - All dimensions in [v] are in the union of domains of [symbol_of_dim]
        and [term_of_adjoined_dim] in [binding]
   *)
  let add_quotient_remainder_dimensions srk (v, r) binding =
    let quotient = binding.next_fresh_dim in
    let remainder = binding.next_fresh_dim + 1 in
    let term_of_adjoined_dim =
      let open Syntax in
      let term = term_of_vector srk binding v in
      let modulus = mk_real srk r in
      let mod_term = mk_mod srk term modulus in
      IntMap.add remainder mod_term binding.term_of_adjoined_dim
      |> IntMap.add quotient
           (* q = 1/b * (a - (a % b)) *)
           (mk_mul srk
              [mk_real srk (QQ.inverse r); mk_sub srk term mod_term])
    in
    { symbol_of_dim = binding.symbol_of_dim
    ; term_of_adjoined_dim = term_of_adjoined_dim
    ; dim_of_symbol = binding.dim_of_symbol
    ; next_fresh_dim = binding.next_fresh_dim + 2
    ; first_mod_term_dimension = binding.first_mod_term_dimension
    ; dims_of_mod_term =
        BatMap.add (v, r) (quotient, remainder) binding.dims_of_mod_term
    ; dimensions_in_initial_terms = binding.dimensions_in_initial_terms
    ; vector_of_initial_adjoined_dim = binding.vector_of_initial_adjoined_dim
    }

  let pp_symbol_to_dimension srk symbols fmt binding =
    let dim_of_symbol = binding.dim_of_symbol in
    Syntax.Symbol.Set.iter
      (fun symbol ->
        Format.fprintf fmt "binding @[%a@]:@[%a@] to %d@;"
          (Syntax.pp_symbol srk) symbol
          Syntax.pp_typ (Syntax.typ_symbol srk symbol)
          (dim_of_symbol symbol)
      )
      symbols

  let assign_mod_term srk binding =
    let eval = pre_vector_of !binding.dim_of_symbol in
    { eval with
      eval_mod =
        (fun v1 v2 ->
          let (v1', r2) = normalize_mod v1 v2 in
          match BatMap.find_opt (v1', r2) (!binding).dims_of_mod_term with
          | None ->
             binding := add_quotient_remainder_dimensions srk (v1', r2) !binding;
             let (_, remainder_dim) =
               BatMap.find (v1', r2) (!binding).dims_of_mod_term in
             V.of_term QQ.one remainder_dim
          | Some (_q_dim, r_dim) ->
             V.of_term QQ.one r_dim
        )
    }

  let assign_quotient_remainder_dims_in_term srk binding term =
    eval_linear_term srk (assign_mod_term srk binding) term

  (** Given a [binding] for [phi] (i.e., one whose [dim_of_symbol] has
      all symbols of [phi] in its domain),
      [add_mod_term_dimensions binding phi = binding']
      where [binding'] is [binding] extended with dimensions for mod terms
      in [phi].
   *)
  let add_mod_term_dimensions srk binding phi =
    let binding_ref = ref binding in
    Syntax.Formula.eval srk
      (function
       | `Tru | `Fls | `And _ | `Or _ | `Not _ -> ()
       | `Quantify (_, _, _, _) -> ()
       | `Atom (`Arith (_, t1, t2)) ->
          ignore (assign_quotient_remainder_dims_in_term srk binding_ref t1);
          ignore (assign_quotient_remainder_dims_in_term srk binding_ref t2)
       | `Atom (`IsInt t) ->
          ignore (assign_quotient_remainder_dims_in_term srk binding_ref t)
       | `Atom (`ArrEq (_, _)) -> ()
       | `Proposition _ -> ()
       | `Ite (_, _, _) -> ()
      )
      phi;
    !binding_ref

  let mk_standard_binding srk ?(project_onto = Array.of_list []) phi =
    let base = Array.length project_onto in
    let dim_of_symbol sym = base + (Syntax.int_of_symbol sym) in
    let max_assigned_dim =
      base + (Syntax.int_of_symbol (Syntax.Symbol.Set.max_elt (Syntax.symbols phi)))
    in
    let symbol_of_dim dim =
      if base <= dim && dim <= max_assigned_dim then
        Some (Syntax.symbol_of_int (dim - base))
      else None
    in
    let term_of_adjoined_dim =
      let open BatEnum in
      (0 --^ base)
      |> fold (fun map dim -> IntMap.add dim project_onto.(dim) map) IntMap.empty
    in
    let initial_binding =
      mk_binding srk symbol_of_dim ~term_of_adjoined_dim dim_of_symbol
        ~free_dims_start:(max_assigned_dim + 1)
    in
    add_mod_term_dimensions srk initial_binding phi

  let to_inequality srk binding (ckind, v) =
    let zero = Syntax.mk_zero srk in
    let op = match ckind with
      | `Zero -> Syntax.mk_eq srk zero
      | `Nonneg -> Syntax.mk_leq srk zero
      | `Pos -> Syntax.mk_lt srk zero
    in
    let term = term_of_vector srk binding v in
    op term

  let to_is_int srk binding v =
    Syntax.mk_is_int srk (term_of_vector srk binding v)

  let formula_of_p_constraints srk binding enum_constraints p =
    BatEnum.fold
      (fun l (ckind, v) ->
        to_inequality srk binding (ckind, v) :: l)
      []
      (enum_constraints p)
    |> Syntax.mk_and srk

  let formula_of_polyhedron srk binding p =
    formula_of_p_constraints srk binding P.enum_constraints p

  let formula_of_dd srk binding dd =
    formula_of_p_constraints srk binding DD.enum_constraints dd

  let formula_of_lattice srk binding l =
    List.fold_left (fun fml v -> to_is_int srk binding v :: fml) []
      (L.basis l)
    |> Syntax.mk_and srk

  let formula_of_point srk binding v =
    let symbol_of_dim = binding.symbol_of_dim in
    let term_of_adjoined_dim = binding.term_of_adjoined_dim in
    let conjuncts =
      V.fold
        (fun dim scalar conjuncts ->
          let r = Syntax.mk_real srk scalar in
          let s = match symbol_of_dim dim with
            | Some s -> Syntax.mk_const srk s
            | None -> begin match IntMap.find_opt dim term_of_adjoined_dim with
                      | Some term -> term
                      | None -> assert false
                      end
          in
          Syntax.mk_eq srk s r :: conjuncts)
        v []
    in
    Syntax.mk_and srk conjuncts

  let formula_of_model srk binding dimensions m =
    let v = IntSet.fold (fun dim v -> V.add_term (m dim) dim v) dimensions V.zero
    in
    formula_of_point srk binding v

  let constraints_of_implicant srk linearize atoms =
    let collect (pcons, lcons) literal =
      match Syntax.Formula.destruct srk literal with
      | `Atom (`Arith (sign, t1, t2)) ->
         let (((pcond1, lcond1), v1), ((pcond2, lcond2), v2)) =
           (linearize t1, linearize t2) in
         let v = V.sub v2 v1 in
         let cnstr = match sign with
           | `Eq -> (`Zero, v)
           | `Leq -> (`Nonneg, v)
           | `Lt -> (`Pos, v) in
         (cnstr :: pcond1 @ pcond2 @ pcons, lcond1 @ lcond2 @ lcons)
      | `Atom (`IsInt t) ->
         let ((pcond, lcond), linterm) = linearize t in
         (pcond @ pcons, linterm :: lcond @ lcons)
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

  let mk_assignment binding interp dim =
    let symbol_of_dim = binding.symbol_of_dim in
    let term_of_adjoined_dim = binding.term_of_adjoined_dim in
    if dim = Linear.const_dim then QQ.one
    else
      match symbol_of_dim dim, IntMap.find_opt dim term_of_adjoined_dim with
      | None, None ->
         failwith
           (Format.sprintf "Cannot translate dimension %d to a symbol for evaluation" dim)
      | Some s, _ -> Interpretation.real interp s
      | _, Some t ->
         Interpretation.evaluate_term interp t

  let definition_to_constraint (dim, v) : P.constraint_kind * V.t =
    (`Zero, V.add_term (QQ.of_int (-1)) dim v)

  let constraints_defining_terms binding =
    IntMap.fold (fun dim v l ->
        definition_to_constraint (dim, v) :: l)
      binding.vector_of_initial_adjoined_dim
      []
        
  let abstract_implicant
        srk binding
        (abstract:
           [ `ImplicantOnly of (int -> QQ.t) -> (P.t * L.t) -> 'a
           | `WithTerms of
               term_defs: (P.constraint_kind * V.t) list ->
               dimensions_in_terms: IntSet.t ->
               (int -> QQ.t) -> (P.t * L.t) -> 'a])
          phi model =
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
       let linearize term =
         linearize_term srk binding.dim_of_symbol binding.dims_of_mod_term term
       in
       let (atom_pcons, atom_lcons) =
         match implicant with
         | None -> assert false
         | Some atoms -> constraints_of_implicant srk linearize atoms
       in
       let (p, l) =
         ( P.of_constraints (BatList.enum atom_pcons)
         , L.hermitize atom_lcons )
       in
       begin match abstract with
       | `ImplicantOnly alpha -> alpha m (p, l)
       | `WithTerms alpha ->
          let term_defs = constraints_defining_terms binding in
          alpha ~term_defs ~dimensions_in_terms:binding.dimensions_in_initial_terms
            m (p, l)
       end
    | _ -> assert false

  (*
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
   *)

  let check_point_in_p srk ?(level=`debug) binding m p =
    let dimensions = collect_dimensions (p, IntLattice.bottom) in
    if (debug ~level (Polyhedron.mem m) true) p then
      ()
    else
      let alpha = formula_of_polyhedron srk binding p in
      let mphi = formula_of_model srk binding dimensions m in
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
  val mixed_lattice_hull: 'a Syntax.context ->
    'a FormulaVectorInterface.binding -> ambient_dim: int ->
    (P.t * L.t) list -> DD.closed DD.t

  val partition_vertices_by_integrality:
    DD.closed DD.t -> L.t -> (V.t list * V.t list)

  (** `PureGomoryChvatal is guaranteed to work only when all variables are
      implied to be integer-valued, but this is not checked.
      Ambient dimension should be at least as large as the maximum dimension
      occurring in the formula (computed via [dim_of_symbol]) + 1.
   *)
  val abstract: 'a Syntax.context -> 'a FormulaVectorInterface.binding ->
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
              (FVI.formula_of_lattice srk binding l);
            List.iter
              (fun v ->
                logf ~level:`debug
                  "Vertex @[%a@] is not in the lattice"
                  (Syntax.Formula.pp srk) (FVI.formula_of_point srk binding v)
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
    let module FVI = FormulaVectorInterface in
    let make_conjunct (p, l) =
      let p_phi = FVI.formula_of_polyhedron srk binding p in
      let l_phi = FVI.formula_of_lattice srk binding l
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
      FVI.abstract_implicant srk binding (`ImplicantOnly abstract) phi
    in
    let domain: ('a, DD.closed DD.t) Abstract.domain =
      {
        join = DD.join
      ; of_model
      ; formula_of = (FVI.formula_of_dd srk binding)
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
      () (FVI.formula_of_dd srk binding hull);
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
          FVI.abstract_implicant srk binding (`ImplicantOnly abstract) phi
      ; formula_of = FVI.formula_of_dd srk binding
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
      () (FVI.formula_of_dd srk binding hull);
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
    'a Syntax.context -> 'a FormulaVectorInterface.binding -> eliminate: int list ->
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

  let formula_of srk binding (dd, l) =
    let module FVI = FormulaVectorInterface in
    let p_phi = FVI.formula_of_dd srk binding dd in
    let l_phi = FVI.formula_of_lattice srk binding l in
    let fml = Syntax.mk_and srk [p_phi; l_phi] in
    logf ~level:`debug "project_cooper: blocking @[%a@]@;" (Syntax.Formula.pp srk) fml;
    fml

  let project srk binding ~eliminate round_lower_bound conjuncts =
    let module FVI = FormulaVectorInterface in
    let make_conjunct (p, l) =
      let p_phi = FVI.formula_of_polyhedron srk binding p in
      let l_phi = FVI.formula_of_lattice srk binding l
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
      ; of_model =
          FVI.abstract_implicant srk binding (`ImplicantOnly abstract) phi
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
    'a FormulaVectorInterface.binding -> eliminate: int list ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t

  val hull_and_project_cooper: 'a Syntax.context ->
    'a FormulaVectorInterface.binding -> eliminate: int list ->
    [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
    (P.t * L.t) list ->
    DD.closed DD.t

  val hull_and_project_real: 'a Syntax.context ->
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
    let p_phi = FVI.formula_of_polyhedron srk binding (P.of_dd dd) in
    logf ~level:`debug "ProjectHull: blocking @[%a@]@;"
      (Syntax.Formula.pp srk) p_phi;
    p_phi

  let top ambient_dim = P.dd_of ambient_dim P.top
  let bottom ambient_dim = P.dd_of ambient_dim P.bottom

  let saturate srk binding ambient_dim op conjuncts =
    let make_conjunct (p, l) =
      let p_phi = FVI.formula_of_polyhedron srk binding p in
      let l_phi = FVI.formula_of_lattice srk binding l
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
      ; of_model = FVI.abstract_implicant srk binding
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
    let ambient_dim = FVI.ambient_dim conjuncts ~except:eliminate in
    let op m (p, l) = local_project_cooper_and_hull m ~eliminate round_lower_bound (p, l) in
    saturate srk binding ambient_dim op conjuncts

  let hull_and_project_cooper srk binding ~eliminate round_lower_bound conjuncts =
    let ambient_dim = FVI.ambient_dim conjuncts ~except:eliminate in
    let op m (p, l) = local_hull_and_project_cooper m ~eliminate round_lower_bound (p, l) in
    saturate srk binding ambient_dim op conjuncts

  let hull_and_project_real srk binding ~eliminate conjuncts =
    let ambient_dim = FVI.ambient_dim conjuncts ~except:eliminate in
    let op m (p, l) = local_hull_and_project_real m ~eliminate (p, l) in
    saturate srk binding ambient_dim op conjuncts

  let abstract_terms_by_one_phase_elim srk proj_alg phi terms =
    let ambient_dim = Array.length terms in
    logf ~level:`debug "abstract_terms_by_one_phase_elim: Terms are @[%a@], base is %d@;"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space (Syntax.ArithTerm.pp srk))
      (Array.to_list terms)
      (Array.length terms);
    let binding = FVI.mk_standard_binding srk ~project_onto:terms phi in
    logf ~level:`debug "Symbol to dimensions: @[%a@]"
      (FVI.pp_symbol_to_dimension srk (Syntax.symbols phi)) binding;
    let abstract ~term_defs ~dimensions_in_terms m (p, l) =
      let eliminate = FVI.collect_dimensions (p, l)
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
      ; of_model = FVI.abstract_implicant srk binding (`WithTerms abstract) phi
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
    let module FVI = FormulaVectorInterface in
    let ambient_dim = Array.length terms in
    let binding = FVI.mk_standard_binding srk ~project_onto:terms phi in

    logf ~level:`debug "Symbol to dimensions: @[%a@]"
      (FVI.pp_symbol_to_dimension srk (Syntax.symbols phi)) binding;

    let abstract ~term_defs ~dimensions_in_terms m (p, l) =
      let original_dimensions = FVI.collect_dimensions (p, l) in
      let eliminate = IntSet.diff original_dimensions dimensions_in_terms
                      |> IntSet.to_list in
      let projected = proj_alg m ~eliminate (p, l) in
      let p' = P.meet projected (P.of_constraints (BatList.enum term_defs))
      in
      let () = FVI.check_point_in_p srk ~level:`debug binding m p' in
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
      ; of_model = FVI.abstract_implicant srk binding (`WithTerms abstract) phi
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

module FVI = FormulaVectorInterface
    
type 'a binding = 'a FVI.binding

let mk_binding = FVI.mk_binding
let mk_standard_binding = FVI.mk_standard_binding
let add_mod_term_dimensions = FVI.add_mod_term_dimensions
let mod_term_dimensions = FVI.mod_term_dimensions
let abstract_implicant = FVI.abstract_implicant

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

let _formula_of_point = FVI.formula_of_point
