module V = Linear.QQVector
module P = Polyhedron
module L = IntLattice

module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

include Log.Make(struct let name = "srk.formulaVector" end)

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
  (* The elimination scheme for ITE only introduces a new symbol to replace an
       ITE term and flattens the condition into a disjunction;
       the result has exactly the same mod terms, but has no ITE, so the formula
       becomes linear.
   *)
  add_mod_term_dimensions srk initial_binding (Syntax.eliminate_ite srk phi)

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

let constraints_of_implicant srk linearize m atoms =
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
    | `Not phi ->
       begin match Syntax.Formula.destruct srk phi with
       | `Atom (`Arith (`Eq, t1, t2)) ->
          let (((pcond1, lcond1), v1), ((pcond2, lcond2), v2)) =
            (linearize t1, linearize t2) in
          if QQ.lt QQ.zero (Linear.evaluate_affine m (V.sub v1 v2)) then
            ( (`Pos, V.sub v1 v2) :: pcond1 @ pcond2 @ pcons
            , lcond1 @ lcond2 @ lcons )
          else
            ( (`Pos, V.sub v2 v1) :: pcond1 @ pcond2 @ pcons
            , lcond1 @ lcond2 @ lcons )
       | `Atom (`Arith (`Leq, t1, t2)) ->
          let (((pcond1, lcond1), v1), ((pcond2, lcond2), v2)) =
            (linearize t1, linearize t2) in
          ( (`Pos, V.sub v1 v2) :: pcond1 @ pcond2 @ pcons
          , lcond1 @ lcond2 @ lcons )
       | `Atom (`Arith (`Lt, t1, t2)) ->
          let (((pcond1, lcond1), v1), ((pcond2, lcond2), v2)) =
            (linearize t1, linearize t2) in
          ( (`Nonneg, V.sub v1 v2) :: pcond1 @ pcond2 @ pcons
          , lcond1 @ lcond2 @ lcons )
       | _ -> raise Linear.Nonlinear
       end
    | _ ->
       logf ~level:`debug "constraints_of_implicant: @[%a@]@;"
         (Syntax.Formula.pp srk) literal;
       assert false
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
       | Some atoms -> constraints_of_implicant srk linearize m atoms
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
