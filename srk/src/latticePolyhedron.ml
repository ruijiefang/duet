module V = Linear.QQVector
module P = Polyhedron
module L = IntLattice
module T = Linear.MakeLinearMap(QQ)(Int)(V)(V)

include Log.Make(struct let name = "srk.latticePolyhedron" end)

let remap_vector move_constant f v =
  BatEnum.fold (fun v (coeff, dim) ->
      if dim <> Linear.const_dim || (dim = Linear.const_dim && move_constant) then
        Linear.QQVector.add_term coeff (f dim) v
      else v
    )
    Linear.QQVector.zero
    (Linear.QQVector.enum v)

module FixedPoint : sig

  (* TODO: Generalize [of_linterm] etc. to not assume standard
     symbol-dimension binding; then remove translation here. *)

  val to_inequality:
    'a Syntax.context -> symbol_of_dim:(int -> Syntax.symbol option) ->
    [< `Nonneg | `Pos | `Zero ] * V.t -> 'a Syntax.formula

  val make_conjunct:
    'a Syntax.context -> symbol_of_dim:(int -> Syntax.symbol option) ->
    P.t * L.t -> 'a Syntax.formula

  val constraints_of_implicant:
    'a Syntax.context -> dim_of_symbol:(Syntax.symbol -> int) ->
    'a Syntax.formula list -> ([> `Nonneg | `Pos | `Zero ] * V.t) list * V.t list

  val collect_dimensions:
    ('a -> Linear.QQVector.t) -> 'a BatEnum.t -> SrkUtil.Int.Set.t
    
  val ambient_dim: (P.t * L.t) list -> except:int list -> int

  val define_terms:
    'a Syntax.context -> 'a Syntax.arith_term Array.t ->
    (Polyhedron.constraint_kind * Linear.QQVector.t) list

  val extract_implicant_and_abstract:
    'a Syntax.context -> 'a Syntax.formula ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    abstract: ((int -> Q.t) -> P.t * L.t -> 'b) ->
    [> `LIRA of 'a Interpretation.interpretation ] -> 'b

end = struct

  module IntSet = SrkUtil.Int.Set

  let to_inequality srk ~symbol_of_dim (ckind, v) =
    let zero = Syntax.mk_zero srk in
    let op = match ckind with
      | `Zero -> Syntax.mk_eq srk zero
      | `Nonneg -> Syntax.mk_leq srk zero
      | `Pos -> Syntax.mk_lt srk zero
    in
    let f x =
      if x = Linear.const_dim then Linear.const_dim
      else
        match symbol_of_dim x with
        | None ->
           failwith (Format.sprintf "cannot translate dimension %d to a symbol" x)
        | Some s ->
           Syntax.int_of_symbol s
    in
    let v' = remap_vector true f v in
    op (Linear.of_linterm srk v')

  let constraints_of_implicant srk ~dim_of_symbol atoms =
    let dim_of_sym x = dim_of_symbol (Syntax.symbol_of_int x) in
    let collect (pcons, lcons) literal =
      match Syntax.Formula.destruct srk literal with
      | `Atom (`Arith (sign, t1, t2)) ->
         let (v1, v2) =
           ( Linear.linterm_of srk t1 |> remap_vector true dim_of_sym
           , Linear.linterm_of srk t2 |> remap_vector true dim_of_sym )
         in
         let v = Linear.QQVector.sub v2 v1 in
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

  let collect_dimensions to_vector cnstrs =
    BatEnum.fold
      (fun dims cnstr ->
        let v = to_vector cnstr in
        Linear.QQVector.fold
          (fun dim _coeff dims ->
            if dim <> Linear.const_dim then IntSet.add dim dims
            else dims
          )
          v dims)
      IntSet.empty
      cnstrs

  let ambient_dim conjuncts ~except =
    let except = IntSet.of_list except in
    List.fold_left (fun curr_max (p, l) ->
        let p_dims =
          collect_dimensions (fun (_, v) -> v) (Polyhedron.enum_constraints p)
        in
        let l_dims =
          collect_dimensions (fun x -> x) (BatList.enum (IntLattice.basis l)) in
        let dims = IntSet.diff (IntSet.union p_dims l_dims) except in
        let curr = IntSet.max_elt dims + 1 in
        Int.max curr curr_max)
      0
      conjuncts

  let define_terms srk terms =
    let base = Array.length terms in
    Array.fold_left
      (fun (vs, idx) term ->
        let v = Linear.linterm_of srk term
                |> remap_vector true (fun dim -> base + dim) in
        ((`Zero, Linear.QQVector.add_term (QQ.of_int (-1)) idx v) :: vs, idx + 1)
      )
      ([], 0) terms
    |> fst

  let extract_implicant_and_abstract
        srk phi ~symbol_of_dim ~dim_of_symbol ~abstract model =
    match model with
    | `LIRA interp ->
       let m dim =
         if dim = Linear.const_dim then QQ.one
         else
           match symbol_of_dim dim with
           | None ->
              failwith
                (Format.sprintf "Cannot translate dimension %d to a symbol for evaluation" dim)
           | Some s -> Interpretation.real interp s
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

  module IntMap = SrkUtil.Int.Map
  module IntSet = SrkUtil.Int.Set

  let recession_extension var_to_ray_var p =
    (* ax <= b, a'x < b' -->
       ax <= b, ax' < b', ar <= 0, a(x-r) <= b, a'(x - r) < b'
     *)
    let system = Polyhedron.enum_constraints p in
    BatEnum.iter (fun (ckind, v) ->
        let recession_ineq = match ckind with
          | `Pos -> `Nonneg
          | _ -> ckind in
        let ray_constraint = remap_vector false var_to_ray_var v in
        let subspace_point_constraint = Linear.QQVector.sub v ray_constraint in
        BatEnum.push system (recession_ineq, ray_constraint);
        BatEnum.push system (ckind, subspace_point_constraint))
      (Polyhedron.enum_constraints p);
    Polyhedron.of_constraints system

  let subspace_restriction var_to_ray_var l m =
    (* Int(cx + d) --> c (x - r) = c x0 *)
    let constraints = BatEnum.empty () in
    BatList.iter
      (fun v ->
        let (_, x) = Linear.QQVector.pivot Linear.const_dim v in
        let lhs =
          Linear.QQVector.sub x (remap_vector false var_to_ray_var x)
        in
        let rhs = Linear.QQVector.fold (fun dim coeff sum ->
                      if dim <> Linear.const_dim then
                        QQ.add (QQ.mul coeff (m dim)) sum
                      else sum)
                    x
                    QQ.zero in
        let subspace_constraint =
          Linear.QQVector.add_term (QQ.negate rhs) Linear.const_dim lhs
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
    Log.logf ~level:`debug "local_mixed_lattice_hull, before projection: @[%a@]@;"
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
    Log.logf ~level:`debug "after projection: @[%a@]@;"
      (Polyhedron.pp Format.pp_print_int) projected;
    projected

  let formula_of srk ~symbol_of_dim dd =
    BatEnum.fold
      (fun l (ckind, v) -> FixedPoint.to_inequality srk ~symbol_of_dim (ckind, v) :: l)
      []
      (DD.enum_constraints dd)
    |> Syntax.mk_and srk    

  let mixed_lattice_hull srk ~symbol_of_dim ~dim_of_symbol conjuncts =
    let open FixedPoint in
    let phi = Syntax.mk_or srk (List.map (make_conjunct srk ~symbol_of_dim) conjuncts) in
    let ambient_dim = ambient_dim conjuncts ~except:[] in
    let of_model =
      let abstract m (p, l) =
        local_mixed_lattice_hull m (p, l)
        |> Polyhedron.dd_of ambient_dim
      in
      FixedPoint.extract_implicant_and_abstract srk phi
        ~symbol_of_dim ~dim_of_symbol ~abstract
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
    Log.logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
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
          FixedPoint.extract_implicant_and_abstract
            srk phi ~symbol_of_dim ~dim_of_symbol
            ~abstract
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
    (int -> QQ.t) -> eliminate: int Array.t -> ?round_lower_bound: ceiling ->
    P.t * L.t ->
    P.t * L.t * [`MinusInfinity | `PlusInfinity | `Term of V.t] Array.t

  val project:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    eliminate: int list -> ?round_lower_bound: ceiling ->
    (P.t * L.t) list ->
    DD.closed DD.t * L.t

  val abstract:
    'a Syntax.context -> ?round_lower_bound: ceiling -> 'a Syntax.formula ->
    ('a Syntax.arith_term) array ->
    DD.closed DD.t * L.t

  (** Identity ceiling *)
  val all_variables_are_integral_and_no_strict_ineqs: ceiling

end = struct

  module IntSet = SrkUtil.Int.Set

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
                        let coeff = Linear.QQVector.coeff dim_to_elim v in
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
      let solution = Linear.QQVector.add_term delta Linear.const_dim rounded_term in
      let new_p = substitute_and_adjoin_ineqs solution inequalities in
      let new_l = substitute_and_adjoin_integral solution integrality in
      Log.logf ~level:`debug
        "local_project_one (1): Eliminating %d from polyhedron @[%a@] and lattice: @[%a@]@;"
        dim_to_elim
        (Polyhedron.pp Format.pp_print_int) polyhedron
        (IntLattice.pp Format.pp_print_int) lattice;
      Log.logf ~level:`debug
        "local_project_one (2): \
         m(var to elim) = @[%a@], \
         glb term before rounding: @[%a@], \
         rounded_value: @[%a@], \
         modulus: @[%a@], \
         delta: @[%a@], \
         rounded_term: @[%a@]@;"
        QQ.pp (m dim_to_elim)
        (Linear.QQVector.pp_term Format.pp_print_int) (lower_bound dim_to_elim glb_v)
        QQ.pp rounded_value
        QQ.pp modulus
        QQ.pp delta
        (Linear.QQVector.pp_term Format.pp_print_int) rounded_term;
      Log.logf ~level:`debug
        "local_project_one (3): new polyhedron: @[%a@], new lattice: @[%a@], term selected: @[%a@]@;"
        (Polyhedron.pp Format.pp_print_int) new_p
        (IntLattice.pp Format.pp_print_int) new_l
        (Linear.QQVector.pp_term Format.pp_print_int) solution;
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

  let local_project m ~eliminate
        ?(round_lower_bound=all_variables_are_integral_and_no_strict_ineqs)
        (polyhedron, lattice) =
    let (p, l, ts) =
      Array.fold_left
        (fun (p, l, ts) dim_to_elim ->
          let (p', l', t') = local_project_one m dim_to_elim ~round_lower_bound p l in
          Log.logf ~level:`debug
            "local_project_cooper: eliminated %d to get result: @[%a@]@;"
            dim_to_elim
            (Polyhedron.pp Format.pp_print_int) p';
          (p', l', t' :: ts)
        )
        (polyhedron, lattice, [])
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

  let formula_of ~symbol_of_dim srk (dd, l) =
    let pcons =
      BatEnum.fold
        (fun l (ckind, v) ->
          FixedPoint.to_inequality srk ~symbol_of_dim (ckind, v) :: l)
        []
        (DD.enum_constraints dd)
    in
    let lcons =
      List.fold_left (fun fml v ->
          Syntax.mk_is_int srk (Linear.of_linterm srk v) :: fml)
        []
        (IntLattice.basis l)
    in
    let fml = Syntax.mk_and srk (List.rev_append lcons pcons) in
    Log.logf "project_cooper: blocking @[%a@]@;" (Syntax.Formula.pp srk) fml;
    fml

  let project srk ~symbol_of_dim ~dim_of_symbol ~eliminate
        ?(round_lower_bound=all_variables_are_integral_and_no_strict_ineqs)
        conjuncts =
    let open FixedPoint in
    let phi = Syntax.mk_or srk (List.map (make_conjunct srk ~symbol_of_dim) conjuncts) in
    let ambient_dim = ambient_dim conjuncts ~except:eliminate in
    let eliminate = Array.of_list eliminate in
    let abstract m (p, l) =
      let (p', l', _) = local_project m ~eliminate ~round_lower_bound (p, l) in
      (Polyhedron.dd_of ambient_dim p', l')
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join
      ; of_model = FixedPoint.extract_implicant_and_abstract srk phi
                     ~symbol_of_dim ~dim_of_symbol ~abstract
      ; formula_of = formula_of srk ~symbol_of_dim
      ; top = top ambient_dim
      ; bottom = bottom ambient_dim
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    Log.logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

  let abstract srk
        ?(round_lower_bound=all_variables_are_integral_and_no_strict_ineqs)
        phi terms =
    let base = Array.length terms in
    let dim_of_symbol base sym = base + (Syntax.int_of_symbol sym) in
    let symbol_of_dim base dim =
      if dim >= base then
        Some (Syntax.symbol_of_int (dim - base))
      else None
    in
    let term_vectors = FixedPoint.define_terms srk terms in    
    let ambient_dim = Array.length terms in
    let abstract m (p, l) =
      let eliminate_p =
        (Polyhedron.enum_constraints p)
        |> FixedPoint.collect_dimensions (fun (_, v) -> v)
      in
      let eliminate_l =
        IntLattice.basis l |> BatList.enum
        |> FixedPoint.collect_dimensions (fun v -> v)
      in
      let eliminate = IntSet.union eliminate_p eliminate_l
                      |> IntSet.to_array in
      let p_with_terms = Polyhedron.of_constraints (BatList.enum term_vectors)
                         |> Polyhedron.meet p in
      let (p', l', _) = local_project m ~eliminate ~round_lower_bound
                          (p_with_terms, l) in
      (Polyhedron.dd_of ambient_dim p', l')
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join
      ; of_model =
          FixedPoint.extract_implicant_and_abstract
            srk phi ~symbol_of_dim:(symbol_of_dim base) ~dim_of_symbol:(dim_of_symbol base) ~abstract
      ; formula_of = formula_of srk ~symbol_of_dim:(symbol_of_dim base)
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

module ProjectHull : sig

  val project_and_hull:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    eliminate: int list -> round_lower_bound: ceiling ->
    (P.t * L.t) list ->
    DD.closed DD.t

  val hull_and_project:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    eliminate: int list -> round_lower_bound: ceiling ->
    (P.t * L.t) list ->
    DD.closed DD.t

end = struct

  let local_project_and_hull m ~eliminate ~round_lower_bound (p, l) =
    let eliminate = Array.of_list eliminate in
    let (projected_p, projected_l, _terms) =
      local_project_cooper m ~eliminate ~round_lower_bound
        (p, l) in
    local_mixed_lattice_hull m (projected_p, projected_l)

  let local_hull_and_project m ~eliminate ~round_lower_bound (p, l) =
    let hulled = local_mixed_lattice_hull m (p, l) in
    let eliminate = Array.of_list eliminate in
    let (projected, _, _) =
      local_project_cooper m ~eliminate ~round_lower_bound (hulled, l)
    in
    projected

  let formula_of srk symbol_of_dim dd =
    let pcons =
      BatEnum.fold
        (fun l (ckind, v) ->
          FixedPoint.to_inequality srk ~symbol_of_dim (ckind, v) :: l)
        []
        (DD.enum_constraints dd)
    in
    let fml = Syntax.mk_and srk pcons in
    Log.logf "project_and_hull: blocking @[%a@]@;" (Syntax.Formula.pp srk) fml;
    fml

  let top ambient_dim = Polyhedron.dd_of ambient_dim Polyhedron.top
  let bottom ambient_dim = Polyhedron.dd_of ambient_dim Polyhedron.bottom

  let saturate srk ~symbol_of_dim ~dim_of_symbol ~eliminate ~round_lower_bound
        op conjuncts =
    let open FixedPoint in
    let phi = Syntax.mk_or srk
                (List.map (make_conjunct srk ~symbol_of_dim) conjuncts)
    in
    let ambient_dim = ambient_dim conjuncts ~except:eliminate in
    let of_model model =
      match model with
      | `LIRA interp ->
         let m dim =
           if dim = Linear.const_dim then QQ.one
           else
             match symbol_of_dim dim with
             | None ->
                failwith (Format.sprintf "project_and_hull: Cannot translate dimension %d to a symbol" dim)
             | Some s -> Interpretation.real interp s
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
         let p' = op m ~eliminate ~round_lower_bound (p, l)
         in
         Polyhedron.dd_of ambient_dim p'
      | _ -> assert false
    in
    let domain: ('a, 'b) Abstract.domain =
      {
        join = DD.join
      ; of_model
      ; formula_of = formula_of srk symbol_of_dim
      ; top = top ambient_dim
      ; bottom = bottom ambient_dim
      }
    in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    Log.logf "phi: @[%a@]@;" (Syntax.pp_smtlib2 srk) phi;
    ignore (Abstract.Solver.get_model solver);
    Abstract.Solver.abstract solver domain

  let project_and_hull srk ~symbol_of_dim ~dim_of_symbol ~eliminate
        ~round_lower_bound =
    saturate srk ~symbol_of_dim ~dim_of_symbol ~eliminate ~round_lower_bound
      local_project_and_hull

  let hull_and_project srk ~symbol_of_dim ~dim_of_symbol ~eliminate
        ~round_lower_bound =
    saturate srk ~symbol_of_dim ~dim_of_symbol ~eliminate ~round_lower_bound
      local_hull_and_project

end

(*
let local_project_and_hull m ~eliminate
      ?(round_lower_bound = CooperProjection.all_variables_are_integral_and_no_strict_ineqs) =
  ProjectHull.local_project_and_hull m ~eliminate ~round_lower_bound
 *)

let project_and_hull srk ~symbol_of_dim ~dim_of_symbol ~eliminate
      ?(round_lower_bound = CooperProjection.all_variables_are_integral_and_no_strict_ineqs) =
  ProjectHull.project_and_hull srk ~symbol_of_dim ~dim_of_symbol ~eliminate
    ~round_lower_bound

let hull_and_project srk ~symbol_of_dim ~dim_of_symbol ~eliminate
      ?(round_lower_bound = CooperProjection.all_variables_are_integral_and_no_strict_ineqs) =
  ProjectHull.hull_and_project srk ~symbol_of_dim ~dim_of_symbol ~eliminate
    ~round_lower_bound
