open Syntax
module P = Polyhedron
module L = IntLattice

module V = Linear.QQVector

include Log.Make (struct let name = "polyhedronLatticeTiling" end)

let () = my_verbosity_level := `info

module LocalAbstraction : sig

  type ('concept1, 'point1, 'concept2, 'point2) t =
    {
      abstract: 'point1 -> 'concept1 -> 'concept2 * ('point1 -> 'point2)
    }

  val apply:
    ('concept1, 'point1, 'concept2, 'point2) t -> 'point1 -> 'concept1 -> 'concept2

  val apply2:
    ('concept1, 'point1, 'concept2, 'point2) t -> 'point1 -> 'concept1 ->
    'concept2 * ('point1 -> 'point2)

  val compose:
    ('concept2, 'point2, 'concept3, 'point3) t ->
    ('concept1, 'point1, 'concept2, 'point2) t ->
    ('concept1, 'point1, 'concept3, 'point3) t

  val inject: ('point1 -> 'concept1 -> 'concept2 * ('point1 -> 'point2))
              -> ('concept1, 'point1, 'concept2, 'point2) t

end = struct

  (** A concept space consists of a universe of points and a set of
      concepts that defines a set of points in some way, e.g., logical satisfaction.

      Let C1, C2 be sets of concepts and P1, P2 be universes of points.
      A local abstraction consists of a function
      [abstract: P1 -> C1 -> C2 * (P1 -> P2)]
      such that whenever [p1] satisfies [c1],
      [abstract(p1, c1) = (c2, univ_translation)] only if
      - univ_translation(p1) satisfies c2
      - for all c2' in C2,
        if all points in univ_translation({x in P1: x satisfies c1}) satisfy c2',
        then all points in univ_translation({x in P2: x satisfies c2}) also
        satisfy c2'.
      This is a generalization of local abstractions where the universe
      translation is constant. This generalization allows local abstractions
      to "expand" the target universe/ambient space by introducing new dimensions
      depending on the concept being abstracted and the point within it,
      but all expansions agree on the intended target subspace and the intended
      universe translation.
   *)

  type ('concept1, 'point1, 'concept2, 'point2) t =
    {
      abstract: 'point1 -> 'concept1 -> 'concept2 * ('point1 -> 'point2)
    }

  let apply t x c = fst (t.abstract x c)

  let apply2 t x c = t.abstract x c

  let compose
        (t2: ('concept2, 'point2, 'concept3, 'point3) t)
        (t1: ('concept1, 'point1, 'concept2, 'point2) t) =
    let abstract x c =
      let (c2, translation12) = t1.abstract x c in
      let (c3, translation23) = t2.abstract (translation12 x) c2 in
      (c3, fun m -> translation23 (translation12 m))
    in
    { abstract }

  let inject f = { abstract = f }

end

module Abstraction = struct

  type ('concept1, 'point1, 'concept2, 'point2) t =
    {
      abstract: 'concept1 -> 'concept2 * ('point1 -> 'point2)
    }

  let apply t c = fst (t.abstract c)

end

module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

let term_of_vector srk term_of_dim v =
  let open Syntax in
  V.enum v
  |> BatEnum.fold
       (fun summands (coeff, dim) ->
         if dim <> Linear.const_dim then
           mk_mul srk [mk_real srk coeff; term_of_dim dim] :: summands
         else
           mk_real srk coeff :: summands)
       []
  |> mk_add srk

let formula_p srk term_of_dim (kind, v) =
  let t = term_of_vector srk term_of_dim v in
  match kind with
  | `Zero -> mk_eq srk t (mk_zero srk)
  | `Nonneg -> mk_leq srk (mk_zero srk) t
  | `Pos -> mk_lt srk (mk_zero srk) t

let formula_l srk term_of_dim v =
  let t = term_of_vector srk term_of_dim v in
  mk_is_int srk t

let formula_t srk term_of_dim v =
  let t = term_of_vector srk term_of_dim v in
  mk_not srk (mk_is_int srk t)

let formula_of_dd srk term_of_dim dd =
  DD.enum_constraints dd
  |> BatEnum.fold
       (fun atoms (kind, v) -> formula_p srk term_of_dim (kind, v) :: atoms) []
  |> List.rev
  |> mk_and srk

let collect_dimensions vector_of add_dim constraints =
  let dims = ref IntSet.empty in
  BatList.iter
    (fun constr ->
      V.enum (vector_of constr)
      |> BatEnum.iter
           (fun (_, dim) ->
             if dim <> Linear.const_dim && add_dim dim
             then dims := IntSet.add dim !dims
             else ())
    )
    constraints;
  !dims

let pp_dim fmt dim = Format.fprintf fmt "(dim %d)" dim

let pp_vector = V.pp_term pp_dim

let pp_pconstr fmt (kind, v) =
  match kind with
  | `Zero -> Format.fprintf fmt "@[%a@] = 0" pp_vector v
  | `Nonneg -> Format.fprintf fmt "@[%a@] >= 0" pp_vector v
  | `Pos -> Format.fprintf fmt "@[%a@] > 0" pp_vector v

let log_plt_constraints ~level str (p, l, t) =
  logf ~level
    "%s: p_constraints: @[%a@]@\n" str
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
       pp_pconstr) p;
  logf ~level
    "%s: l_constraints: @[%a@]@\n" str
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
       pp_vector) l;
  logf ~level
    "%s: t_constraints: @[%a@]@\n" str
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
       pp_vector) t

let test_level = ref `debug

let test_point_in_polyhedron str m p =
  if Log.level_leq !my_verbosity_level !test_level then
    List.iter
      (fun (kind, v) ->
        logf ~level:`debug "%s: testing @[%a@]" str pp_pconstr (kind, v);
        let result = Linear.evaluate_affine m v in
        match kind with
        | `Zero ->
           if not (QQ.equal result QQ.zero) then
             failwith
               (Format.asprintf "%s: evaluated vector to %a, expected 0"
                  str QQ.pp result)
           else ()
        | `Nonneg -> assert (QQ.leq QQ.zero result)
        | `Pos -> assert (QQ.lt QQ.zero result)
      )
      p
  else ()

let test_point_in_lattice is_int str m l =
  if Log.level_leq !my_verbosity_level !test_level then
    List.iter
      (fun v ->
        logf ~level:`debug "%s: testing %a(%a)"
          str
          (fun fmt is_int -> match is_int with
                             | `IsInt -> Format.fprintf fmt "Int"
                             | `NotInt -> Format.fprintf fmt "~Int")
          is_int
          Linear.QQVector.pp v;
        let result = Linear.evaluate_affine m v in
        match QQ.to_zz result, is_int with
        | Some _, `IsInt -> ()
        | None, `NotInt -> ()
        | None, `IsInt ->
           failwith
             (Format.asprintf "%s: evaluated vector to %a, expected an integer"
                str QQ.pp result)
        | Some _, `NotInt ->
           failwith
             (Format.asprintf "%s: evaluated vector to %a, expected a non-integer"
                str QQ.pp result)
      )
      l
  else ()

module Plt : sig

  type standard
  type intfrac =
    {
      start_of_term_int_frac: int
    ; start_of_symbol_int_frac: int
    }

  type 'layout t

  val int_frac_layout: num_terms:int -> intfrac

  val top: 'layout t

  val formula_of_plt:
    'a context -> (int -> 'a arith_term) -> 'layout t -> 'a formula

  val constrained_dimensions: 'layout t -> IntSet.t

  val ceiling_int_frac:
    (int -> QQ.t) -> V.t -> (V.t * (P.constraint_kind * V.t) list * V.t list)

  val abstract_to_standard_plt:
    [`ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, standard t, int -> Q.t)
      LocalAbstraction.t

  val abstract_to_intfrac_plt:
    [`ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, intfrac t, int -> Q.t)
      LocalAbstraction.t

  val poly_part: 'layout t -> P.t
  val lattice_part: 'layout t -> L.t
  val tiling_part: 'layout t -> L.t

  val mk_plt:
    poly_part:P.t -> lattice_part:L.t -> tiling_part:L.t -> 'layout t

  val abstract_poly_part:
    (P.t, int -> Q.t, P.t, int -> Q.t) LocalAbstraction.t ->
    ('layout t, int -> Q.t, 'layout t, int -> Q.t) LocalAbstraction.t

end = struct

  type standard = unit
  type intfrac =
    {
      start_of_term_int_frac: int
    ; start_of_symbol_int_frac: int
    }

  type 'layout t =
    {
      poly_part: P.t
    ; lattice_part: L.t
    ; tiling_part: L.t
    ; metadata: 'layout option
    }

  let poly_part plt = plt.poly_part
  let lattice_part plt = plt.lattice_part
  let tiling_part plt = plt.tiling_part
  let mk_plt ~poly_part ~lattice_part ~tiling_part =
    {
      poly_part
    ; lattice_part
    ; tiling_part
    ; metadata = None
    }

  let constrained_dimensions plt =
    let p = BatList.of_enum (P.enum_constraints plt.poly_part) in
    let l = L.basis plt.lattice_part in
    let t = L.basis plt.tiling_part in
    collect_dimensions (fun (_, v) -> v) (fun _ -> true) p
    |> IntSet.union (collect_dimensions (fun v -> v) (fun _ -> true) l)
    |> IntSet.union (collect_dimensions (fun v -> v) (fun _ -> true) t)

  let top =
    {
      poly_part = Polyhedron.top
    ; lattice_part = L.bottom
    ; tiling_part = L.bottom
    ; metadata = None
    }

  let real_of v =
    let (r, v') = V.pivot Linear.const_dim v in
    if V.is_zero v' then r
    else invalid_arg "not a constant"

  let mul_vec v1 v2 =
    try V.scalar_mul (real_of v1) v2
    with Invalid_argument _ ->
      begin
        try V.scalar_mul (real_of v2) v1
        with
          Invalid_argument _ ->
          raise Linear.Nonlinear
      end

  type lin_cond =
    {
      p_cond: (P.constraint_kind * V.t) list
    ; l_cond: V.t list
    ; t_cond: V.t list
    }

  let tru =
    {
      p_cond = []
    ; l_cond = []
    ; t_cond = []
    }

  let fls =
    {
      p_cond = [(`Zero, Linear.const_linterm QQ.one)]
    ; l_cond = []
    ; t_cond = []
    }

  let conjoin lin1 lin2 =
    {
      p_cond = List.rev_append lin1.p_cond lin2.p_cond
    ; l_cond = List.rev_append lin1.l_cond lin2.l_cond
    ; t_cond = List.rev_append lin1.t_cond lin2.t_cond
    }

  let lift_binop op (v1, ln1) (v2, ln2) =
    (op v1 v2, conjoin ln1 ln2)

  type term_vector =
    | TV_real of QQ.t
    | TV_mod of V.t * QQ.t
    | TV_floor of V.t

  let lin_mod ~vec_of_free_dim ~int_cond ~next_free_dim ~add_term_of_dim
        ~free_dim term_of_dim v1 v2 =
    let modulus =
      try real_of v2 with | Invalid_argument _ -> raise Linear.Nonlinear
    in
    let () =
      if QQ.equal modulus QQ.zero then invalid_arg "Division by zero"
      else ()
    in
    let quotient = vec_of_free_dim free_dim in
    logf ~level:`debug
      "lin_mod: introducing dimension %d for quotient in @[%a@] modulo %a"
      free_dim pp_vector v1 QQ.pp modulus;
    let remainder = V.sub v1 (V.scalar_mul modulus quotient) in
    let (intcond_p, intcond_l) = int_cond free_dim in
    let lincond =
      {
        p_cond = [(`Nonneg, remainder); (`Pos, V.sub v2 remainder)]
                 @ intcond_p
      ; l_cond = intcond_l
      ; t_cond = []
      }
    in
    ( remainder
    , lincond
    , next_free_dim free_dim
    , add_term_of_dim free_dim (TV_mod (v1, modulus)) term_of_dim
    )

  let lin_floor
        ~vec_of_free_dim ~int_cond ~next_free_dim ~add_term_of_dim
        ~free_dim term_of_dim v =
    let floored = vec_of_free_dim free_dim in
    logf ~level:`debug "introducing dimension %d for floor(%a)"
      free_dim pp_vector v;
    let lower_bound = V.sub v floored in
    let upper_bound =
      V.sub floored v |>
        V.add_term QQ.one Linear.const_dim in
    let (intcond_p, intcond_l) = int_cond free_dim in
    let lincond =
      {
        p_cond = [(`Nonneg, lower_bound); (`Pos, upper_bound)]
                 @ intcond_p
      ; l_cond = intcond_l
      ; t_cond = []
      }
    in
    ( floored
    , lincond
    , next_free_dim free_dim
    , add_term_of_dim free_dim (TV_floor v) term_of_dim
    )

  type expand_mod_floor =
    | NoExpansion
    | Expand_mod_floor_with of
        { free_dim: int
        ; new_dimensions: term_vector IntMap.t
        ; linearize_mod: free_dim:int -> term_vector IntMap.t ->
                         V.t -> V.t ->
                         (V.t * lin_cond * int * term_vector IntMap.t)
        ; linearize_floor: free_dim:int -> term_vector IntMap.t ->
                           V.t ->
                           (V.t * lin_cond * int * term_vector IntMap.t)
        }

  type expansion =
    {
      vec_of_symbol: Syntax.symbol -> V.t
    ; translate_int_atom: [`IsInt | `NotInt] -> (int -> QQ.t) -> V.t -> lin_cond
    ; expand_mod_floor: expand_mod_floor
    }

  let expand_univ_translation univ_translation new_dimensions initial =
    let extend m new_dimensions =
      let rec evaluate_dim dim =
        try
          begin match IntMap.find dim new_dimensions with
          | TV_real r -> r
          | TV_mod (v, r) ->
             QQ.idiv (Linear.evaluate_affine evaluate_dim v) r |> QQ.of_zz
          | TV_floor v ->
             QQ.floor (Linear.evaluate_affine evaluate_dim v) |> QQ.of_zz
          end
        with
        | Not_found -> m dim
      in
      evaluate_dim
    in
    let next = univ_translation initial in
    extend next new_dimensions

  let floor_int_frac m v =
    (*
       For integer dimensions:

       (Finite image)
       Let r(m) \in \Z be such that
       m |= p x_int = kq + r(m) for some integer k and 0 <= r(m) < q.

       1. (Abstraction)
          If m |= F[floor((p/q) x_int + t)], then
          m |= F[ (p/q) x_int - r(m)/q + floor(r(m)/q + t) ] /\ Int( (p/q) x_int - r(m)/q ).

       2. (Universality)
          F[ (p/q) x_int - r(m)/q + floor(r(m)/q + t) ] /\ Int( (p/q) x_int - r(m)/q )
          |= F[floor((p/q) x_int + t)].

          Int((p/q) x_int - r(m)/q) implies
          Int( (p/q) x_int - r(m)/q + floor(r(m)/q + t) ) implies
          (p/q) x_int - r(m)/q + floor(r(m)/q + t) = k for some k \in \Z.

          Want to show k = floor((p/q) x_int + t).
          (p/q) x_int + t = k + (r(m)/q + t) - floor(r(m)/q + t).
          So floor( (p/q) x_int + t ) = k + floor( (r(m)/q + t) - floor(r(m)/q + t) ).
          For all y \in \R, 0 <= y - floor(y) < 1, so the second summand is always 0,
          and the claim follows.

       For fractional dimensions:

       (Finite image)
       0 <= x_frac < 1 -->
       - t <= a x_frac + t < a + t. floor(t) <= floor(a x_frac + t) <= floor(a + t).
       - a + t < a x_frac + t <= t. floor(a + t) <= floor(a x_frac + t) <= floor(t).

       Let n \in \Z be such that m |= floor(a x_frac + t) = n.

       1. (Abstraction)
       If m |= F[floor(a x_frac + t)], then m |= F[n] /\ n <= a x_frac + t < n + 1.

       2. (Universality)
       F[n] /\ n <= a x_frac + t < n + 1 |= F[floor(a x_frac + t)].
     *)
    let (integer_part, fraction_from_integer_part, lconds) =
      V.fold
        (fun dim coeff (integer_part, fractional_part, lconds) ->
          if dim = Linear.const_dim then
            (integer_part, fractional_part, lconds)
          else if dim mod 2 = 1 then (integer_part, fractional_part, lconds)
          else
            let (p, q) = QQ.to_zzfrac coeff in
            let remainder =
              match QQ.to_zz (m dim) with
              | Some n -> ZZ.modulo (ZZ.mul p n) q
              | None ->
                 failwith
                   (Format.asprintf "dim %d should evaluate to an integer" dim)
            in
            let fraction = QQ.of_zzfrac remainder q in
            let integer_summand =
              V.of_term coeff dim
              |> V.add_term (QQ.negate fraction) Linear.const_dim in
            ( V.add integer_part integer_summand
            , QQ.add fractional_part fraction
            , integer_summand :: V.of_term QQ.one dim :: lconds
            )
        )
        v
        (V.zero, QQ.zero, [])
    in
    let within_unit_interval lower_bound term =
      [
        (`Nonneg, V.add_term (QQ.negate lower_bound) Linear.const_dim term)
      ; (`Pos, (Linear.const_linterm (QQ.add lower_bound QQ.one))
               |> V.add (V.negate term))
      ]
    in
    let (fraction_part, pconds) =
      let constant_within_floor =
        QQ.add fraction_from_integer_part (V.coeff Linear.const_dim v)
      in
      V.fold
        (fun dim coeff (sum, term, fractional_bounds) ->
          if dim = Linear.const_dim then (sum, term, fractional_bounds)
          else if dim mod 2 = 0 then (sum, term, fractional_bounds)
          else
            ( QQ.add (QQ.mul coeff (m dim)) sum
            , V.add_term coeff dim term
            , List.rev_append
                (within_unit_interval QQ.zero (V.of_term QQ.one dim))
                fractional_bounds
            )
        )
        v
        ( constant_within_floor
        , Linear.const_linterm constant_within_floor
        , []
        )
      |> (fun (sum, term, fractional_bounds) ->
        let lower_bound = QQ.floor sum |> QQ.of_zz in
        let pconds =
          List.rev_append
            (within_unit_interval lower_bound term)
            fractional_bounds
        in
        (lower_bound, pconds))
    in
    let result = V.add_term fraction_part Linear.const_dim integer_part in
    logf ~level:`debug
      "floor_int_frac: @[floor(%a) = %a@] is %b when @[%a@] and@\n @[%a@]@;"
      pp_vector v pp_vector result
      (QQ.equal (QQ.of_zz (QQ.floor (Linear.evaluate_affine m v))) (Linear.evaluate_affine m result))
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_pconstr)
      pconds
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_vector)
      lconds;
    test_point_in_polyhedron "floor_int_frac" m pconds;
    test_point_in_lattice `IsInt "floor_int_frac" m lconds;
    (result, pconds, lconds)

  let ceiling_int_frac m v =
    let (neg_v', pcond, lcond) = floor_int_frac m (V.negate v) in
    let v' = V.negate neg_v' in
    (v', pcond, lcond)

  let standard_vec_of_symbol dim_of_symbol s =
    V.of_term QQ.one (dim_of_symbol s)

  let int_frac_vec_of_symbol dim_of_symbol s =
    V.of_term QQ.one (dim_of_symbol s)
    |> V.add_term QQ.one (dim_of_symbol s + 1)

  let mk_expansion expand layout dim_of_symbol =
    let mk_standard lin =
      lin
        ~vec_of_free_dim:(V.of_term QQ.one)
        ~int_cond:(fun dim -> ([], [V.of_term QQ.one dim]))
        ~next_free_dim:(fun n -> n + 1)
        ~add_term_of_dim:IntMap.add
    in
    let mk_int_frac lin =
      lin
        ~vec_of_free_dim:(fun dim -> V.of_term QQ.one dim |> V.add_term QQ.one (dim + 1))
        ~int_cond:(fun dim -> ([(`Zero, V.of_term QQ.one (dim + 1))], []))
        ~next_free_dim:(fun n -> n + 2)
        ~add_term_of_dim:(fun free_dim term map ->
          IntMap.add free_dim term map |> IntMap.add (free_dim + 1) (TV_real QQ.zero)
        )
    in
    let int_frac_translate integral m v =
      let (result, pconds, lconds) = floor_int_frac m v in
      match integral with
      | `IsInt ->
         { p_cond = (`Zero, V.sub v result) :: pconds
         ; l_cond = lconds
         ; t_cond = []
         }
      | `NotInt ->
         { p_cond = (`Pos, V.sub v result) :: pconds
         ; l_cond = lconds
         ; t_cond = []
         }
    in
    let standard_translate integral _m v =
      match integral with
      | `IsInt -> { p_cond = []; l_cond = [v]; t_cond = [] }
      | `NotInt -> { p_cond = []; l_cond = []; t_cond = [v] }
    in
    match layout with
    | `Standard ->
       begin match expand with
       | `Expand free_dim ->
          { vec_of_symbol = standard_vec_of_symbol dim_of_symbol
          ; translate_int_atom = standard_translate
          ; expand_mod_floor =
              Expand_mod_floor_with
                { free_dim
                ; new_dimensions = IntMap.empty
                ; linearize_mod = mk_standard lin_mod
                ; linearize_floor = mk_standard lin_floor
                }
          }
       | `NoExpand ->
          { vec_of_symbol = standard_vec_of_symbol dim_of_symbol
          ; translate_int_atom = standard_translate
          ; expand_mod_floor = NoExpansion
          }
       end
    | `IntFrac ->
       begin match expand with
       | `Expand free_dim ->
          { vec_of_symbol = int_frac_vec_of_symbol dim_of_symbol
          ; translate_int_atom = int_frac_translate
          ; expand_mod_floor =
              Expand_mod_floor_with
                { free_dim
                ; new_dimensions = IntMap.empty
                ; linearize_mod = mk_int_frac lin_mod
                ; linearize_floor = mk_int_frac lin_floor
                }
          }
       | `NoExpand ->
          { vec_of_symbol = int_frac_vec_of_symbol dim_of_symbol
          ; translate_int_atom = int_frac_translate
          ; expand_mod_floor = NoExpansion
          }
       end

  (* Linear.linterm_of can only handle div and mod on constants, but
     [t div constant] and [t mod constant] can come from the input.
     Also, Interpretation.destruct_atom translates [IsInt t] into
     [t' mod constant] terms.
   *)
  let linearize_term srk expansion term =
    let vec_of_symbol = expansion.vec_of_symbol in
    let (curr_free_dim, curr_term_of_dim, lin_mod, lin_floor) =
      match expansion.expand_mod_floor with
      | Expand_mod_floor_with
        { free_dim
        ; new_dimensions
        ; linearize_mod = lin_mod
        ; linearize_floor = lin_floor
        } ->
         (ref free_dim, ref new_dimensions, lin_mod, lin_floor)
      | NoExpansion ->
         ( ref (-1)
         , ref IntMap.empty
         , (fun ~free_dim _term_of_dim -> ignore free_dim; invalid_arg "mod term in formula")
         , (fun ~free_dim _term_of_dim -> ignore free_dim; invalid_arg "floor term in formula")
         )
    in
    let (linearized, cond) =
      ArithTerm.eval srk (function
          | `Real r -> (Linear.const_linterm r, tru)
          | `App (x, []) -> (vec_of_symbol x, tru)
          | `App (_f, _xs) -> raise Linear.Nonlinear
          | `Var (_i, _typ) -> raise Linear.Nonlinear
          | `Add linconds ->
             List.fold_left
               (lift_binop V.add)
               (V.zero, tru)
               linconds
          | `Mul linconds ->
             List.fold_left
               (lift_binop mul_vec)
               (Linear.const_linterm QQ.one, tru)
               linconds
          | `Binop (`Div, lincond1, lincond2) ->
             begin
               let divide v1 v2 =
                 let divisor = try real_of v2 with | Invalid_argument _ -> raise Linear.Nonlinear
                 in
                 if QQ.equal divisor QQ.zero then invalid_arg "Division by zero"
                 else
                   V.scalar_mul (QQ.inverse divisor) v1
               in
               (lift_binop divide) lincond1 lincond2
             end
          | `Binop (`Mod, (v1, lincond1), (v2, lincond2)) ->
             let (term, cond, next_free_dim, next_term_of_dim) =
               lin_mod ~free_dim:!curr_free_dim !curr_term_of_dim v1 v2
             in
             let lincond = (conjoin lincond2 lincond1)
                           |> conjoin cond
             in
             curr_free_dim := next_free_dim;
             curr_term_of_dim := next_term_of_dim;
             (term, lincond)
          | `Unop (`Floor, (v, lincond)) ->
             let (term, cond, next_free_dim, next_term_of_dim) =
               lin_floor ~free_dim:!curr_free_dim !curr_term_of_dim v
             in
             let lincond_floor = conjoin cond lincond in
             curr_free_dim := next_free_dim;
             curr_term_of_dim := next_term_of_dim;
             (term, lincond_floor)
          | `Unop (`Neg, (v, lincond)) -> (V.negate v, lincond)
          | `Ite _ -> assert false
          | `Select _ -> raise Linear.Nonlinear
        ) term
    in
    let expand_mod_floor =
      match expansion.expand_mod_floor with
      | NoExpansion -> NoExpansion
      | Expand_mod_floor_with initial ->
         Expand_mod_floor_with
           { initial with
             free_dim = !curr_free_dim
           ; new_dimensions = !curr_term_of_dim
           }
    in
    (linearized, cond, {expansion with expand_mod_floor})

  let plt_ineq srk expansion (sign: [`Lt | `Leq | `Eq]) t1 t2 =
    let (v2, lin2, expansion2) = linearize_term srk expansion t2 in
    let (v1, lin1, expansion1) = linearize_term srk expansion2 t1 in
    let v = V.sub v2 v1 in
    let kind = match sign with
      | `Lt -> `Pos
      | `Leq -> `Nonneg
      | `Eq -> `Zero
    in
    let constrnt = {
        p_cond = (kind, v) :: (lin1.p_cond @ lin2.p_cond)
      ; l_cond = lin1.l_cond @ lin2.l_cond
      ; t_cond = lin1.t_cond @ lin2.t_cond
      }
    in
    (constrnt, expansion1)

  let plt_int srk univ_translation expansion interp (sign: [`IsInt | `NotInt]) t =
    let (v, lincond_linearize, next_expansion) = linearize_term srk expansion t in
    let m =
      match next_expansion.expand_mod_floor with
      | NoExpansion -> univ_translation interp
      | Expand_mod_floor_with {new_dimensions; _} ->
         (expand_univ_translation univ_translation new_dimensions) interp
    in
    let lincond_int = next_expansion.translate_int_atom sign m v
    in
    (conjoin lincond_int lincond_linearize, next_expansion)

  let plt_constraint_of_atom srk univ_translation expansion interp atom =
    match Formula.destruct srk atom with
    | `Tru -> (tru, expansion)
    | `Fls -> (fls, expansion)
    | `Not psi ->
       begin
         match Formula.destruct srk psi with
         | `Tru -> (fls, expansion)
         | `Fls -> (tru, expansion)
         | `Atom (`Arith (`Eq, t1, t2)) ->
            if Interpretation.evaluate_formula interp (Syntax.mk_lt srk t1 t2)
            then
              plt_ineq srk expansion `Lt t1 t2
            else
              plt_ineq srk expansion `Lt t2 t1
         | `Atom (`Arith (`Leq, t1, t2)) ->
            plt_ineq srk expansion `Lt t2 t1
         | `Atom (`Arith (`Lt, t1, t2)) ->
            plt_ineq srk expansion `Leq t2 t1
         | `Atom (`ArrEq (_t1, _t2)) -> invalid_arg "linearize_atom"
         | `Atom (`IsInt t) ->
            plt_int srk univ_translation expansion interp `NotInt t
         | _ -> invalid_arg "linearize_atom"
       end
    | `Atom (`Arith (`Eq, t1, t2)) ->
       plt_ineq srk expansion `Eq t1 t2
    | `Atom (`Arith (`Leq, t1, t2)) ->
       plt_ineq srk expansion `Leq t1 t2
    | `Atom (`Arith (`Lt, t1, t2)) ->
       plt_ineq srk expansion `Lt t1 t2
    | `Atom (`ArrEq (_t1, _t2)) -> invalid_arg "linearize_atom"
    | `Atom (`IsInt t) ->
       plt_int srk univ_translation expansion interp `IsInt t
    | _ -> invalid_arg "linearize_atom"

  let plt_implicant_of_implicant srk univ_translation expansion m implicant =
    match implicant with
    | None -> assert false
    | Some atoms ->
       List.fold_left (fun (lincond, expansion) atom ->
           let (lincond_atom, next_expansion) =
             plt_constraint_of_atom srk univ_translation expansion m atom in
           (conjoin lincond_atom lincond, next_expansion)
         )
         (tru, expansion)
         atoms

  let abstract_to_plt
        expansion
        srk
        ?(universe_p=[])
        ?(universe_l=[])
        ?(universe_t=[])
        univ_translation =
    let abstract interp phi =
      logf ~level:`debug "abstract_to_plt...";
      let implicant = Interpretation.select_implicant interp phi in
      logf ~level:`debug "abstract_to_plt: abstracting @[%a@]"
        (Format.pp_print_list
           ~pp_sep: (fun fmt () -> Format.fprintf fmt ", ")
           (fun fmt atom -> Syntax.Formula.pp srk fmt atom)
        )
        (Option.get implicant);
      let (lincond, post_expansion) =
        plt_implicant_of_implicant srk univ_translation expansion interp implicant in
      log_plt_constraints ~level:`debug "abstract_to_plt: abstracted: "
        (lincond.p_cond, lincond.l_cond, lincond.t_cond);
      let imp_p =
        Polyhedron.of_constraints
          (BatEnum.append (BatList.enum universe_p) (BatList.enum lincond.p_cond))
      in
      let imp_l =
        L.hermitize (List.rev_append universe_l lincond.l_cond)
      in
      let imp_t =
        L.hermitize (List.rev_append universe_t lincond.t_cond)
      in
      let plt = { poly_part = imp_p
                ; lattice_part = imp_l
                ; tiling_part = imp_t
                ; metadata = None
                }
      in
      let expanded_univ_translation =
        match post_expansion.expand_mod_floor with
        | NoExpansion -> univ_translation
        | Expand_mod_floor_with {new_dimensions ; _} ->
           logf ~level:`debug
             "abstract_to_plt: expanding universe with dimensions @[%a@]"
             (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
                Format.pp_print_int)
             (BatList.of_enum (IntMap.keys new_dimensions));
           expand_univ_translation univ_translation new_dimensions
      in
      test_point_in_polyhedron "abstract_to_plt"
        (expanded_univ_translation interp)
        (BatList.of_enum (P.enum_constraints plt.poly_part));
      test_point_in_lattice `IsInt "abstract_to_plt"
        (expanded_univ_translation interp)
        (L.basis plt.lattice_part);
      test_point_in_lattice `NotInt "abstract_to_plt"
        (expanded_univ_translation interp)
        (L.basis plt.tiling_part);
      (plt, expanded_univ_translation)
    in
    LocalAbstraction.{ abstract }

  let formula_of_plt srk term_of_dim plt =
    let phis_p =
      BatEnum.fold
        (fun phis constr -> formula_p srk term_of_dim constr :: phis)
        []
        (P.enum_constraints plt.poly_part)
    in
    let phis_l =
      BatList.fold
        (fun phis lconstr -> formula_l srk term_of_dim lconstr :: phis)
        []
        (L.basis plt.lattice_part)
    in
    let phis_t =
      BatList.fold
        (fun phis tconstr -> formula_t srk term_of_dim tconstr :: phis)
        []
        (L.basis plt.tiling_part)
    in
    mk_and srk (phis_p @ phis_l @ phis_t)

  let int_frac_layout ~num_terms =
    let start_of_term_int_frac =
      if num_terms mod 2 = 0 then num_terms
      else num_terms + 1
    in
    let start_of_symbol_int_frac = start_of_term_int_frac + (2 * num_terms) in
    { start_of_term_int_frac
    ; start_of_symbol_int_frac
    }

  let mk_interp_dim layout terms interp dim =
    let num_terms = Array.length terms in
    match layout with
    | `Standard ->
       if dim >= num_terms then
         Interpretation.real interp (Syntax.symbol_of_int (dim - num_terms))
       else if dim >= 0 && dim < num_terms then
         Interpretation.evaluate_term interp terms.(dim)
       else
         begin
           logf "interp_dim: %d not defined" dim;
           assert false
         end
    | `IntFrac ->
       let {start_of_term_int_frac ; start_of_symbol_int_frac} =
         int_frac_layout ~num_terms in
       let int r = QQ.floor r |> QQ.of_zz in
       let frac r = QQ.modulo r QQ.one in
       let original_idx base int_frac_idx =
         let idx =
           if int_frac_idx mod 2 = 0 then (int_frac_idx - base) / 2
           else (int_frac_idx - 1 - base) / 2
         in
         assert (idx >= 0);
         idx
       in
       if dim >= start_of_symbol_int_frac then
         let idx = original_idx start_of_symbol_int_frac dim in
         let value = Interpretation.real interp (Syntax.symbol_of_int idx) in
         if dim mod 2 = 0 then int value else frac value
       else if dim >= start_of_term_int_frac && dim < start_of_symbol_int_frac
       then
         let idx = original_idx start_of_term_int_frac dim in
         assert (idx >= 0 && idx < num_terms);
         let value = Interpretation.evaluate_term interp terms.(idx) in
         if dim mod 2 = 0 then int value else frac value
       else if dim >= 0 && dim < num_terms then
         Interpretation.evaluate_term interp terms.(dim)
       else if dim >= num_terms && dim < start_of_term_int_frac then QQ.zero
       else
         begin
           logf "interp_dim: %d not defined" dim;
           assert false
         end

  let mk_term_definitions layout srk dim_of_symbol terms =
    let linearize_term =
      match layout with
      | `Standard ->
         linearize_term srk (mk_expansion `NoExpand `Standard dim_of_symbol)
      | `IntFrac ->
         linearize_term srk (mk_expansion `NoExpand `IntFrac dim_of_symbol)
    in
    let vector_of_term idx =
      match layout with
      | `Standard -> V.of_term QQ.one idx
      | `IntFrac ->
         let {start_of_term_int_frac; _} =
           int_frac_layout ~num_terms:(Array.length terms) in
         let int_dim_of_term i = start_of_term_int_frac + (2 * i) in
         V.of_term QQ.one (int_dim_of_term idx)
         |> V.add_term QQ.one (int_dim_of_term idx + 1)
    in
    let (p_conds, l_conds, t_conds) =
      (ref (BatEnum.empty ()), ref (BatEnum.empty ()), ref (BatEnum.empty ()))
    in
    Array.iteri
      (fun dim term ->
        let (v, lincond, _expansion) = linearize_term term in
        BatEnum.push !p_conds
          (`Zero, V.add v (V.negate (vector_of_term dim)));
        p_conds := BatEnum.append (BatList.enum lincond.p_cond) !p_conds;
        l_conds := BatEnum.append (BatList.enum lincond.l_cond) !l_conds;
        t_conds := BatEnum.append (BatList.enum lincond.t_cond) !t_conds
      )
      terms;
    ( BatList.of_enum !p_conds
    , BatList.of_enum !l_conds
    , BatList.of_enum !t_conds
    )

  let get_max_dim layout num_terms symbols =
    match layout with
    | `Standard ->
       begin match Symbol.Set.max_elt_opt symbols with
       | None -> num_terms - 1
       | Some dim -> Syntax.int_of_symbol dim + num_terms
       end
    | `IntFrac ->
       let {start_of_symbol_int_frac; _} = int_frac_layout ~num_terms in
       begin match Symbol.Set.max_elt_opt symbols with
       | None -> start_of_symbol_int_frac - 1
       | Some dim ->
          let num_symbols = Syntax.int_of_symbol dim + 1 in
          start_of_symbol_int_frac + (2 * num_symbols) - 1
       end

  let abstract_to_standard_plt has_mod_floor srk terms symbols =
    let num_terms = Array.length terms in
    let max_dim = get_max_dim `Standard num_terms symbols in
    logf ~level:`debug "initial plt abstraction: max_dim: %d, num_terms = %d@;"
      max_dim num_terms;
    let dim_of_symbol sym = Syntax.int_of_symbol sym + num_terms in
    let expansion =
      let expand = match has_mod_floor with
        | `NoExpandModFloor -> `NoExpand
        | `ExpandModFloor -> `Expand (max_dim + 1)
      in
      mk_expansion expand `Standard dim_of_symbol
    in
    let (universe_p, universe_l, universe_t) =
      mk_term_definitions `Standard srk dim_of_symbol terms in
    logf ~level:`debug "abstract_to_standard_plt...";
    log_plt_constraints ~level:`debug "term definitions" (universe_p, universe_l, universe_t);
    let interp_dim = mk_interp_dim `Standard terms in
    abstract_to_plt expansion srk ~universe_p ~universe_l ~universe_t interp_dim

  (* LIRA PLT layout:
     0 ... len(terms) - 1 represent terms.
     Let n be the first even integer >= len(terms).
     Dimensions corresponding to integer-valued variables are even and
     those for fractional variables are odd.
     Then n + 2k, n + 2k + 1 are the integer and fractional dimensions for
     the (k-1)-th term, k = 1, ..., len(terms).
     Dimensions (n + 2 * (len(terms) + m), (n + (2 * len(terms) + m) + 1)
     are the integer and fractional dimensions for symbol m,
     m = 0, ..., max_elt symbols.
   *)
  let abstract_to_intfrac_plt has_mod_floor srk terms symbols =
    let num_terms = Array.length terms in
    let { start_of_symbol_int_frac ; start_of_term_int_frac} =
      int_frac_layout ~num_terms in
    let max_dim = get_max_dim `IntFrac num_terms symbols in
    logf ~level:`debug
      "initial int-frac plt abstraction: max_dim: %d, num_terms = %d,
       start_of_term_int_frac = %d, start_of_symbol_int_frac = %d@;"
      max_dim num_terms start_of_term_int_frac start_of_symbol_int_frac;
    let int_dim_of_symbol sym =
      start_of_symbol_int_frac + (2 * Syntax.int_of_symbol sym) in
    let expansion =
      let expand = match has_mod_floor with
        | `NoExpandModFloor -> `NoExpand
        | `ExpandModFloor -> `Expand (max_dim + 1)
      in
      mk_expansion expand `IntFrac int_dim_of_symbol
    in
    let (universe_p, universe_l, universe_t) =
      mk_term_definitions `IntFrac srk int_dim_of_symbol terms
    in
    logf ~level:`debug "abstract_to_intfrac_plt...";
    log_plt_constraints ~level:`debug "term definitions" (universe_p, universe_l, universe_t);
    let interp_dim = mk_interp_dim `IntFrac terms in
    abstract_to_plt expansion srk
      ~universe_p ~universe_l ~universe_t interp_dim

  let abstract_poly_part abstract_poly =
    let abstract m plt =
      let p = plt.poly_part in
      let (p', p_translate) = LocalAbstraction.apply2 abstract_poly m p in
      ({ plt with poly_part = p' }, p_translate)
    in
    LocalAbstraction.{abstract}

end

module ModelSearch: sig
  
  val extrapolate: integer_point:V.t -> direction:V.t -> 'a Plt.t -> V.t list

  val model_to_vector: IntSet.t -> (int -> QQ.t) -> V.t

end = struct

  let model_to_vector dimensions m =
    IntSet.fold (fun dim v ->
        if dim <> Linear.const_dim then V.add_term (m dim) dim v
        else v)
      dimensions
      V.zero

  let extrapolate ~integer_point ~direction plt =
    let lt = List.rev_append
               (L.basis (Plt.tiling_part plt))
               (L.basis (Plt.lattice_part plt)) in
    if V.equal V.zero direction then [integer_point]
    else
      begin
        logf ~level:`debug
          "extrapolate: integer point is @[%a@]@; direction is @[%a@]@;"
          pp_vector integer_point
          pp_vector direction;
        let u = List.map (V.dot direction) lt in
        let gcd = List.fold_left (fun a b -> QQ.gcd a b) QQ.zero u in
        let integral_direction = not (QQ.equal QQ.zero gcd) in
        let rescaled =
          if QQ.equal QQ.zero gcd then direction
          else V.scalar_mul (QQ.inverse gcd) direction
        in
        let min = function
          | `PlusInfinity, `PlusInfinity -> `PlusInfinity
          | `PlusInfinity, `Num n -> `Num n
          | `Num n, `PlusInfinity -> `Num n
          | `Num n1, `Num n2 -> `Num (QQ.min n1 n2)
        in
        let (coeff_neg_dirn, coeff_pos_dirn) =
          BatEnum.fold
            (fun (max_neg_dirn, max_pos_dirn) (kind, v) ->
              let eval_base = QQ.add (V.dot v integer_point) (V.coeff Linear.const_dim v) in
              let eval_rescaled_direction = V.dot v rescaled in
              let (curr_num_steps_neg_dirn, curr_num_steps_pos_dirn) =
                match kind with
                | `Zero ->
                   if QQ.equal QQ.zero eval_rescaled_direction then
                     (`PlusInfinity, `PlusInfinity)
                   else
                     (`Num QQ.zero, `Num QQ.zero)
                | `Nonneg
                  | `Pos ->
                   if QQ.equal QQ.zero eval_rescaled_direction then
                     (`PlusInfinity, `PlusInfinity)
                   else
                     let num_steps =
                       if integral_direction then
                         QQ.of_zz (QQ.idiv eval_base (QQ.abs eval_rescaled_direction))
                       else 
                         QQ.div eval_base (QQ.abs eval_rescaled_direction)
                     in
                     let remainder =
                       if integral_direction then
                         QQ.modulo eval_base (QQ.abs eval_rescaled_direction)
                       else QQ.zero
                     in
                     match ( QQ.lt QQ.zero eval_rescaled_direction
                           , integral_direction )
                     with
                     | (true, true) ->
                        if QQ.equal QQ.zero remainder && kind = `Pos then
                          (`Num (QQ.sub num_steps QQ.one), `PlusInfinity)
                        else
                          (`Num num_steps, `PlusInfinity)
                     | (false, true) ->
                        if QQ.equal QQ.zero remainder && kind = `Pos then
                          (`PlusInfinity, `Num (QQ.sub num_steps QQ.one))
                        else
                          (`PlusInfinity, `Num num_steps)
                     | (true, false) ->
                        if QQ.equal QQ.zero remainder && kind = `Pos then
                          (`Num (QQ.div num_steps (QQ.of_int 2)), `PlusInfinity)
                        else
                          (`Num num_steps, `PlusInfinity)
                     | (false, false) ->
                        if QQ.equal QQ.zero remainder && kind = `Pos then
                          (`PlusInfinity, `Num (QQ.div num_steps (QQ.of_int 2)))
                        else
                          (`Num num_steps, `PlusInfinity)
              in
              ( min (max_neg_dirn, curr_num_steps_neg_dirn)
              , min (max_pos_dirn, curr_num_steps_pos_dirn)
              )
            )
            (`PlusInfinity, `PlusInfinity)
            (P.enum_constraints (Plt.poly_part plt))
        in
        let translate coeff =
          if QQ.equal QQ.zero coeff then
            None
          else
            Some (V.add integer_point (V.scalar_mul coeff rescaled))
        in
        match (coeff_neg_dirn, coeff_pos_dirn) with
        | (`Num n1), (`Num n2) ->
           BatList.filter_map translate [QQ.negate n1; n2]
        | (`Num n1, `PlusInfinity) ->
           BatList.filter_map translate [QQ.negate n1]
        | (`PlusInfinity, `Num n2) ->
           BatList.filter_map translate [n2]
        | (`PlusInfinity, `PlusInfinity) -> []
      end

end

module Ddify: sig

  val abstract:
    man:DD.closed Apron.Manager.t ->
    max_dim_in_projected: int ->
    (P.t, int -> QQ.t, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t

end = struct

  let abstract ~man ~max_dim_in_projected =
    let abstract _m p =
      logf ~level:`debug "DDifying @[%a@] in ambient dimension %d" (P.pp pp_dim) p
        (max_dim_in_projected + 1);
      let dd = P.dd_of ~man (max_dim_in_projected + 1) p in
      let () = logf ~level:`debug "DDified@;" in
      (dd, (fun m -> m))
    in
    LocalAbstraction.{ abstract }

end

module LoosWeispfenning: sig

  val abstract_lw:
    elim: (int -> bool) ->
    (P.t, int -> QQ.t, P.t, int -> QQ.t) LocalAbstraction.t

end = struct

  let abstract_lw ~elim =
    let abstract m p =
      let to_project =
        BatList.of_enum (P.enum_constraints p)
        |> collect_dimensions (fun (_, v) -> v) (fun _ -> true)
        |> IntSet.filter elim
        |> IntSet.to_list
      in
      logf ~level:`debug "abstract_lw: eliminating dimensions @[%a@] from @[%a@]"
        (Format.pp_print_list ~pp_sep:(fun fmt _ -> Format.fprintf fmt ", ")
           Format.pp_print_int)
        to_project
        (P.pp pp_dim) p;
      let abstracted = P.local_project m to_project p in
      logf ~level:`debug "abstract_lw: abstracted.@\n";
      test_point_in_polyhedron "abstract_lw" m
        (BatList.of_enum (P.enum_constraints abstracted));
      let restricted m dim =
        if elim dim then failwith "abstract_lw: Dimension has been eliminated"
        else m dim
      in
      (abstracted, restricted)
    in
    LocalAbstraction.{ abstract }

end

module MixedCooper: sig

  (* Dimensions to be eliminated must take on only integer values in the
     universe.
   *)
  val abstract_cooper:
    elim: (int -> bool) ->
    ceiling: ((int -> QQ.t) -> V.t -> (V.t * (P.constraint_kind * V.t) list * V.t list)) ->
    ('layout Plt.t, int -> QQ.t, 'layout Plt.t, int -> QQ.t) LocalAbstraction.t

end = struct

  let substitute_for_in v dim w =
    let (coeff, w') = V.pivot dim w in
    V.add (V.scalar_mul coeff v) w'

  let virtual_sub_p vt dim (kind, v) =
    let (coeff, _) = V.pivot dim v in
    let result =
      if QQ.equal coeff QQ.zero then
        Some (kind, v)
      else
        match (vt, QQ.lt QQ.zero coeff) with
        | (`PlusInfinity, true) ->
           begin match kind with
           | `Zero -> invalid_arg "abstract_cooper: invalid selection of +infty"
           | `Nonneg
             | `Pos -> None
           end
        | (`MinusInfinity, false) ->
           begin match kind with
           | `Zero -> invalid_arg "abstract_cooper: invalid selection of -infty"
           | `Nonneg
             | `Pos -> None
           end
        | (`PlusInfinity, false) ->
           invalid_arg "abstract_cooper: invalid selection of +infty"
        | (`MinusInfinity, true) ->
           invalid_arg "abstract_cooper: invalid selection of -infty"
        | (`Term t, _) ->
           Some (kind, substitute_for_in t dim v)
    in
    logf ~level:`trace "virtual substitution: substituting %a for %d in @[%a@]"
      (fun fmt vt -> match vt with
                     | `PlusInfinity -> Format.fprintf fmt "+infty"
                     | `MinusInfinity -> Format.fprintf fmt "-infty"
                     | `Term t -> pp_vector fmt t
      ) vt
      dim pp_pconstr (kind, v);
    logf ~level:`trace "virtual substitution: result is @[%a@]"
      (Format.pp_print_option
         ~none:(fun fmt _ -> Format.fprintf fmt "None") pp_pconstr)
      result;
    result

  (* TODO: Verify that there is only one possibility in the range
     [0, lcm of denom)
   *)
  let virtual_sub_l lcm_denom_dim_in_lt m vt dim v =
    let (coeff, _) = V.pivot dim v in
    if QQ.equal coeff QQ.zero then Some v
    else
      match vt with
      | `PlusInfinity
        | `MinusInfinity ->
         let delta = QQ.modulo (m dim) lcm_denom_dim_in_lt in
         Some (substitute_for_in (V.of_term delta Linear.const_dim) dim v)
      | `Term t ->
         Some (substitute_for_in t dim v)

  let virtual_sub substitution_fn vt dim constraints =
    let result = BatEnum.empty () in
    List.iter
      (fun constr ->
        begin match substitution_fn vt dim constr with
        | None -> ()
        | Some atom -> BatEnum.push result atom
        end
      )
      constraints;
    BatList.of_enum result |> List.rev

  let glb_for dim p m =
    let has_upper_bound = ref false in
    let argmax (kind1, lower_bound1, b1) (kind2, lower_bound2, b2) =
      if QQ.lt b1 b2 then (kind2, lower_bound2, b2)
      else if QQ.lt b2 b1 then (kind1, lower_bound1, b1)
      else
        begin
          match (kind1, kind2) with
          | (`Nonneg, `Pos)
            | (`Nonneg, `Zero)
            | (`Pos, `Zero) -> (kind2, lower_bound2, b2)
          | (_, _) -> (kind1, lower_bound1, b1)
        end
    in
    let glb = ref None in
    let set_glb lb =
      logf ~level:`debug "glb_for: setting lower bound @[%a@]"
        pp_vector (let (_, lower_bound, _) = lb in lower_bound);
      glb := Some lb
    in
    List.iter
      (fun (kind, v) ->
        logf ~level:`debug "glb_for: @[%a@]"
          pp_pconstr (kind, v);
        let (coeff, w) = V.pivot dim v in
        if QQ.equal QQ.zero coeff then
          ()
        else
          let lower_bound = V.scalar_mul (QQ.negate (QQ.inverse coeff)) w in
          let b = Linear.evaluate_affine m lower_bound in
          if QQ.lt QQ.zero coeff then
            begin
              let () =
                match kind with
                | `Zero -> has_upper_bound := true
                | _ -> ()
              in
              match !glb with
              | None ->
                 set_glb (kind, lower_bound, b)
              | Some (kind0, lower_bound0, b0) ->
                 set_glb (argmax (kind0, lower_bound0, b0) (kind, lower_bound, b))
            end
          else
            begin
              has_upper_bound := true;
              match kind with
              | `Zero ->
                 begin match !glb with
                 | None ->
                    set_glb (kind, lower_bound, b)
                 | Some (kind0, lower_bound0, b0) ->
                    set_glb (argmax (kind0, lower_bound0, b0) (kind, lower_bound, b))
                 end
              | _ -> ()
            end
      )
      p;
    (!glb, !has_upper_bound)

  let lcm_denom dim vectors =
    List.fold_left
      (fun lcm v ->
        let coeff = V.coeff dim v in
        if QQ.equal QQ.zero coeff then lcm
        else ZZ.lcm lcm (QQ.denominator coeff)
      )
      ZZ.one vectors

  (* For vectors v, v' in dimensions free of elim_dim,
     [ceiling m t = t']  only if [t'] evaluated at [m] is the least integer
     greater than or equal to [t] evaluated at [m].
     For a general lattice, orient its constraints to have positive coefficient
     in [elim_dim]. Then "integer" generalizes to a (finite-dimensional) vector
     of integers, and "least integer" means least in product order.
     If [ceiling] has finite image (for each t), [abstract_cooper_one] has.
   *)
  let cooper_one ceiling lcm_denom_elim_dim_in_lt elim_dim m (p, l, t) =
    logf ~level:`debug "cooper_one: eliminating %d, lcm of denom is %a"
      elim_dim QQ.pp lcm_denom_elim_dim_in_lt;
    let select_term lower =
      let delta = QQ.modulo
                    (QQ.sub (m elim_dim) (Linear.evaluate_affine m lower))
                    lcm_denom_elim_dim_in_lt
      in
      let term = V.add_term delta Linear.const_dim lower in
      logf ~level:`debug
        "select_term: calculating delta: value of elim dimension %d = %a,
         value of lower bound = %a, lcm_denom_elim_dim = %a, delta = %a@;"
        elim_dim
        QQ.pp (m elim_dim)
        QQ.pp (Linear.evaluate_affine m lower)
        QQ.pp lcm_denom_elim_dim_in_lt
        QQ.pp delta;
      logf ~level:`debug "cooper_one: selected term @[%a@]@;" pp_vector term;
      term
    in
    let (term_selected, pcond, lcond) =
      match glb_for elim_dim p m with
      | (_, false) ->
         logf ~level:`debug "abstract_cooper: selecting +infty";
         (`PlusInfinity, [], [])
      | (None, _) ->
         logf ~level:`debug "abstract_cooper: selecting -infty";
         (`MinusInfinity, [], [])
      | (Some (kind, term, value), true) ->
         logf ~level:`debug "abstract_cooper: selecting term based on @[%a@]"
           pp_pconstr (kind, V.add_term QQ.one elim_dim (V.negate term));
         let (rounded, pcond, lcond) = ceiling m term in
         if Option.is_some (QQ.to_zz value) && kind = `Pos then
           let lb = V.add_term QQ.one Linear.const_dim rounded
           in
           logf ~level:`debug
             "selecting term based on rounding + 1: @[%a@]" pp_vector
             rounded;
           (`Term (select_term lb), pcond, lcond)
         else
           let (rounded, pcond, lcond) = ceiling m term in
           logf ~level:`debug "selecting term based on just rounding: @[%a@]" pp_vector rounded;
           (`Term (select_term rounded), pcond, lcond)
    in
    let polyhedron =
      virtual_sub virtual_sub_p term_selected elim_dim p
      |> List.rev_append pcond
    in
    let virtual_sub_l =
      virtual_sub (virtual_sub_l lcm_denom_elim_dim_in_lt m)
    in
    let lattice = virtual_sub_l term_selected elim_dim l
                  |> List.rev_append lcond
    in
    let tiling = virtual_sub_l term_selected elim_dim t
    in
    test_point_in_polyhedron "cooper_one" m polyhedron;
    test_point_in_lattice `IsInt "cooper_one" m lattice;
    test_point_in_lattice `NotInt "cooper_one" m tiling;
    (polyhedron, lattice, tiling)

  let abstract_cooper_ ~elim ~ceiling m plt =
    let open Plt in
    let p = P.enum_constraints (Plt.poly_part plt) |> BatList.of_enum in
    let l = L.basis (Plt.lattice_part plt) in
    let t = L.basis (Plt.tiling_part plt) in
    let elim_dimensions =
      Plt.constrained_dimensions plt
      |> IntSet.filter elim
    in
    logf ~level:`debug "abstract_cooper: eliminating dimensions @[%a@] from@\n"
      IntSet.pp elim_dimensions;
    log_plt_constraints ~level:`debug "plt: " (p, l, t);
    let (projected_p, projected_l, projected_t) =
      IntSet.fold
        (fun elim_dim (p, l, t) ->
          let lcm = lcm_denom elim_dim (List.rev_append l t) in
          cooper_one ceiling (QQ.of_zz lcm) elim_dim m (p, l, t)
        )
        elim_dimensions
        (p, l, t)
    in
    logf ~level:`debug "abstract_cooper: abstracted";
    mk_plt ~poly_part:(Polyhedron.of_constraints (BatList.enum projected_p))
      ~lattice_part:(L.hermitize projected_l)
      ~tiling_part:(L.hermitize projected_t)

  let abstract_cooper ~elim ~ceiling =
    let restricted m dim =
      if elim dim then failwith "abstract_cooper: Dimension has been eliminated"
      else m dim
    in
    LocalAbstraction.
    {
      abstract =
        (fun m plt -> (abstract_cooper_ ~elim ~ceiling m plt, restricted))
    }

end

module SubspaceCone : sig

  val abstract_sc:
    man:DD.closed Apron.Manager.t ->
    max_dim_in_projected: int ->
    ('layout Plt.t, int -> QQ.t, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t

end = struct

  module LW = LoosWeispfenning

  let close_constraints constrs =
    constrs
    |> BatEnum.map
         (fun (kind, v) ->
           match kind with
           | `Zero | `Nonneg -> (kind, v)
           | `Pos -> (`Nonneg, v)
         )

  let abstract_sc ~man ~max_dim_in_projected =
    let abstract m plt =
      logf ~level:`debug "abstract_sc...";
      let abstract_lw =
        let abstract =
          LW.abstract_lw ~elim:(fun dim -> dim > max_dim_in_projected)
          |> LocalAbstraction.compose
               (Ddify.abstract ~man ~max_dim_in_projected)
        in
        LocalAbstraction.apply abstract m
      in
      let closed_p = close_constraints (P.enum_constraints (Plt.poly_part plt))
                     |> P.of_constraints in
      let l_constraints = L.basis (Plt.lattice_part plt) in
      logf ~level:`debug "abstract_sc: lattice constraints: @[%a@]"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
           pp_vector)
        l_constraints;
      let subspace_constraints =
        List.map
          (fun v ->
            ( `Zero
            , V.add_term
                (QQ.negate (Linear.evaluate_affine m v))
                Linear.const_dim
                v
            )
          )
          l_constraints
      in
      let polyhedron_abstraction = abstract_lw closed_p in
      let subspace_abstraction =
        match subspace_constraints with
        | [] -> polyhedron_abstraction
        | _ ->
           BatEnum.append (BatList.enum subspace_constraints)
             (P.enum_constraints closed_p)
           |> P.of_constraints
           |> abstract_lw
      in
      logf ~level:`debug "abstract_sc: combining...";
      let recession_cone =
        DD.enum_generators polyhedron_abstraction
        |> BatEnum.filter (fun (kind, _) -> kind = `Ray || kind = `Line)
      in
      let dd = BatEnum.append (DD.enum_generators subspace_abstraction)
                 recession_cone
               |> DD.of_generators ~man (max_dim_in_projected + 1) in
      logf ~level:`debug "abstract_sc: combined dd = @[%a@]"
        (DD.pp pp_dim) dd;
      let restricted m dim =
        if dim > max_dim_in_projected
        then failwith "abstract_sc: Dimension has been eliminated"
        else m dim
      in
      (dd, restricted)
    in
    LocalAbstraction.{ abstract }

end

module IntFracProjection: sig

  val abstract_intfrac_plt:
    elim:(int -> bool) ->
    (Plt.intfrac Plt.t, int -> QQ.t, Plt.intfrac Plt.t, int -> QQ.t)
      LocalAbstraction.t

end = struct

  module LW = LoosWeispfenning

  let abstract_intfrac_plt ~elim =
    let abstract m plt =
      logf ~level:`debug "abstract_intfrac_plt...";
      let must_be_integral dim =
        (* If dim is supported in any positive integrality constraint,
           dim itself is.
         *)
        L.member (V.of_term QQ.one dim) (Plt.lattice_part plt) in
      let abstract_lw =
        LW.abstract_lw
          ~elim:(fun dim ->
            elim dim &&
              (* If an integrality assumption for an integer dimension is
                 not used, it is sound to treat it as real-valued.
               *)
              not (must_be_integral dim)) in
      let abstract_cooper =
        MixedCooper.abstract_cooper
          ~elim:(fun dim -> elim dim && must_be_integral dim)
          ~ceiling:Plt.ceiling_int_frac
      in
      LocalAbstraction.apply2
        (Plt.abstract_poly_part abstract_lw
         |> LocalAbstraction.compose abstract_cooper)
        m plt
    in
    LocalAbstraction.{abstract}
end

module LwCooper: sig

  (** This abstraction does real projection for real-valued dimensions and
      Cooper projection for integer-valued dimensions.
   *)
  val abstract_lw_cooper:
    elim: (int -> bool) ->
    ('layout Plt.t, int -> QQ.t, 'layout Plt.t, int -> QQ.t) LocalAbstraction.t

end = struct

  let abstract_lw_cooper_ ~elim m plt =
    let p = P.enum_constraints (Plt.poly_part plt) |> BatList.of_enum in
    let l = L.basis (Plt.lattice_part plt) in
    let t = L.basis (Plt.tiling_part plt) in
    log_plt_constraints ~level:`debug "abstract_lw_cooper: abstracting" (p, l, t);
    let elim_dimensions =
      Plt.constrained_dimensions plt |> IntSet.filter elim in
    let integer_dimensions = collect_dimensions (fun v -> v) (fun _ -> true) l in
    let (int_dims_to_elim, real_dims_to_elim) =
      IntSet.partition (fun dim -> IntSet.mem dim integer_dimensions)
        elim_dimensions
    in
    let abstract_lw =
      LoosWeispfenning.abstract_lw
        ~elim:(fun dim -> IntSet.mem dim real_dims_to_elim)
    in
    let local_abstraction =
      Plt.abstract_poly_part abstract_lw
      |> LocalAbstraction.compose
           (MixedCooper.abstract_cooper
              ~elim:(fun dim -> IntSet.mem dim int_dims_to_elim)
              ~ceiling:(fun _ v -> (v, [], [])))
    in
    let (plt, univ_translation) =
      LocalAbstraction.apply2 local_abstraction m plt in
    let projected_p = Plt.poly_part plt in
    let projected_l = Plt.lattice_part plt in
    let projected_t = Plt.tiling_part plt in
    log_plt_constraints ~level:`debug "abstract_lw_cooper: abstracted"
      ( BatList.of_enum (P.enum_constraints projected_p)
      , L.basis projected_l
      , L.basis projected_t);
    (plt, univ_translation)

  let abstract_lw_cooper ~elim =
    LocalAbstraction.
    {
      abstract = abstract_lw_cooper_ ~elim
    }

end

module LocalGlobal: sig

  open Syntax
  open Interpretation

  val localize:
    ('concept1, 'point1, 'concept2, 'point2) Abstraction.t ->
    ('concept1, 'point1, 'concept2, 'point2) LocalAbstraction.t

  val lift_dd_abstraction:
    man:(DD.closed Apron.Manager.t) ->
    'a context -> max_dim:int -> term_of_dim:(int -> 'a Syntax.arith_term) ->
    ('a formula, 'a interpretation, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t ->
    ('a formula, 'a interpretation, DD.closed DD.t, int -> QQ.t) Abstraction.t

  val lift_plt_abstraction:
    'a context -> term_of_dim:(int -> 'a Syntax.arith_term) ->
    ('a formula, 'a interpretation, 'layout Plt.t, int -> QQ.t) LocalAbstraction.t ->
    ('a formula, 'a interpretation, 'layout Plt.t list, int -> QQ.t) Abstraction.t

end = struct

  open Syntax

  let localize
        (abstraction : ('concept1, 'point1, 'concept2, 'point2) Abstraction.t) =
    LocalAbstraction.
    { abstract = (fun _x c -> abstraction.abstract c) }

  let lift_abstraction ?(max_dim_to_inspect = -1)
        srk join formula_of top bottom term_of_dim local_abs =
    let counter = ref 0 in
    let of_model phi m =
      match m with
      | `LIRR _ -> assert false
      | `LIRA m ->
         let () =
           let rec evaluate n l =
             if n < 0 then l
             else
               let term = term_of_dim n in
               let l' = (term, Interpretation.evaluate_term m term) :: l in
               evaluate (n - 1) l'
           in
           logf ~level:`debug "model: @[%a@]@;"
             (Format.pp_print_list
                ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
                (fun fmt (t, value) ->
                  Format.fprintf fmt "(%a, %a)"
                    (Syntax.ArithTerm.pp srk) t
                    QQ.pp value)
             )
             (evaluate max_dim_to_inspect [])
         in
         logf ~level:`info "Abstraction loop iteration: %d" !counter;
         counter := !counter + 1;
         LocalAbstraction.apply local_abs m phi
    in
    let abstract phi =
      let domain =
        Abstract.
        { join
        ; of_model = of_model phi
        ; formula_of
        ; top
        ; bottom
        }
      in
      let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
      ( Abstract.Solver.abstract solver domain
      , fun interp -> (fun dim -> Interpretation.evaluate_term interp (term_of_dim dim))
      )
    in
    Abstraction.{abstract}

  let lift_dd_abstraction ~man
        (srk: 'a context) ~max_dim ~term_of_dim
        local_abs =
    let ambient_dim = max_dim + 1 in
    let formula_of dd =
      let fml = formula_of_dd srk term_of_dim dd in
      logf ~level:`debug "Blocking %a" (Syntax.Formula.pp srk) fml;
      fml
    in
    let top = P.dd_of ~man ambient_dim P.top in
    let bottom = P.dd_of ~man ambient_dim P.bottom in
    lift_abstraction ~max_dim_to_inspect:max_dim
      srk DD.join formula_of top bottom term_of_dim local_abs

  let lift_plt_abstraction srk ~term_of_dim local_abs =
    let local_abs' =
      let abstract m phi =
        let ((plt: 'b Plt.t), univ_translation) =
          local_abs.LocalAbstraction.abstract m phi in
        ([plt], univ_translation)
      in
      LocalAbstraction.{abstract}
    in
    let join plts1 plts2 = plts1 @ plts2 in
    let formula_of plts =
      let to_block = mk_or srk (List.map (Plt.formula_of_plt srk term_of_dim) plts) in
      logf ~level:`debug "blocking: @[%a@]" (Syntax.Formula.pp srk) to_block;
      to_block
    in
    let top = [Plt.top] in
    let bottom = [] in
    lift_abstraction srk join formula_of top bottom term_of_dim local_abs'

end

module AbstractTerm: sig

  val mk_sc_abstraction:
    man:DD.closed Apron.Manager.t ->
    [ `ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> Q.t)
      LocalAbstraction.t

  val mk_sc_abstraction_with_acceleration:
    man:DD.closed Apron.Manager.t ->
    [ `ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> Q.t)
      LocalAbstraction.t

  val mk_cooper_abstraction:
    [ `ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, Plt.standard Plt.t, int -> Q.t)
      LocalAbstraction.t

  val mk_lw_cooper_abstraction:
    man:DD.closed Apron.Manager.t ->
    [`IntHullAfterProjection | `NoIntHullAfterProjection] ->
    [ `ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> Q.t)
      LocalAbstraction.t

  val mk_intfrac_abstraction:
    man:DD.closed Apron.Manager.t ->
    [ `ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> Q.t)
      LocalAbstraction.t

  val mk_intfrac_abstraction_with_acceleration:
    man:DD.closed Apron.Manager.t ->
    [ `ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> Q.t)
      LocalAbstraction.t

end = struct

  let abstract_multiple_models abstract_to_plt abstract_to_dd models phi =
    let end_to_end = abstract_to_plt |> LocalAbstraction.compose abstract_to_dd in
    match models with
    | [] -> invalid_arg "at least one model is needed"
    | [interp] -> LocalAbstraction.apply2 end_to_end interp phi
    | interp1 :: interp2 :: _ ->
       let (plt1, univ_translation1) =
         LocalAbstraction.apply2 abstract_to_plt interp1 phi in
       let point = univ_translation1 interp1 in
       let (dd1, univ_translation2) =
         LocalAbstraction.apply2 abstract_to_dd point plt1 in
       let dimensions = Plt.constrained_dimensions plt1 in
       let integer_point = ModelSearch.model_to_vector dimensions point in
       let rational_point = univ_translation1 interp2
                            |> ModelSearch.model_to_vector dimensions in
       let points =
         let direction = V.sub rational_point integer_point in
         ModelSearch.extrapolate ~integer_point ~direction plt1
       in
       log_plt_constraints ~level:`debug "diversifying within"
         ( BatList.of_enum (P.enum_constraints (Plt.poly_part plt1))
         , L.basis (Plt.lattice_part plt1)
         , L.basis (Plt.tiling_part plt1));
       logf ~level:`debug "diversified points: @[%a@]@\n@[%a@]@;"
         pp_vector integer_point
         (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
            pp_vector)
         points;
       let points = List.map (fun v dim -> V.coeff dim v) points in
       let dd = List.map (fun m -> LocalAbstraction.apply abstract_to_dd m plt1)
                  points
                |> List.fold_left DD.join dd1
       in
       (dd, fun interp -> univ_translation2 (univ_translation1 interp))
    
  let mk_sc_abstraction ~man
        expand_mod_floor srk terms symbols =
    let num_terms = Array.length terms in
    let plt_abstraction =
      Plt.abstract_to_standard_plt expand_mod_floor srk terms symbols
    in
    let sc_abstraction =
      SubspaceCone.abstract_sc ~man ~max_dim_in_projected:(num_terms - 1)
    in
    plt_abstraction |> LocalAbstraction.compose sc_abstraction

  let mk_sc_abstraction_with_acceleration ~man
        expand_mod_floor srk terms symbols =
    let models = ref [] in
    let plt_abstraction =
      Plt.abstract_to_standard_plt expand_mod_floor srk terms symbols
    in
    let dd_dimension = Array.length terms - 1 in
    let sc_abstraction =
      SubspaceCone.abstract_sc ~man ~max_dim_in_projected:dd_dimension
    in
    let abstract interp phi =
      models := interp :: !models;
      BatList.iter
        (fun interp ->
          assert (Interpretation.evaluate_formula interp phi)
        ) !models;
      abstract_multiple_models plt_abstraction sc_abstraction !models phi
    in
    LocalAbstraction.{abstract}

  let mk_cooper_abstraction expand_mod_floor srk terms symbols =
    let num_terms = Array.length terms in
    let plt_abstraction =
      Plt.abstract_to_standard_plt expand_mod_floor srk terms symbols in
    let cooper_abstraction =
      let elim dim = dim > num_terms in
      let ceiling _m v = (v, [], []) in
      plt_abstraction
      |> LocalAbstraction.compose
           (MixedCooper.abstract_cooper ~elim ~ceiling)
    in
    cooper_abstraction

  let mk_lw_cooper_abstraction ~man
        hull_after_proj expand_mod_floor srk terms symbols =
    let finalizer =
      match hull_after_proj with
      | `IntHullAfterProjection ->
         (fun _m dd ->
           logf ~level:`debug "convex_hull_lw_cooper: taking integer hull...";
           (DD.integer_hull dd, fun m -> m))
      | `NoIntHullAfterProjection ->
         (fun _m dd ->
           logf ~level:`debug "convex_hull_lw_cooper: done";
           (dd, fun m -> m))
    in
    let num_terms = Array.length terms in
    let local_abs =
      let open LocalAbstraction in
      logf ~level:`debug "convex_hull_lw_cooper...";
      Plt.abstract_to_standard_plt expand_mod_floor srk terms symbols
      |> compose (LwCooper.abstract_lw_cooper ~elim:(fun dim -> dim >= num_terms))
      |> compose (inject (fun _ plt -> (Plt.poly_part plt, fun m -> m)))
      |> compose (Ddify.abstract ~man ~max_dim_in_projected:(num_terms - 1))
      |> compose (inject finalizer)
    in
    local_abs

  let mk_map_intfrac_to_original_dimensions man terms =
    let num_terms = Array.length terms in
    let Plt.{start_of_term_int_frac; start_of_symbol_int_frac} =
      Plt.int_frac_layout ~num_terms
    in
    let defining_equations =
      let equations = BatEnum.empty () in
      let sum dim = V.of_term QQ.one dim |> V.add_term QQ.one (dim + 1)
      in
      let rec loop dim intfrac_dim =
        if dim < num_terms then
          begin
            BatEnum.push equations
              (`Zero, V.of_term (QQ.of_int (-1)) dim |> V.add (sum intfrac_dim));
            loop (dim + 1) (intfrac_dim + 2)
          end
        else
          ()
      in
      loop 0 start_of_term_int_frac;
      (BatList.of_enum equations)
    in
    let map_intfrac _m dd =
      let int_frac_term_dimensions =
        BatList.of_enum
          BatEnum.(num_terms --^ start_of_symbol_int_frac)
      in
      let mapped_dd = DD.meet_constraints dd defining_equations
                      |> DD.project int_frac_term_dimensions
                      |> DD.enum_constraints
                      |> DD.of_constraints_closed ~man num_terms
      in
      logf ~level:`debug "DD in original dimensions: @[%a@]@;"
        (DD.pp pp_dim) mapped_dd;
      ( mapped_dd
      , fun m dim ->
        if dim >= 0 && dim < num_terms then m dim
        else failwith "convex_hull_intfrac: dimension has been eliminated"
      )
    in
    map_intfrac

  let mk_intfrac_abstraction ~man
        expand_mod_floor srk terms symbols =
    let map_intfrac = mk_map_intfrac_to_original_dimensions man terms in
    let Plt.{start_of_symbol_int_frac; _} =
      Plt.int_frac_layout ~num_terms:(Array.length terms)
    in
    let max_dim_in_projected = start_of_symbol_int_frac - 1 in
    let local_abs =
      let open LocalAbstraction in
      Plt.abstract_to_intfrac_plt expand_mod_floor srk terms symbols
      |> compose
           (IntFracProjection.abstract_intfrac_plt
              ~elim:(fun dim -> dim > max_dim_in_projected))
      |> compose
           (SubspaceCone.abstract_sc ~man ~max_dim_in_projected)
      |> compose (inject map_intfrac)
    in
    local_abs

  let mk_intfrac_abstraction_with_acceleration ~man
    expand_mod_floor srk terms symbols =
    let map_intfrac = mk_map_intfrac_to_original_dimensions man terms in
    let Plt.{start_of_symbol_int_frac; _} =
      Plt.int_frac_layout ~num_terms:(Array.length terms)
    in
    let max_dim_in_projected = start_of_symbol_int_frac - 1 in
    let open LocalAbstraction in
    let abstract_to_plt =
      Plt.abstract_to_intfrac_plt expand_mod_floor srk terms symbols
    in
    let abstract_to_dd =
      IntFracProjection.abstract_intfrac_plt
        ~elim:(fun dim -> dim > max_dim_in_projected)
      |> compose (SubspaceCone.abstract_sc ~man ~max_dim_in_projected)
      |> compose (inject map_intfrac)
    in
    let models = ref [] in
    let abstract interp phi =
      models := interp :: !models;
      BatList.iter
        (fun interp ->
          assert (Interpretation.evaluate_formula interp phi)
        ) !models;
      abstract_multiple_models abstract_to_plt abstract_to_dd !models phi
    in
    LocalAbstraction.{abstract}

end

type standard = Plt.standard
type intfrac = Plt.intfrac
type 'a plt = 'a Plt.t

let formula_of_plt = Plt.formula_of_plt

let mk_term_of_dim terms dim =
  let num_terms = Array.length terms in
  if dim >= 0 && dim < num_terms then terms.(dim)
  else failwith (Format.asprintf "term_of_dim: %d" dim)

let cooper_project srk phi terms =
  let local_abs = AbstractTerm.mk_cooper_abstraction `ExpandModFloor
                    srk terms (Syntax.symbols phi) in
  let abstract =
    LocalGlobal.lift_plt_abstraction srk ~term_of_dim:(mk_term_of_dim terms)
      local_abs
  in
  Abstraction.apply abstract phi

let sc_abstraction_of solver man terms model =
  let phi = Abstract.Solver.get_formula solver in
  let srk = Abstract.Solver.get_context solver in
  let local_abs = AbstractTerm.mk_sc_abstraction ~man `ExpandModFloor
                      srk terms (Syntax.symbols phi) in
  LocalAbstraction.apply local_abs model phi

let lw_cooper_abstraction_of finalize solver man terms model =
  let phi = Abstract.Solver.get_formula solver in
  let srk = Abstract.Solver.get_context solver in
  let local_abs =
    AbstractTerm.mk_lw_cooper_abstraction ~man finalize `ExpandModFloor srk
      terms (Syntax.symbols phi)
  in
  LocalAbstraction.apply local_abs model phi

let intfrac_abstraction_of solver man terms model =
  let phi = Abstract.Solver.get_formula solver in
  let srk = Abstract.Solver.get_context solver in
  let local_abs =
    AbstractTerm.mk_intfrac_abstraction ~man `ExpandModFloor srk
      terms (Syntax.symbols phi)
  in
  LocalAbstraction.apply local_abs model phi

let convex_hull_of_lira_model how solver man terms model =
  let m = match model with
    | `LIRA m -> m
    | `LIRR _ -> invalid_arg "Unsupported"
  in
  match how with
  | `SubspaceCone -> sc_abstraction_of solver man terms m
  | `IntFrac -> intfrac_abstraction_of solver man terms m
  | `LwCooper finalizer ->
     begin
       match finalizer with
       | `IntHullAfterProjection ->
          lw_cooper_abstraction_of `IntHullAfterProjection solver man terms m
       | `NoIntHullAfterProjection ->
          lw_cooper_abstraction_of `NoIntHullAfterProjection solver man terms m
     end

let convex_hull_sc ?(man=Polka.manager_alloc_loose()) speed srk phi terms =
  let local_abs =
    match speed with
    | `SingleModel ->
       AbstractTerm.mk_sc_abstraction ~man
         `ExpandModFloor srk terms (Syntax.symbols phi)
    | `Accelerate ->
       AbstractTerm.mk_sc_abstraction_with_acceleration ~man
         `ExpandModFloor srk terms (Syntax.symbols phi)
  in
  let num_terms = Array.length terms in
  let abstract =
    LocalGlobal.lift_dd_abstraction srk ~man ~max_dim:(num_terms - 1)
      ~term_of_dim:(mk_term_of_dim terms)
      local_abs
  in
  Abstraction.apply abstract phi

let convex_hull_intfrac ?(man=(Polka.manager_alloc_loose ())) speed srk phi terms =
  let num_terms = Array.length terms in
  let local_abs =
    match speed with
    | `SingleModel ->
       AbstractTerm.mk_intfrac_abstraction ~man `ExpandModFloor srk terms
         (Syntax.symbols phi)
    | `Accelerate ->
       AbstractTerm.mk_intfrac_abstraction_with_acceleration
         ~man `ExpandModFloor srk terms (Syntax.symbols phi)
  in
  let abstract =
    LocalGlobal.lift_dd_abstraction srk ~man ~max_dim:(num_terms - 1)
      ~term_of_dim:(mk_term_of_dim terms) local_abs
  in
  let projected_dd_in_original_dims = Abstraction.apply abstract phi in
  logf ~level:`debug "convex_hull_intfrac result: @[%a@]" (DD.pp pp_dim)
    projected_dd_in_original_dims;
  projected_dd_in_original_dims

let convex_hull_lw_cooper ?(man=(Polka.manager_alloc_loose ()))
      hull_after_proj srk phi terms =
  let num_terms = Array.length terms in
  let local_abs =
    AbstractTerm.mk_lw_cooper_abstraction ~man hull_after_proj `ExpandModFloor
      srk terms (Syntax.symbols phi) in
  let abstract =
    LocalGlobal.lift_dd_abstraction srk ~man
      ~max_dim:(num_terms - 1) ~term_of_dim:(mk_term_of_dim terms) local_abs
  in
  Abstraction.apply abstract phi

let convex_hull how ?(man=(Polka.manager_alloc_loose ())) srk phi terms =
  match how with
  | `SubspaceCone -> convex_hull_sc ~man `SingleModel srk phi terms
  | `SubspaceConeAccelerated -> convex_hull_sc ~man `Accelerate srk phi terms
  | `IntFrac -> convex_hull_intfrac ~man `SingleModel srk phi terms
  | `IntFracAccelerated -> convex_hull_intfrac ~man `Accelerate srk phi terms
  | `LwCooper finalize -> convex_hull_lw_cooper finalize ~man srk phi terms

let convex_hull_lia srk phi terms =
  convex_hull (`LwCooper `IntHullAfterProjection) srk phi terms

let convex_hull_lra srk phi terms =
  convex_hull (`LwCooper `NoIntHullAfterProjection) srk phi terms
