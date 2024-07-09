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

let sharpen_strict_inequalities_assuming_integrality p =
  let cnstrnts = BatEnum.empty () in
  BatEnum.iter (fun (kind, v) ->
      match kind with
      | `Pos ->
         let sharpened =
           V.scalar_mul (QQ.of_zz (V.common_denominator v)) v
           |> V.add_term (QQ.of_int (-1)) Linear.const_dim
         in
         BatEnum.push cnstrnts (`Nonneg, sharpened)
      | _ -> BatEnum.push cnstrnts (kind, v)
    )
    (P.enum_constraints p);
  cnstrnts

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

  (* val subset: 'layout t -> 'layout t -> bool *)

  val int_frac_layout: num_terms:int -> intfrac

  val top: 'layout t

  val formula_of_plt:
    'a context -> (int -> 'a arith_term) -> 'layout t -> 'a formula

  val constrained_dimensions: 'layout t -> IntSet.t

  val ceiling_int_frac:
    (int -> QQ.t) -> V.t -> (V.t * (P.constraint_kind * V.t) list * V.t list)

  (* An expansion defines how terms are expanded into vectors;
     floor and modulo terms correspond to fresh dimensions starting at free_dim.
   *)

  type 'a expansion

  val mk_standard_expansion:
    'a Syntax.context -> dim_of_symbol:(Syntax.symbol -> int) -> free_dim:int -> 'a expansion

  (* TODO: Remove this and use the interfaces below. *)
  val abstract_to_plt:
    'a expansion ->
    'a context ->
    ?term_of_new_dims_to_set:(('a Syntax.arith_term) IntMap.t) ref option ->
    ?universe_p:(P.constraint_kind * V.t) list ->
    ?universe_l:V.t list ->
    ?universe_t:V.t list ->
    ('a Interpretation.interpretation -> int -> Q.t) ->
    ('a formula, 'a Interpretation.interpretation, 'b t, int -> Q.t)
      LocalAbstraction.t

  (** A standard PLT lives in a space where dimensions are partitioned into
      three parts:
      - Dimensions i between 0 to (Array.length terms) exclusive correspond to
        term i in the term array.
      - Dimensions i from Array.length terms to 
        Array.length terms + max int_of_symbol over symbols correspond to symbol
        (i - Array.length terms)
      - "New dimensions" that start from the maximum of
        (Array.length terms + max int_of_symbol over symbols + 1) and 
        the largest dimension in the support of [term_of_new_dims_to_set].

      Each time the local abstraction is applied, [term_of_new_dims_to_set] is
      extended with term definitions for new dimensions that are introduced
      in the space that the output PLT lives in.
   *)
  val abstract_to_standard_plt:
    [`ExpandModFloor | `NoExpandModFloor] ->
    'a context ->
    ?term_of_new_dims_to_set:(('a Syntax.arith_term) IntMap.t) ref option ->
    'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, standard t, int -> Q.t)
      LocalAbstraction.t

  val abstract_to_intfrac_plt:
    [`ExpandModFloor | `NoExpandModFloor] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, intfrac t, int -> Q.t)
      LocalAbstraction.t

  val mk_standard_term_definitions:
    'a context -> (symbol -> int) -> 'a ArithTerm.t array ->
    (P.constraint_kind * V.t) list * V.t list * V.t list

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

  (*
  let subset plt1 plt2 =
    let (p1, p2) = (poly_part plt1, poly_part plt2) in
    let (lattice1, lattice2) = (lattice_part plt1, lattice_part plt2) in
    let (tiling1, tiling2) = (tiling_part plt1, tiling_part plt2) in
    let poly_subset p1 p2 =
      BatEnum.for_all (fun cnstrnt -> P.implies p1 cnstrnt)
        (P.enum_constraints p2)
    in
    poly_subset p1 p2 &&
      IntLattice.subset lattice2 lattice1 &&
        IntLattice.subset tiling2 tiling1
   *)

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

  let lift_binop op (v1, lin1) (v2, lin2) =
    (op v1 v2, conjoin lin1 lin2)

  (*
  type term_vector =
    | TV_real of QQ.t
    | TV_mod of V.t * QQ.t
    | TV_floor of V.t
   *)

  let lin_mod
        ~vec_of_free_dim
        ~int_cond
        ~next_free_dim
        ~add_term_of_dim
        srk
        ~free_dim term_of_dim v1 v2 t1 t2 =
    let modulus =
      try real_of v2 with
      | Invalid_argument _ -> raise Linear.Nonlinear
    in
    let () =
      if QQ.equal modulus QQ.zero then invalid_arg "Division by zero"
      else ()
    in
    let quotient = vec_of_free_dim free_dim in
    logf ~level:`debug
      "lin_mod: introducing dimension %d for quotient in @[%a@] modulo %a (@[%a@] modulo %a)"
      free_dim pp_vector v1 QQ.pp modulus
      (ArithTerm.pp srk) t1 (ArithTerm.pp srk) t2;
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
    let quotient_term =
      mk_div srk (mk_sub srk t1 (mk_mod srk t1 t2)) t2 in
    ( remainder
    , lincond
    , next_free_dim free_dim
    , add_term_of_dim free_dim quotient_term term_of_dim
    )

  let lin_floor
        ~vec_of_free_dim ~int_cond ~next_free_dim ~add_term_of_dim
        srk ~free_dim term_of_dim v t =
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
    , add_term_of_dim free_dim (Syntax.mk_floor srk t) term_of_dim
    )

  type 'a expand_mod_floor =
    | NoExpansion
    | Expand_mod_floor_with of
        { free_dim: int
        ; new_dimensions: ('a Syntax.arith_term) IntMap.t
        ; linearize_mod: 'a Syntax.context -> free_dim:int -> ('a Syntax.arith_term) IntMap.t ->
                         V.t -> V.t -> ('a Syntax.arith_term) -> ('a Syntax.arith_term) ->
                         (V.t * lin_cond * int * ('a Syntax.arith_term) IntMap.t)
        ; linearize_floor: 'a Syntax.context -> free_dim:int -> ('a Syntax.arith_term) IntMap.t ->
                           V.t -> 'a Syntax.arith_term ->
                           (V.t * lin_cond * int * ('a Syntax.arith_term) IntMap.t)
        }

  type 'a expansion =
    {
      vec_of_symbol: Syntax.symbol -> V.t
    ; translate_int_atom: [`IsInt | `NotInt] -> (int -> QQ.t) -> V.t -> lin_cond
    (* TODO: one more way of translating an int_atom is to replace the term 
       inside with a fresh dimension, i.e.,
       for `IsInt, add a new equation defining a new dimension and add the 
       dimension to the lattice,
       and for `NotInt, add a new inequality b < t < b + 1 and dimension b to
       the lattice.
       So [translate_int_atom] should have a signature like [linearize_floor].
     *)
    ; expand_mod_floor: 'a expand_mod_floor
    }

  let expand_univ_translation univ_translation interp new_dimensions initial =
    let extend m new_dimensions dim =
      try
        begin
          let term = IntMap.find dim new_dimensions in
          Interpretation.evaluate_term interp term
        end
      with
      | Not_found -> m dim
    in
    let next = univ_translation initial in
    extend next new_dimensions

  let floor_int_frac m v =
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

  let mk_expansion srk expand layout dim_of_symbol =
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
          IntMap.add free_dim term map |> IntMap.add (free_dim + 1) (Syntax.mk_real srk QQ.zero)
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

  let mk_standard_expansion srk ~dim_of_symbol ~free_dim =
    mk_expansion srk (`Expand free_dim) `Standard dim_of_symbol

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
         , (fun _srk ~free_dim _term_of_dim -> ignore free_dim; invalid_arg "mod term in formula")
         , (fun _srk ~free_dim _term_of_dim -> ignore free_dim; invalid_arg "floor term in formula")
         )
    in
    let (linearized, cond, _term) =
      ArithTerm.eval srk (function
          | `Real r -> (Linear.const_linterm r, tru, mk_real srk r)
          | `App (x, []) -> (vec_of_symbol x, tru, mk_const srk x)
          | `App (_f, _xs) -> raise Linear.Nonlinear
          | `Var (_i, _typ) -> raise Linear.Nonlinear
          | `Add lincondterms ->
             let linconds =
               List.map (fun (lin, cond, _term) -> (lin, cond)) lincondterms
             in
             let (lin, cond) = List.fold_left (lift_binop V.add) (V.zero, tru)
                                 linconds
             in
             (lin, cond, Syntax.mk_add srk (List.map (fun (_, _, term) -> term) lincondterms))
          | `Mul lincondterms ->
             let linconds =
               List.map (fun (lin, cond, _term) -> (lin, cond)) lincondterms
             in
             let (lin, cond) =
               List.fold_left (lift_binop mul_vec) (Linear.const_linterm QQ.one, tru)
                 linconds
             in
             (lin, cond, Syntax.mk_mul srk (List.map (fun (_, _, term) -> term) lincondterms))
          | `Binop (`Div, lincondterm1, lincondterm2) ->
             begin
               let (lin1, cond1, term1) = lincondterm1 in
               let (lin2, cond2, term2) = lincondterm2 in
               let lincond1, lincond2 = (lin1, cond1), (lin2, cond2) in
               let divide v1 v2 =
                 let divisor = try real_of v2 with | Invalid_argument _ -> raise Linear.Nonlinear
                 in
                 if QQ.equal divisor QQ.zero then invalid_arg "Division by zero"
                 else
                   V.scalar_mul (QQ.inverse divisor) v1
               in
               let (div_v, lincond) = (lift_binop divide) lincond1 lincond2 in
               (div_v, lincond, Syntax.mk_div srk term1 term2)
             end
          | `Binop (`Mod, (v1, cond1, t1), (v2, cond2, t2)) ->
             let (mod_v, cond, next_free_dim, next_term_of_dim) =
               lin_mod srk ~free_dim:!curr_free_dim !curr_term_of_dim v1 v2 t1 t2
             in
             let lincond = (conjoin cond2 cond1)
                           |> conjoin cond
             in
             curr_free_dim := next_free_dim;
             curr_term_of_dim := next_term_of_dim;
             (mod_v, lincond, Syntax.mk_mod srk t1 t2)
          | `Unop (`Floor, (v, cond, term)) ->
             let (floor_v, floor_cond, next_free_dim, next_term_of_dim) =
               lin_floor srk ~free_dim:!curr_free_dim !curr_term_of_dim v term
             in
             let lincond_floor = conjoin floor_cond cond in
             curr_free_dim := next_free_dim;
             curr_term_of_dim := next_term_of_dim;
             (floor_v, lincond_floor, Syntax.mk_floor srk term)
          | `Unop (`Neg, (v, lincond, term)) ->
             (V.negate v, lincond, Syntax.mk_neg srk term)
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
         (expand_univ_translation univ_translation interp new_dimensions) interp
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
        ?(term_of_new_dims_to_set = None)
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
           let () =
             match term_of_new_dims_to_set with
             | None -> ()
             | Some term_of_dim ->
                term_of_dim :=
                  IntMap.union
                    (fun dim _ _ ->
                      failwith
                        (Format.asprintf
                           "expansion overlaps with existing dimensions in dimension %d"
                           dim)
                    ) !term_of_dim new_dimensions
           in
           expand_univ_translation univ_translation interp new_dimensions
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
      BatEnum.map (formula_p srk term_of_dim) (P.enum_constraints plt.poly_part)
      |> BatList.of_enum
    in
    let phis_l =
      List.map (formula_l srk term_of_dim) (L.basis plt.lattice_part)
    in
    let phis_t =
      List.map (formula_t srk term_of_dim) (L.basis plt.tiling_part)
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
         linearize_term srk (mk_expansion srk `NoExpand `Standard dim_of_symbol)
      | `IntFrac ->
         linearize_term srk (mk_expansion srk `NoExpand `IntFrac dim_of_symbol)
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

  let mk_standard_term_definitions srk dim_of_symbol terms =
    mk_term_definitions `Standard srk dim_of_symbol terms

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

  let abstract_to_standard_plt
        has_mod_floor srk ?(term_of_new_dims_to_set = None) terms symbols =
    let num_terms = Array.length terms in
    let max_dim = get_max_dim `Standard num_terms symbols in
    logf ~level:`debug "initial plt abstraction: max_dim: %d, num_terms = %d@;"
      max_dim num_terms;
    let dim_of_symbol sym = Syntax.int_of_symbol sym + num_terms in
    let free_dim =
      match term_of_new_dims_to_set with
      | None -> max_dim + 1
      | Some term_of_new_dims ->
         begin match IntMap.max_binding_opt !term_of_new_dims with
         | None -> max_dim + 1
         | Some (dim, _) -> (Int.max max_dim dim) + 1
         end
    in
    let expansion =
      let expand = match has_mod_floor with
        | `NoExpandModFloor -> `NoExpand
        | `ExpandModFloor -> `Expand free_dim
      in
      mk_expansion srk expand `Standard dim_of_symbol
    in
    let (universe_p, universe_l, universe_t) =
      mk_term_definitions `Standard srk dim_of_symbol terms in
    logf ~level:`debug "abstract_to_standard_plt...";
    log_plt_constraints ~level:`debug "term definitions" (universe_p, universe_l, universe_t);
    let interp_dim = mk_interp_dim `Standard terms in
    abstract_to_plt expansion srk ~term_of_new_dims_to_set
      ~universe_p ~universe_l ~universe_t interp_dim

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
      mk_expansion srk expand `IntFrac int_dim_of_symbol
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

module LocalGlobal: sig

  open Syntax
  open Interpretation

  val localize:
    ('concept1, 'point1, 'concept2, 'point2) Abstraction.t ->
    ('concept1, 'point1, 'concept2, 'point2) LocalAbstraction.t

  (* TODO: [solver] should hold the formula (concept) that the 
     output abstraction abstracts,
     but a local abstraction and an abstraction should abstract arbitrary 
     concepts. This signature doesn't make sense.
   *)

  val lift_abstraction:
    ?show:('a interpretation -> unit) ->
    ?solver: 'a Abstract.Solver.t option ->
    'a context ->
    join:('concept2 -> 'concept2 -> 'concept2) ->
    formula_of_source:('concept1 -> 'a formula) ->
    univ_translation:('a Interpretation.interpretation -> 'point1) ->
    formula_of_target:('concept2 -> 'a formula) ->
    top:'concept2 ->
    bottom:'concept2 ->
    ('concept1, 'point1, 'concept2, 'point2) LocalAbstraction.t ->
    ('concept1, 'point1, 'concept2, 'point2) Abstraction.t

  val lift_dd_abstraction:
    ?solver: 'a Abstract.Solver.t option ->
    ?bottom: DD.closed DD.t option ->
    man:(DD.closed Apron.Manager.t) ->
    'a context -> max_dim:int -> term_of_dim:(int -> 'a Syntax.arith_term) ->
    ('a formula, 'a interpretation, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t ->
    ('a formula, 'a interpretation, DD.closed DD.t, int -> QQ.t) Abstraction.t

  val lift_plt_abstraction:
    ?solver: 'a Abstract.Solver.t option ->
    'a context -> term_of_dim:(int -> 'a Syntax.arith_term) ->
    ('a formula, 'a interpretation, 'layout Plt.t, int -> QQ.t) LocalAbstraction.t ->
    ('a formula, 'a interpretation, 'layout Plt.t list, int -> QQ.t) Abstraction.t

end = struct

  open Syntax

  let localize
        (abstraction : ('concept1, 'point1, 'concept2, 'point2) Abstraction.t) =
    LocalAbstraction.
    { abstract = (fun _x c -> abstraction.abstract c) }

  let dump_model_up_to srk term_of_dim max_dim_to_inspect interp =
    let rec evaluate n l =
      if n < 0 then l
      else
        let term = term_of_dim n in
        let l' = (term, Interpretation.evaluate_term interp term) :: l in
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

  let lift_abstraction ?(show=(fun _m -> ()))
        ?(solver=None)
        (srk: 'a context) ~join ~formula_of_source ~univ_translation
        ~formula_of_target ~top ~bottom
        local_abs =
    let counter = ref 0 in
    let of_model src m =
      match m with
      | `LIRR _ -> assert false
      | `LIRA m ->
         let () = show m in
         logf ~level:`info "Abstraction loop iteration: %d" !counter;
         counter := !counter + 1;
         let result = LocalAbstraction.apply local_abs (univ_translation m) src in
         logf ~level:`info "Abstraction loop iteration %d done" (!counter - 1);
         result
    in
    let abstract src =
      let domain =
        Abstract.
        { join
        ; of_model = of_model src
        ; formula_of = formula_of_target
        ; top
        ; bottom
        }
      in
      let solver =
        match solver with
        | None -> Abstract.Solver.make srk ~theory:`LIRA (formula_of_source src)
        | Some solver -> solver
      in
      ( Abstract.Solver.abstract solver domain
      , (fun m ->
          let (_, univ_translation') = LocalAbstraction.apply2 local_abs m src in
          logf ~level:`debug
            "Warning: universe translation should be constant for lifting to be sound";
          univ_translation' m)
      )
    in
    Abstraction.{abstract}

  let lift_dd_abstraction ?(solver=None) ?(bottom=None) ~man
        (srk: 'a context) ~max_dim ~term_of_dim
        local_abs =
    let ambient_dim = max_dim + 1 in
    let formula_of_target dd =
      let fml = formula_of_dd srk term_of_dim dd in
      logf ~level:`debug "Blocking %a" (Syntax.Formula.pp srk) fml;
      fml
    in
    let top = P.dd_of ~man ambient_dim P.top in
    let bottom = match bottom with
      | None -> P.dd_of ~man ambient_dim P.bottom
      | Some bottom -> bottom
    in
    lift_abstraction ~show:(dump_model_up_to srk term_of_dim max_dim)
      ~solver
      srk ~join:DD.join
      ~formula_of_source:(fun phi -> phi)
      ~univ_translation:(fun interp -> interp)
      ~formula_of_target ~top ~bottom local_abs

  let lift_plt_abstraction ?(solver=None) srk ~term_of_dim local_abs =
    let local_abs' =
      let abstract m phi =
        let ((plt: 'b Plt.t), univ_translation) =
          local_abs.LocalAbstraction.abstract m phi in
        ([plt], univ_translation)
      in
      LocalAbstraction.{abstract}
    in
    let join plts1 plts2 = plts1 @ plts2 in
    let formula_of_target plts =
      let to_block = mk_or srk (List.map (Plt.formula_of_plt srk term_of_dim) plts) in
      logf ~level:`debug "blocking: @[%a@]" (Syntax.Formula.pp srk) to_block;
      to_block
    in
    let top = [Plt.top] in
    let bottom = [] in
    lift_abstraction srk ~solver ~join
      ~formula_of_source:(fun phi -> phi) ~univ_translation:(fun interp -> interp)
      ~formula_of_target ~top ~bottom local_abs'

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

(*
module UnionPlt : sig

  type 'layout t

  val plt_and_points: 'layout t -> ('layout Plt.t * ) list

  val abstract_to_union_plt:
    'a context -> 'a Syntax.ArithTerm.t array -> 
    (('a Syntax.Formula.t, 'a Interpretation.interpretation,
      'layout t, (int -> QQ.t)) Abstraction.t) *
      (int -> 'a Syntax.ArithTerm.t)
    
end = struct

  val lift_abstraction:
    ?show:('a interpretation -> unit) ->
    ?solver: 'a Abstract.Solver.t option ->
    'a context ->
    join:('concept2 -> 'concept2 -> 'concept2) ->
    formula_of_source:('concept1 -> 'a formula) ->
    univ_translation:('a Interpretation.interpretation -> 'point1) ->
    formula_of_target:('concept2 -> 'a formula) ->
    top:'concept2 ->
    bottom:'concept2 ->
    ('concept1, 'point1, 'concept2, 'point2) LocalAbstraction.t ->
    ('concept1, 'point1, 'concept2, 'point2) Abstraction.t

  type 'layout t = ('layout Plt.t * (int -> QQ.t) list) list

  let adjoin plt_points plts =
    let (plt1, points1) = plt_points in
    List.fold_left 
      (fun (plt2, pts2) -> )
      []
      plts
      

  (* Best-effort join *)
  let join union1 union2 =
    List.fold_left
      (fun plt1 )
      []
      union1
                 

  let abstract_to_union_plt srk terms symbols =
    let curr_term_of_dim = ref IntMap.empty in
    let num_terms = Array.length terms in
    let () =
      Array.iteri
        (fun dim term -> curr_term_of_dim := IntMap.add dim term !curr_term_of_dim)
        terms;
      Syntax.Symbol.Set.iter
        (fun sym ->
          curr_term_of_dim :=
            IntMap.add
              (Syntax.int_of_symbol sym + num_terms)
              (Syntax.mk_const srk sym)
              !curr_term_of_dim
        )
        symbols
    in
    let abstract_plt =
      Plt.abstract_to_standard_plt `ExpandModFloor srk
        ~term_of_new_dims_to_set:(Some curr_term_of_dim)
        terms
        symbols
    in
    let mk_univ_translation term_of_dim =
      fun interp dim ->
      try
        let term = IntMap.find dim term_of_dim in
        Interpretation.evaluate_term interp term
      with
      | Not_found ->
         failwith
           (Format.asprintf "abstract_to_union_plt: cannot evaluate dimension %d" dim)
    in
    let alpha interp phi =
      let plt = LocalAbstraction.apply abstract_plt interp phi in
      let univ_translation = mk_univ_translation !curr_term_of_dim in
      ((plt, univ_translation interp), univ_translation)
    in
    let term_of_dim dim =
      try IntMap.find dim !curr_term_of_dim
      with
      | Not_found ->
         failwith
           (Format.asprintf "abstract_to_union_plt: cannot find a term at dimension %d" dim)
    in
    let join plts1 plts2 = plts1 @ plts2 in
    let formula_of_target plts =
      let to_block =
        mk_or srk (List.map (Plt.formula_of_plt srk term_of_dim) plts) in
      logf ~level:`debug "blocking: @[%a@]" (Syntax.Formula.pp srk) to_block;
      to_block
    in
    let top = [Plt.top] in
    let bottom = [] in
    let abstract = LocalGlobal.lift_abstraction srk ~join
                     ~formula_of_source:(fun phi -> phi)
                     ~formula_of_target
                     ~top ~bottom
                     LocalAbstraction.{abstract=alpha}
    in
    (abstract, term_of_dim)

end
 *)

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

  (* Let PLT(x, Y) be a PLT in dimensions R^{x \cup Y}.
     [round_up: Q^{x \cup Y} -> Term(Y) -> Term(Y)] is a function such that
     for all terms [t], [t'] and [m] in PLT(x, Y),
     [round_up m t = t'] only if m(t(y)) <= m(t'(y)) <= m(x).

     If [ceiling] has finite image for each [t], [abstract_cooper] is a
     local abstraction that has finite image.
   *)

  (* Dimensions to be eliminated must take on only integer values in the
     universe.
   *)
  val abstract_cooper:
    elim: (int -> bool) ->
    round_up: ((int -> QQ.t) -> V.t -> V.t) ->
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
  let virtual_sub_l modulus m vt dim v =
    let (coeff, _) = V.pivot dim v in
    if QQ.equal coeff QQ.zero then Some v
    else
      match vt with
      | `PlusInfinity
        | `MinusInfinity ->
         let delta = QQ.modulo (m dim) modulus in
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

  let select_term elim_dim modulus round_up (kind, lower) m =
    let rounded = round_up m lower in
    let lower_point = Linear.evaluate_affine m lower in
    let rounded_point = Linear.evaluate_affine m rounded in
    let remainder = QQ.modulo (QQ.sub (m elim_dim) rounded_point) modulus in
    let delta = match (kind, QQ.equal QQ.zero remainder) with
      | (`Zero, _)
        | (`Nonneg, _)
        | (`Pos, false) -> remainder
      | (`Pos, true) ->
         assert (QQ.leq lower_point rounded_point);
         if QQ.lt lower_point rounded_point then QQ.zero
         else modulus
    in
    let term = V.add_term delta Linear.const_dim rounded in
    logf ~level:`debug
      "select_term: calculating term: value of elim dimension %d = %a,
       value of lower bound = %a, value of rounded = %a,
       modulus = %a, remainder = %a, chosen point = %a@;"
      elim_dim
      QQ.pp (m elim_dim)
      QQ.pp (Linear.evaluate_affine m lower)
      QQ.pp (Linear.evaluate_affine m rounded)
      QQ.pp modulus
      QQ.pp remainder
      QQ.pp (QQ.add rounded_point delta);
    logf ~level:`debug
      "select_term: lower bound term: @[%a@]@; rounded term: @[%a@]@; selected term: @[%a@]"
      pp_vector lower pp_vector rounded pp_vector term;
    term

  let cooper_one round_up elim_dim m (p, l, t) =
    logf ~level:`debug "cooper_one: eliminating %d" elim_dim;
    let gcd_coeffs =
      List.fold_left (fun gcd v -> QQ.gcd (V.coeff elim_dim v) gcd) QQ.zero
        (List.rev_append l t)
    in
    let modulus =
      (* Better than just lcm of denoms, e.g., smaller steps for coeffs 5/2, 5/3 *)
      assert (not (QQ.equal QQ.zero gcd_coeffs));
      QQ.inverse gcd_coeffs
    in
    let select_term = select_term elim_dim modulus round_up in
    let term_selected =
      match glb_for elim_dim p m with
      | (_, false) ->
         logf ~level:`debug "abstract_cooper: selecting +infty";
         `PlusInfinity
      | (None, _) ->
         logf ~level:`debug "abstract_cooper: selecting -infty";
         `MinusInfinity
      | (Some (kind, term, _value), true) ->
         logf ~level:`debug "abstract_cooper: selecting term based on @[%a@]"
           pp_pconstr (kind, V.add_term QQ.one elim_dim (V.negate term));
         `Term (select_term (kind, term) m)
    in
    let polyhedron = virtual_sub virtual_sub_p term_selected elim_dim p in
    let virtual_sub_lattice = virtual_sub (virtual_sub_l modulus m) in
    let lattice = virtual_sub_lattice term_selected elim_dim l in
    let tiling = virtual_sub_lattice term_selected elim_dim t in
    test_point_in_polyhedron "cooper_one" m polyhedron;
    test_point_in_lattice `IsInt "cooper_one" m lattice;
    test_point_in_lattice `NotInt "cooper_one" m tiling;
    (polyhedron, lattice, tiling)

  let abstract_cooper_ ~elim ~round_up m plt =
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
          cooper_one round_up elim_dim m (p, l, t)
        )
        elim_dimensions
        (p, l, t)
    in
    logf ~level:`debug "abstract_cooper: abstracted";
    mk_plt ~poly_part:(Polyhedron.of_constraints (BatList.enum projected_p))
      ~lattice_part:(L.hermitize projected_l)
      ~tiling_part:(L.hermitize projected_t)

  let abstract_cooper ~elim ~round_up =
    let restricted m dim =
      if elim dim then failwith "abstract_cooper: Dimension has been eliminated"
      else m dim
    in
    LocalAbstraction.
    {
      abstract =
        (fun m plt -> (abstract_cooper_ ~elim ~round_up m plt, restricted))
    }

end

module SubspaceCone : sig

  val abstract_sc:
    man:DD.closed Apron.Manager.t ->
    max_dim_in_projected: int ->
    ('layout Plt.t, int -> QQ.t, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t

  (* For testing only *)
  val abstract_subspace:
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

  let abstract_subspace ~man ~max_dim_in_projected =
    let abstract m plt =
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
      let restricted m dim =
        if dim > max_dim_in_projected
        then failwith "abstract_sc: Dimension has been eliminated"
        else m dim
      in
      (subspace_abstraction, restricted)
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
          ~round_up:(fun m t -> let (t', _, _) = Plt.ceiling_int_frac m t in t')
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
    let abstract_cooper =
      MixedCooper.abstract_cooper
        ~elim:(fun dim -> IntSet.mem dim int_dims_to_elim)
        ~round_up:(fun _ v -> v)
    in
    let local_abstraction =
      Plt.abstract_poly_part abstract_lw
      |> LocalAbstraction.compose abstract_cooper
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

  (* To remove *)
  val mk_subspace_abstraction_with_acceleration:
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
    [ `IntRealHullAfterProjection
    | `IntHullAfterProjection
    | `NoIntHullAfterProjection] ->
    [ `ExpandModFloor | `NoExpandModFloor ] ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> Q.t)
      LocalAbstraction.t

  val mk_lw_abstraction:
    man:DD.closed Apron.Manager.t ->
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

  (* TODO: Refactor this and abstract_multiple_models *)
  let abstract_multiple_points local_abs plt points =
    match points with
    | [] -> invalid_arg "at least one point is needed"
    | [point] -> LocalAbstraction.apply2 local_abs point plt
    | point1 :: point2 :: _ ->
       let dimensions = Plt.constrained_dimensions plt in
       let integer_point = ModelSearch.model_to_vector dimensions point1 in
       let rational_point = ModelSearch.model_to_vector dimensions point2 in
       let points =
         let direction = V.sub rational_point integer_point in
         ModelSearch.extrapolate ~integer_point ~direction plt
       in
       log_plt_constraints ~level:`debug "diversifying within"
         ( BatList.of_enum (P.enum_constraints (Plt.poly_part plt))
         , L.basis (Plt.lattice_part plt)
         , L.basis (Plt.tiling_part plt));
       logf ~level:`debug "diversified points: @[%a@]@\n@[%a@]@;"
         pp_vector integer_point
         (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
            pp_vector)
         points;
       let points = List.map (fun v dim -> V.coeff dim v) points in
       let (dd1, univ_translation) =
         LocalAbstraction.apply2 local_abs point1 plt in
       let dd = List.map (fun m -> LocalAbstraction.apply local_abs m plt)
                  points
                |> List.fold_left DD.join dd1
       in
       (dd, univ_translation)

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

  let mk_subspace_abstraction_with_acceleration ~man
        expand_mod_floor srk terms symbols =
    let models = ref [] in
    let plt_abstraction =
      Plt.abstract_to_standard_plt expand_mod_floor srk terms symbols
    in
    let dd_dimension = Array.length terms - 1 in
    let subspace_abstraction =
      SubspaceCone.abstract_subspace ~man ~max_dim_in_projected:dd_dimension
    in
    let abstract interp phi =
      models := interp :: !models;
      BatList.iter
        (fun interp ->
          assert (Interpretation.evaluate_formula interp phi)
        ) !models;
      abstract_multiple_models plt_abstraction subspace_abstraction !models phi
    in
    LocalAbstraction.{abstract}

  let mk_cooper_abstraction expand_mod_floor srk terms symbols =
    let num_terms = Array.length terms in
    let plt_abstraction =
      Plt.abstract_to_standard_plt expand_mod_floor srk terms symbols in
    let cooper_abstraction =
      let elim dim = dim > num_terms in
      let round_up _m v = v in
      plt_abstraction
      |> LocalAbstraction.compose
           (MixedCooper.abstract_cooper ~elim ~round_up)
    in
    cooper_abstraction

  let integer_real_hull ~man srk terms =
    let num_terms = Array.length terms in
    let accelerated_sc_abstraction =
      let abstract_sc =
        SubspaceCone.abstract_sc ~man ~max_dim_in_projected:(num_terms-1)
      in
      let points = ref [] in
      let abstract point plt =
        points := point :: !points;
        abstract_multiple_points abstract_sc plt !points
      in
      LocalAbstraction.{abstract}
    in
    let abs =
      LocalGlobal.lift_abstraction
        srk ~join:DD.join
        ~formula_of_source:(Plt.formula_of_plt srk (fun dim -> terms.(dim)))
        ~univ_translation:(fun interp dim -> Interpretation.evaluate_term interp terms.(dim))
        ~formula_of_target:(formula_of_dd srk (fun dim -> terms.(dim)))
        ~top:(P.dd_of ~man num_terms P.top)
        ~bottom:(P.dd_of ~man num_terms P.bottom)
        (* (SubspaceCone.abstract_sc ~man ~max_dim_in_projected:(num_terms-1)) *)
        accelerated_sc_abstraction
    in
    abs

  let mk_lw_cooper_abstraction ~man
        hull_after_proj expand_mod_floor srk terms symbols =
    let num_terms = Array.length terms in
    let finalizer =
      match hull_after_proj with
      | `IntRealHullAfterProjection ->
         (fun _m plt ->
           (Abstraction.apply (integer_real_hull ~man srk terms) plt, (fun m -> m)))
      | `IntHullAfterProjection ->
         (fun _m plt ->
           let p = Plt.poly_part plt in
           let cnstrnts = sharpen_strict_inequalities_assuming_integrality p in
           let dd = DD.of_constraints_closed ~man num_terms cnstrnts in
           logf ~level:`debug
             "convex_hull_lw_cooper: taking integer hull assuming all remaining
              variables are integral...";
           (DD.integer_hull dd, fun m -> m))
      | `NoIntHullAfterProjection ->
         (fun _m plt ->
           let dd = P.dd_of ~man num_terms (Plt.poly_part plt) in
           logf ~level:`debug "convex_hull_lw_cooper: done";
           (dd, fun m -> m))
    in
    let local_abs =
      let open LocalAbstraction in
      logf ~level:`debug "convex_hull_lw_cooper...";
      Plt.abstract_to_standard_plt expand_mod_floor srk terms symbols
      |> compose (LwCooper.abstract_lw_cooper ~elim:(fun dim -> dim >= num_terms))
      |> compose (inject finalizer)
    in
    local_abs

  let mk_lw_abstraction ~man expand_mod_floor srk terms symbols =
    let num_terms = Array.length terms in
    let drop_integrality _m plt = (Plt.poly_part plt, fun m -> m) in
    let local_abs =
      let open LocalAbstraction in
      logf ~level:`debug "convex_hull_lw...";
      Plt.abstract_to_standard_plt expand_mod_floor srk terms symbols
      |> compose {abstract = drop_integrality}
      |> compose (LoosWeispfenning.abstract_lw ~elim:(fun dim -> dim >= num_terms))
      |> compose (Ddify.abstract ~man ~max_dim_in_projected:(num_terms - 1))
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

let conjunctive_normal_form srk ~base_dim phi =
    let symbols = Syntax.symbols phi in
    let dim_of_symbol sym = Syntax.int_of_symbol sym + base_dim in
    let initial_term_of_dim =
      Symbol.Set.fold
        (fun sym map ->
          IntMap.add (dim_of_symbol sym) (Syntax.mk_const srk sym) map)
        symbols IntMap.empty
    in
    let curr_term_of_dim = ref initial_term_of_dim in
    let curr_free_dim =
      ref
        (match Symbol.Set.max_elt_opt symbols with
         | Some symbol -> dim_of_symbol symbol + 1
         | None -> base_dim
        )
    in
    let local_abs =
      let abstract m psi =
        let expansion =
          Plt.mk_standard_expansion srk
            ~free_dim:!curr_free_dim ~dim_of_symbol
        in
        let result =
          LocalAbstraction.apply2
            (Plt.abstract_to_plt
               expansion
               ~term_of_new_dims_to_set:(Some curr_term_of_dim)
               srk
               (fun interp dim ->
                 try
                   let term = IntMap.find dim !curr_term_of_dim in
                   Interpretation.evaluate_term interp term
                 with
                 | Not_found ->
                    failwith
                      (Format.asprintf "conjunctive normal form: cannot evaluate dimension %d" dim)
               )
            )
            m psi
        in
        curr_free_dim :=
          (match IntMap.max_binding_opt !curr_term_of_dim with
           | Some (dim, _) -> dim + 1
           | None -> 0);
        result
      in
      LocalAbstraction.{abstract}
    in
    let term_of_dim dim =
      try IntMap.find dim !curr_term_of_dim
      with
      | Not_found ->
         failwith
           (Format.asprintf "conjunctive normal form: cannot find a term at dimension %d" dim)
    in
    let abstract =
      LocalGlobal.lift_plt_abstraction srk ~term_of_dim local_abs
    in
    (Abstraction.apply abstract phi, !curr_term_of_dim)

let local_abstraction_of_lira_model how solver man terms =
  let phi = Abstract.Solver.get_formula solver in
  let srk = Abstract.Solver.get_context solver in
  let local_abs =
    match how with
    | `SubspaceCone ->
       AbstractTerm.mk_sc_abstraction ~man
         `ExpandModFloor srk terms (Syntax.symbols phi)
    | `SubspaceConeAccelerated ->
       AbstractTerm.mk_sc_abstraction_with_acceleration ~man
         `ExpandModFloor srk terms (Syntax.symbols phi)
    | `Subspace ->
       AbstractTerm.mk_subspace_abstraction_with_acceleration ~man
         `ExpandModFloor srk terms (Syntax.symbols phi)
    | `IntFrac ->
       AbstractTerm.mk_intfrac_abstraction ~man `ExpandModFloor srk terms
         (Syntax.symbols phi)
    | `IntFracAccelerated ->
       AbstractTerm.mk_intfrac_abstraction_with_acceleration
         ~man `ExpandModFloor srk terms (Syntax.symbols phi)
    | `LwCooper hull_after_proj ->
       AbstractTerm.mk_lw_cooper_abstraction ~man hull_after_proj `ExpandModFloor
         srk terms (Syntax.symbols phi)
    | `Lw ->
       AbstractTerm.mk_lw_abstraction ~man `ExpandModFloor srk terms
         (Syntax.symbols phi)
  in
  local_abs

let convex_hull_of_lira_model how solver man terms model =
  let local_abs = local_abstraction_of_lira_model how solver man terms in
  let phi = Abstract.Solver.get_formula solver in
  let m = match model with
    | `LIRA m -> m
    | `LIRR _ -> invalid_arg "Unsupported"
  in
  LocalAbstraction.apply local_abs m phi

let abstract how solver ?(man=Polka.manager_alloc_loose ()) ?(bottom=None)
      terms =
  let phi = Abstract.Solver.get_formula solver in
  let srk = Abstract.Solver.get_context solver in
  let num_terms = Array.length terms in
  let local_abs = local_abstraction_of_lira_model how solver man terms in
  let abstract =
    LocalGlobal.lift_dd_abstraction ~solver:(Some solver) ~bottom
      srk ~man ~max_dim:(num_terms - 1)
      ~term_of_dim:(mk_term_of_dim terms)
      local_abs
  in
  Abstraction.apply abstract phi

let convex_hull how ?(man=(Polka.manager_alloc_loose ())) srk phi terms =
  let solver = Abstract.Solver.make srk phi in
  match how with
  | `SubspaceCone -> abstract `SubspaceCone solver ~man terms
  | `SubspaceConeAccelerated -> abstract `SubspaceConeAccelerated solver ~man terms
  | `Subspace -> abstract `Subspace solver ~man terms
  | `IntFrac -> abstract `IntFrac solver ~man terms
  | `IntFracAccelerated -> abstract `IntFracAccelerated solver ~man terms
  | `LwCooper finalize -> abstract (`LwCooper finalize) solver ~man terms
  | `Lw -> abstract `Lw solver ~man terms

let full_integer_hull_then_project
      ?(man=(Polka.manager_alloc_loose ()))
      how
      ~to_keep srk phi =
  let (plts, term_of_dim) = conjunctive_normal_form srk ~base_dim:0 phi in
  let polyhedra =
    List.map (fun plt ->
        let cnstrnts = sharpen_strict_inequalities_assuming_integrality (Plt.poly_part plt)
        in
        P.of_constraints cnstrnts
      ) plts
  in
  let max_dim =
    List.fold_left
      (fun max_dim p -> Int.max max_dim (P.max_constrained_dim p))
      Linear.const_dim
      polyhedra
  in
  let terms_to_keep = Symbol.Set.to_list to_keep
                      |> List.map (Syntax.mk_const srk) in
  let dimensions_to_project =
    let open BatEnum in
    (0 -- max_dim) //
      (fun dim ->
        try
          let term = IntMap.find dim term_of_dim in
          not (List.mem term terms_to_keep)
        with
        | Not_found ->
           true
      )
    |> BatList.of_enum
  in
  let dds = List.map (P.dd_of ~man (max_dim + 1)) polyhedra in
  let realconvhull = List.fold_left DD.join (P.dd_of (max_dim + 1) P.bottom) dds
  in
  let integerhull =
    match how with
    | `GomoryChvatal -> DD.integer_hull realconvhull
    | `Normaliz -> P.integer_hull `Normaliz (P.of_dd realconvhull)
                   |> P.dd_of (max_dim + 1)
  in
  DD.project dimensions_to_project integerhull

let full_integer_hull_then_project_onto_terms
      ?(man=(Polka.manager_alloc_loose ()))
      how
      srk phi terms =
  let num_terms = Array.length terms in
  let (plts, _term_of_dim) = conjunctive_normal_form srk ~base_dim:num_terms phi
  in
  let (term_definitions, lcond, tcond) =
    Plt.mk_standard_term_definitions srk
      (fun sym -> Syntax.int_of_symbol sym + num_terms) terms in
  assert (lcond = []);
  assert (tcond = []);
  let polyhedra =
    List.map (fun plt ->
        let cnstrnts =
          sharpen_strict_inequalities_assuming_integrality (Plt.poly_part plt)
        in
        let cnstrnts = BatEnum.append (BatList.enum term_definitions) cnstrnts in
        P.of_constraints cnstrnts
      ) plts
  in
  let max_dim =
    List.fold_left
      (fun max_dim p -> Int.max max_dim (P.max_constrained_dim p))
      Linear.const_dim
      polyhedra
  in
  let dimensions_to_project =
    let open BatEnum in
    (0 -- max_dim) // (fun dim -> dim >= num_terms) |> BatList.of_enum
  in
  let dds = List.map (P.dd_of ~man (max_dim + 1)) polyhedra in
  let realconvhull = List.fold_left DD.join (P.dd_of (max_dim + 1) P.bottom) dds
  in
  let integerhull =
    match how with
    | `GomoryChvatal -> DD.integer_hull realconvhull
    | `Normaliz -> P.integer_hull `Normaliz (P.of_dd realconvhull)
                   |> P.dd_of (max_dim + 1)
  in
  DD.project dimensions_to_project integerhull

let convex_hull_lia srk phi terms =
  convex_hull (`LwCooper `IntHullAfterProjection) srk phi terms

let convex_hull_lra srk phi terms =
  convex_hull (`LwCooper `NoIntHullAfterProjection) srk phi terms

module PolyhedralFormula : sig

  val polyhedral_formula_of_qf: 'a Syntax.context -> 'a Syntax.Formula.t ->
                                'a Syntax.Formula.t * Symbol.Set.t

  val retype_as:
    'a Syntax.context -> [`TyInt | `TyReal] -> 'a Syntax.Formula.t ->
    'a Syntax.Formula.t * (Syntax.symbol Syntax.Symbol.Map.t)

end = struct

  (** For [phi] that is quantifier-free,
      [remove_integrality_constraints srk phi] returns [psi] that is
      free of [is_int] and whose projection onto the symbols of [phi] is
      equivalent to [phi], provided that projection respects 
      integrality constraints of symbols that are eliminated.
   *)
  let remove_integrality_constraints srk phi =
    let open Syntax in
    rewrite srk
      ~down:(fun expr ->
        match destruct srk expr with
        | `Not phi ->
           begin match destruct srk phi with
           | (`Atom (`IsInt t)) ->
              let s = mk_symbol srk ~name:"standardize_not_int" `TyInt in
              let bound = mk_const srk s in
              mk_and srk [ mk_lt srk bound t
                         ; mk_leq srk t (mk_add srk [bound; mk_real srk QQ.one])
                ]
           | _ -> expr
           end
        | `Atom (`IsInt t) ->
           let s = Syntax.mk_symbol srk ~name:"standardize_int" `TyInt
           in
           mk_eq srk (mk_const srk s) t
        | _ -> expr
      )
      phi

  let polyhedral_formula_of_qf srk phi =
    let polyhedral_phi =
      rewrite srk ~down:(Syntax.nnf_rewriter srk) phi
      |> rewrite srk ~down:(Syntax.pos_rewriter srk)
      |> remove_integrality_constraints srk
      |> eliminate_floor_mod_div srk in
    let new_symbols =
      Symbol.Set.diff (symbols polyhedral_phi) (Syntax.symbols phi)
    in
    (polyhedral_phi, new_symbols)

  let cast_formula srk typ phi =
    let map =
      Symbol.Set.fold
        (fun sym map ->
          match typ_symbol srk sym with
          | `TyInt ->
             begin match typ with
             | `TyReal ->
                let new_sym =
                  mk_symbol srk ~name:(Format.asprintf "%s_realified"
                                         (show_symbol srk sym))
                    `TyReal
                in
                Symbol.Map.add sym new_sym map
             | `TyInt ->
                map
             end
          | `TyReal ->
             begin match typ with
             | `TyInt ->
                let new_sym =
                  mk_symbol srk ~name:(Format.asprintf "%s_integralized"
                                         (show_symbol srk sym))
                    `TyInt
                in
                Symbol.Map.add sym new_sym map
             | `TyReal -> map
             end
          | _ -> map
        )
        (symbols phi)
        Symbol.Map.empty
    in
    let lookup s = try Symbol.Map.find s map with | Not_found -> s in
    ( Syntax.substitute_const srk
        (fun s -> Syntax.mk_const srk (lookup s)) phi
    , map )

  (* 

  Why doesn't this typecheck?

  let make_all_symbols srk typ phi =
    let new_symbols =
      Symbol.Set.fold
        (fun sym map1 ->
          match typ with
          | `TyInt ->
             fun s ->
             begin match typ_symbol srk s with
             | `TyReal ->
             let new_sym =
                  mk_symbol srk ~name:(Format.asprintf "%s_integralized"
                                         (show_symbol srk s))
                    `TyInt
                in
                Symbol.Map.add sym new_sym (map1 sym)
             | _ -> (map1 sym)
             end
          | `TyReal ->
             fun s ->
             begin match typ_symbol srk s with
             | `TyInt -> 
                let new_sym =
                  mk_symbol srk ~name:(Format.asprintf "%s_realified"
                                         (show_symbol srk s))
                    `TyReal
                in
                Symbol.Map.add sym new_sym (map1 sym)
             | _ -> (map1 sym)
             end
        )
        (symbols phi)
        Symbol.Map.empty
    in
    let lookup s =
      try Symbol.Map.find s new_symbols
      with
      | Not_found -> s
    in
    ( Syntax.substitute_const srk
        (fun s -> Syntax.mk_const srk (lookup s)) phi
    , new_symbols )
   *)
    
  let retype_as srk typ phi =
    let (p_phi, _new_symbols) = polyhedral_formula_of_qf srk phi in
    cast_formula srk typ p_phi
    
end
