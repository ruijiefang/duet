open Syntax
module P = Polyhedron
module L = IntLattice

module V = Linear.QQVector

include Log.Make (struct let name = "polyhedronLatticeTiling" end)

let () = my_verbosity_level := `debug

module LocalAbstraction : sig

  type ('concept1, 'point1, 'concept2, 'point2) t =
    {
      abstract: 'point1 -> 'concept1 -> 'concept2 * ('point1 -> 'point2)
    }

  val apply:
    ('concept1, 'point1, 'concept2, 'point2) t -> 'point1 -> 'concept1 -> 'concept2

  val compose:
    ('concept1, 'point1, 'concept2, 'point2) t ->
    ('concept2, 'point2, 'concept3, 'point3) t ->
    ('concept1, 'point1, 'concept3, 'point3) t

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

  let compose
        (t1: ('concept1, 'point1, 'concept2, 'point2) t)
        (t2: ('concept2, 'point2, 'concept3, 'point3) t) =
    let abstract x c =
      let (c2, translation12) = t1.abstract x c in
      let (c3, translation23) = t2.abstract (translation12 x) c2 in
      (c3, fun m -> translation23 (translation12 m))
    in
    { abstract }

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

type dd = (DD.closed DD.t * int)

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

let collect_dimensions vector_of constraints =
  let dims = ref IntSet.empty in
  BatList.iter
    (fun constr ->
      V.enum (vector_of constr)
      |> BatEnum.iter
           (fun (_, dim) ->
             if dim <> Linear.const_dim
             then dims := IntSet.add dim !dims
             else ())
    )
    constraints;
  !dims

let pp_vector =
  V.pp_term (fun fmt dim -> Format.fprintf fmt "(dim %d)" dim)

let pp_pconstr fmt (kind, v) =
  match kind with
  | `Zero -> Format.fprintf fmt "@[%a@] = 0" pp_vector v
  | `Nonneg -> Format.fprintf fmt "@[%a@] >= 0" pp_vector v
  | `Pos -> Format.fprintf fmt "@[%a@] > 0" pp_vector v

module SyntaxVector: sig

  open Syntax

  type 'a lin_cond =
    {
      p_cond: (P.constraint_kind * V.t) list
    ; l_cond: V.t list
    ; t_cond: V.t list
    ; free_dim: int
    ; extension: QQ.t IntMap.t -> QQ.t IntMap.t
    }

  val tru: free_dim:int -> 'a lin_cond
  val fls: free_dim:int -> 'a lin_cond

  val extension_union:
    (QQ.t IntMap.t -> QQ.t IntMap.t) ->
    (QQ.t IntMap.t -> QQ.t IntMap.t) ->
    (QQ.t IntMap.t -> QQ.t IntMap.t)

  val conjoin: 'a lin_cond -> 'a lin_cond -> 'a lin_cond

  val linearize_term:
    'a context -> (Syntax.symbol -> V.t) ->
    free_dim: int -> 'a arith_term -> (V.t * 'a lin_cond)

end = struct

  open Syntax

  type 'a lin_cond =
    {
      p_cond: (P.constraint_kind * V.t) list
    ; l_cond: V.t list
    ; t_cond: V.t list
    ; free_dim: int
    ; extension: QQ.t IntMap.t -> QQ.t IntMap.t
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

  let fun_of_int_map ?(err="") m dim =
    try IntMap.find dim m with
    | Not_found ->
       failwith
         (Format.asprintf "%s: cannot find dimension %d" err dim)

  let tru ~free_dim =
    {
      p_cond = []
    ; l_cond = []
    ; t_cond = []
    ; free_dim = free_dim
    ; extension = (fun _ -> IntMap.empty)
    }

  let fls ~free_dim =
    {
      p_cond = [(`Zero, Linear.const_linterm QQ.one)]
    ; l_cond = []
    ; t_cond = []
    ; free_dim = free_dim
    ; extension = (fun _ -> IntMap.empty)
    }

  let consistent_union map1 map2 =
    IntMap.union
      (fun dim r1 r2 ->
        if r1 <> r2 then
          failwith
            (Format.asprintf "linearize_term: conflicting valuation at %d when combining extensions"
               dim)
        else Some r1
      )
      map1 map2

  let extension_union ext1 ext2 orig = consistent_union (ext1 orig) (ext2 orig)

  let conjoin lin1 lin2 =
    {
      p_cond = List.rev_append lin1.p_cond lin2.p_cond
    ; l_cond = List.rev_append lin1.l_cond lin2.l_cond
    ; t_cond = List.rev_append lin1.t_cond lin2.t_cond
    ; free_dim = Int.max lin1.free_dim lin2.free_dim
    ; extension = extension_union lin1.extension lin2.extension
    }

  let lift_binop op (v1, ln1) (v2, ln2) =
    (op v1 v2, conjoin ln1 ln2)

  (* Linear.linterm_of can only handle div and mod on constants, but
     [t div constant] and [t mod constant] can come from the input.
     Also, Interpretation.destruct_atom translates [IsInt t] into
     [t' mod constant] terms.
   *)
  let linearize_term srk vec_of_symbol ~free_dim t =
    ArithTerm.eval srk (function
        | `Real r -> (Linear.const_linterm r, tru ~free_dim)
        | `App (x, []) -> (vec_of_symbol x, tru ~free_dim)
        | `App (_f, _xs) -> raise Linear.Nonlinear
        | `Var (_i, _typ) -> raise Linear.Nonlinear
        | `Add lns ->
           List.fold_left
             (lift_binop V.add)
             (V.zero, tru ~free_dim)
             lns
        | `Mul lns ->
           List.fold_left
             (lift_binop mul_vec)
             (Linear.const_linterm QQ.one, tru ~free_dim)
             lns
        | `Binop (`Div, ln1, ln2) ->
           begin
             let divide v1 v2 =
               let divisor = try real_of v2 with | Invalid_argument _ -> raise Linear.Nonlinear
               in
               if QQ.equal divisor QQ.zero then invalid_arg "Division by zero"
               else
                 V.scalar_mul (QQ.inverse divisor) v1
             in
             (lift_binop divide) ln1 ln2
           end
        | `Binop (`Mod, (v1, ln1), (v2, _)) ->
           (*
              E[s mod constant] -->
              exists q. Int(q)
                /\ E[s - q * constant] /\ 0 <= s - q * constant < constant
            *)
           begin
             let modulus =
               try real_of v2 with | Invalid_argument _ -> raise Linear.Nonlinear
             in
             let () =
               if QQ.equal modulus QQ.zero then invalid_arg "Division by zero"
               else ()
             in
             let quotient = V.of_term QQ.one free_dim in
             logf ~level:`debug "linearize_term: introducing dimension %d for quotient" free_dim;
             let remainder =
               V.sub
                 v1 (V.scalar_mul modulus quotient) in
             let extend orig =
               let extended = consistent_union (ln1.extension orig) orig
               in
               let v1_val =
                 (* WARNING:
                    In Z3, [mod] is NOT QQ.modulo in general, but
                    Z3's mod is the restriction of QQ.modulo to integer operands.
                    Input to Z3 should restrict operands to integer-typed ones,
                    so this should work.
                  *)
                 Linear.evaluate_affine
                   (fun_of_int_map ~err:"linearize_term: evaluating mod: " extended) v1
               in
               IntMap.add free_dim (QQ.of_zz (QQ.idiv v1_val modulus)) extended
             in
             let ln =
             {
               p_cond = [(`Nonneg, remainder); (`Pos, V.sub v2 remainder)]
                        @ ln1.p_cond
             ; l_cond = [quotient] @ ln1.l_cond
             ; t_cond = ln1.t_cond
             ; free_dim = free_dim + 1
             ; extension = extend
             } in
             (remainder, ln)
           end
        | `Unop (`Floor, (v, ln)) ->
           (*
             E[floor(t)] --> exists n. Int(n) /\ n <= t < n + 1 /\ E[n].
            *)
           begin
             let floored = V.of_term QQ.one free_dim in
             logf ~level:`debug "introducing dimension %d for floor" free_dim;
             let lower_bound = V.sub v floored in
             let upper_bound =
               V.sub floored v |>
                 V.add_term QQ.one Linear.const_dim in
             let extend orig =
               let extended = consistent_union (ln.extension orig) orig in
               let floored_value =
                 Linear.evaluate_affine
                   (fun_of_int_map ~err:"linearize_term" extended) v
                 |> QQ.floor |> QQ.of_zz
               in
               IntMap.add free_dim floored_value extended
             in
             let ln =
               {
                 p_cond = [(`Nonneg, lower_bound); (`Pos, upper_bound)] @ ln.p_cond
               ; l_cond = [floored] @ ln.l_cond
               ; t_cond = ln.t_cond
               ; free_dim = free_dim + 1
               ; extension = extend
               }
             in
             (floored, ln)
           end
        | `Unop (`Neg, (v, ln)) ->
           (V.negate v, ln)
        | `Ite _ -> assert false
        | `Select _ -> raise Linear.Nonlinear
      ) t

end

module Plt : sig

  type t =
    {
      poly_part: P.t
    ; lattice_part: L.t
    ; tiling_part: L.t
    ; universe_p: (P.constraint_kind * V.t) list
    ; universe_l: V.t list
    ; universe_t: V.t list
    ; max_dim: int
    }

  val top: max_dim: int -> t

  val abstract_to_standard_plt:
    'a Syntax.context ->
    ?universe_p: (P.constraint_kind * V.t) BatEnum.t ->
    ?universe_l: V.t BatEnum.t ->
    ?universe_t: V.t BatEnum.t ->
    max_dim:int ->
    (Syntax.symbol -> int) ->
    ('a Interpretation.interpretation -> (int -> QQ.t)) ->
    ('a Syntax.formula, 'a Interpretation.interpretation, t, int -> QQ.t) LocalAbstraction.t

  val formula_of_plt:
    'a Syntax.context -> (int -> 'a Syntax.arith_term) -> t -> 'a formula

end = struct

  open SyntaxVector

  type t =
    {
      poly_part: P.t
    ; lattice_part: L.t
    ; tiling_part: L.t
    ; universe_p: (P.constraint_kind * V.t) list
    ; universe_l: V.t list
    ; universe_t: V.t list
    ; max_dim: int
    }

  let top ~max_dim =
    {
      poly_part = Polyhedron.top
    ; lattice_part = L.bottom
    ; tiling_part = L.bottom
    ; universe_p = []
    ; universe_l = []
    ; universe_t = []
    ; max_dim
    }

  let plt_ineq srk vec_of_symbol ~free_dim (sign: [`Lt | `Leq | `Eq]) t1 t2 =
    let (v2, lin2) = linearize_term srk vec_of_symbol
                       ~free_dim t2 in
    let (v1, lin1) = linearize_term srk vec_of_symbol
                       ~free_dim:(lin2.free_dim) t1 in
    let v = V.sub v2 v1 in
    let kind = match sign with
      | `Lt -> `Pos
      | `Leq -> `Nonneg
      | `Eq -> `Zero
    in
    {
      p_cond = (kind, v) :: (lin1.p_cond @ lin2.p_cond)
    ; l_cond = lin1.l_cond @ lin2.l_cond
    ; t_cond = lin1.t_cond @ lin2.t_cond
    ; free_dim = lin1.free_dim
    ; extension = extension_union lin1.extension lin2.extension
    }

  let plt_int srk vec_of_symbol ~free_dim (sign: [`IsInt | `NotInt]) t =
    let (v, lin) = linearize_term srk vec_of_symbol ~free_dim t in
    match sign with
    | `IsInt ->
       {lin with l_cond = v :: lin.l_cond }
    | `NotInt ->
       {lin with t_cond = v :: lin.t_cond }

  let plt_constraint_of_atom srk vec_of_symbol ~free_dim m atom =
    match Formula.destruct srk atom with
    | `Tru -> tru ~free_dim
    | `Fls -> fls ~free_dim
    | `Not psi ->
       begin
         match Formula.destruct srk psi with
         | `Tru -> fls ~free_dim
         | `Fls -> tru ~free_dim
         | `Atom (`Arith (`Eq, t1, t2)) ->
            if Interpretation.evaluate_formula m (Syntax.mk_lt srk t1 t2)
            then
              plt_ineq srk vec_of_symbol ~free_dim `Lt t1 t2
            else
              plt_ineq srk vec_of_symbol ~free_dim `Lt t2 t1
         | `Atom (`Arith (`Leq, t1, t2)) ->
            plt_ineq srk vec_of_symbol ~free_dim `Lt t2 t1
         | `Atom (`Arith (`Lt, t1, t2)) ->
            plt_ineq srk vec_of_symbol ~free_dim `Leq t2 t1
         | `Atom (`ArrEq (_t1, _t2)) -> invalid_arg "linearize_atom"
         | `Atom (`IsInt t) ->
            plt_int srk vec_of_symbol ~free_dim `NotInt t
         | _ -> invalid_arg "linearize_atom"
       end
    | `Atom (`Arith (`Eq, t1, t2)) ->
       plt_ineq srk vec_of_symbol ~free_dim `Eq t1 t2
    | `Atom (`Arith (`Leq, t1, t2)) ->
       plt_ineq srk vec_of_symbol ~free_dim `Leq t1 t2
    | `Atom (`Arith (`Lt, t1, t2)) ->
       plt_ineq srk vec_of_symbol ~free_dim `Lt t1 t2
    | `Atom (`ArrEq (_t1, _t2)) -> invalid_arg "linearize_atom"
    | `Atom (`IsInt t) -> plt_int srk vec_of_symbol ~free_dim `IsInt t
    | _ -> invalid_arg "linearize_atom"

  let plt_implicant_of_implicant srk vec_of_symbol ~free_dim m implicant =
    match implicant with
    | None -> assert false
    | Some atoms ->
       let lin = List.fold_left (fun lin atom ->
                     let lin_atom =
                       plt_constraint_of_atom srk vec_of_symbol
                         ~free_dim:lin.free_dim m atom in
                     conjoin lin_atom lin
                   )
                   (tru ~free_dim)
                   atoms
       in
       ( P.of_constraints (BatList.enum lin.p_cond)
       , L.hermitize (lin.l_cond)
       , L.hermitize (lin.t_cond)
       , free_dim - 1
       , lin.extension
       )

  let to_int_map m n =
    let rec to_int_map n map =
      try
        if n = -1 then map
        else
          to_int_map (n-1) (IntMap.add n (m n) map)
      with _ ->
        to_int_map (n-1) map
    in
    to_int_map n IntMap.empty
        
  let abstract_to_standard_plt srk
        ?(universe_p=(BatList.enum []))
        ?(universe_l=(BatList.enum []))
        ?(universe_t=(BatList.enum []))
        ~max_dim
        dim_of_symbol univ_translation =
    let universe_p = BatList.of_enum universe_p in
    let universe_l = BatList.of_enum universe_l in
    let universe_t = BatList.of_enum universe_t in
    let abstract m phi =
      logf ~level:`debug "abstract_to_standard_plt...";
      let implicant = Interpretation.select_implicant m phi in
      logf ~level:`debug "abstract_to_standard_plt: abstracting @[%a@]"
        (Format.pp_print_list
           ~pp_sep: (fun fmt () -> Format.fprintf fmt ", ")
           (fun fmt atom -> Syntax.Formula.pp srk fmt atom)
        )
        (Option.get implicant);
      let (p, l, t, max_dim_plt, extension) =
        plt_implicant_of_implicant srk
          (fun sym -> V.of_term QQ.one (dim_of_symbol sym))
          ~free_dim:(max_dim + 1)
          m
          implicant
      in
      logf ~level:`debug "abstract_to_standard_plt: abstracted @[%a@]"
        (P.pp Format.pp_print_int) p;
      let plt = { poly_part = p
                ; lattice_part = l
                ; tiling_part = t
                ; universe_p
                ; universe_l
                ; universe_t
                ; max_dim = max_dim_plt
                }
      in
      let extended_univ_translation interp =
        let m = univ_translation interp in
        let map = to_int_map m max_dim in
        (fun dim ->
          try IntMap.find dim (extension map) with
          | Not_found -> m dim)
      in
      (plt, extended_univ_translation)
    in
    LocalAbstraction.{ abstract }

  let formula_of_plt srk term_of_dim plt =
    let phis_p =
      BatEnum.fold
        (fun phis constr -> formula_p srk term_of_dim constr :: phis)
        []
        ((P.enum_constraints plt.poly_part)
         |> BatEnum.append (BatList.enum plt.universe_p))
    in
    let phis_l =
      BatList.fold
        (fun phis lconstr -> formula_l srk term_of_dim lconstr :: phis)
        []
        (L.basis plt.lattice_part |> List.rev_append plt.universe_l)
    in
    let phis_t =
      BatList.fold
        (fun phis tconstr -> formula_t srk term_of_dim tconstr :: phis)
        []
        (L.basis plt.tiling_part |> List.rev_append plt.universe_t)
    in
    mk_and srk (phis_p @ phis_l @ phis_t)

end

module Ddify: sig

  val abstract:
    max_dim_in_projected: int ->
    (P.t, int -> QQ.t, dd, int -> QQ.t) LocalAbstraction.t

end = struct

  let abstract ~max_dim_in_projected =
    let abstract _m p =
      ( (P.dd_of (max_dim_in_projected + 1) p, max_dim_in_projected)
      , (fun m -> m)
      )
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
        |> collect_dimensions (fun (_, v) -> v)
        |> IntSet.filter elim
        |> IntSet.to_list
      in
      logf ~level:`debug "abstract_lw: eliminating dimensions @[%a@] from @[%a@]"
        (Format.pp_print_list ~pp_sep:(fun fmt _ -> Format.fprintf fmt ", ")
           Format.pp_print_int)
        to_project
        (P.pp Format.pp_print_int) p;
      let abstracted = P.local_project m to_project p in
      logf ~level:`debug "abstract_lw: abstracted @[%a@]@\n"
        (P.pp Format.pp_print_int) abstracted;
      (abstracted, fun m -> m)
    in
    LocalAbstraction.{ abstract }

end

module MixedCooper: sig

  (* Dimensions to be eliminated must take on only integer values in the
     universe.
   *)
  val abstract_cooper:
    elim: (int -> bool) ->
    ceiling: (V.t -> (int -> QQ.t) -> (V.t * (P.constraint_kind * V.t) list * V.t list)) ->
    (Plt.t, int -> QQ.t, Plt.t, int -> QQ.t) LocalAbstraction.t

end = struct

  let substitute_for_in v dim w =
    let (coeff, w') = V.pivot dim w in
    V.add (V.scalar_mul coeff v) w'

  let virtual_sub_p vt dim (kind, v) =
    let (coeff, _) = V.pivot dim v in
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
         let delta = QQ.modulo (Linear.evaluate_affine m v)
                       lcm_denom_dim_in_lt in
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
    let glb = ref None in
    List.iter
      (fun (kind, v) ->
        let (coeff, w) = V.pivot dim v in
        if QQ.equal QQ.zero coeff then
          ()
        else if QQ.lt QQ.zero coeff then
          let lower_bound = V.scalar_mul (QQ.negate (QQ.inverse coeff)) w in
          let b = Linear.evaluate_affine m lower_bound in
          begin
            let () =
              match kind with
              | `Zero -> has_upper_bound := true
              | _ -> ()
            in
            match !glb with
            | None -> glb := Some (kind, lower_bound, b)
            | Some (kind0, _, b0) ->
               if b0 < b then
                 glb := Some (kind, lower_bound, b)
               else if b < b0 then
                 ()
               else
                 begin match (kind0, kind) with
                 | (`Nonneg, `Pos)
                   | (`Nonneg, `Zero)
                   | (`Pos, `Zero) -> glb := Some (kind, lower_bound, b)
                 | (_, _) -> ()
                 end
          end
        else
          has_upper_bound := true
      )
      p;
    (!glb, !has_upper_bound)

  (* For vectors v, v' in dimensions free of elim_dim,
     [ceiling t m = t']  only if [t'] evaluated at [m] is the least integer
     greater than or equal to [t] evaluated at [m].
     For a general lattice, orient its constraints to have positive coefficient
     in [elim_dim]. Then "integer" generalizes to a (finite-dimensional) vector
     of integers, and "least integer" means least in product order.
     If [ceiling] has finite image (for each t), [abstract_cooper_one] has.
   *)
  let cooper_one ceiling lcm_denom_elim_dim_in_lt elim_dim m (p, l, t) =
    let select_term lower =
      let delta = QQ.modulo
                    (QQ.sub (m elim_dim) (Linear.evaluate_affine m lower))
                    lcm_denom_elim_dim_in_lt
      in
      let term = V.add_term delta Linear.const_dim lower in
      logf ~level:`debug "cooper_one: selected term @[%a@]" pp_vector term;
      term
    in
    let (term_selected, pcond, lcond) =
      match glb_for elim_dim p m with
      | (_, false) -> (`PlusInfinity, [], [])
      | (None, _) -> (`MinusInfinity, [], [])
      | (Some (kind, term, value), true) ->
         if Option.is_some (QQ.to_zz value) && kind = `Pos then
           let (rounded, pcond, lcond) = ceiling term m in
           let lb =
             V.add_term QQ.one Linear.const_dim rounded
           in
           (`Term (select_term lb), pcond, lcond)
         else
           let (rounded, pcond, lcond) = ceiling term m in
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
    (polyhedron, lattice, tiling)

  let log_constraints str (p, l, t) =
    logf ~level:`debug
      "abstract_cooper: %s p_constraints: @[%a@]@\n" str
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
         pp_pconstr) p;
    logf ~level:`debug
      "abstract_cooper: %s l_constraints: @[%a@]@\n" str
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
         pp_vector) l;
    logf ~level:`debug
      "abstract_cooper: %s t_constraints: @[%a@]@\n" str
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
         pp_vector) t

  let abstract_cooper_ ~elim ~ceiling m plt =
    let open Plt in
    let p =
      P.enum_constraints plt.poly_part
      |> BatList.of_enum
      |> List.rev_append plt.universe_p
    in
    let l = L.basis plt.lattice_part
            |> List.rev_append plt.universe_l
    in
    let t = L.basis plt.tiling_part
            |> List.rev_append plt.universe_t
    in
    log_constraints "abstracting" (p, l, t);
    let collect_dimensions (p, l, t) =
      p
      |> collect_dimensions (fun (_, v) -> v)
      |> IntSet.union (collect_dimensions (fun v -> v) l)
      |> IntSet.union (collect_dimensions (fun v -> v) t)
    in
    let elim_dimensions =
      collect_dimensions (p, l, t)
      |> IntSet.filter elim
    in
    let (projected_p, projected_l, projected_t) =
      IntSet.fold
        (fun elim_dim (p, l, t) ->
          let lcm_denom vectors =
            List.fold_left
              (fun lcm v ->
                let coeff = V.coeff elim_dim v in
                if QQ.equal QQ.zero coeff then lcm
                else ZZ.lcm lcm (QQ.denominator coeff)
              )
              ZZ.one vectors
          in
          let lcm = lcm_denom (List.rev_append l t) in
          cooper_one ceiling (QQ.of_zz lcm) elim_dim m (p, l, t)
        )
        elim_dimensions
        (p, l, t)
    in
    log_constraints "abstracted" (projected_p, projected_l, projected_t);
    let max_dim =
      let dimensions = collect_dimensions (projected_p, projected_l, projected_t) in
      try IntSet.max_elt dimensions with
      | Not_found -> failwith "abstract_cooper: no dimension left!"
    in
    {
      poly_part = Polyhedron.of_constraints (BatList.enum projected_p)
    ; lattice_part = L.hermitize projected_l
    ; tiling_part = L.hermitize projected_t
    ; universe_p = [] (* TODO: Separate projection from poly_part from universe_p? *)
    ; universe_l = []
    ; universe_t = []
    ; max_dim
    }

  let abstract_cooper ~elim ~ceiling =
    LocalAbstraction.
    {
      abstract =
        (fun m plt -> (abstract_cooper_ ~elim ~ceiling m plt, fun m -> m))
    }

end

module SubspaceCone : sig

  val abstract_sc:
    max_dim_in_projected: int ->
    (Plt.t, int -> QQ.t, dd, int -> QQ.t) LocalAbstraction.t

end = struct

  module LW = LoosWeispfenning

  let closure p =
    P.enum_constraints p
    |> BatEnum.map
         (fun (kind, v) ->
           match kind with
           | `Zero | `Nonneg -> (kind, v)
           | `Pos -> (`Nonneg, v)
         )
    |> P.of_constraints

  let abstract_sc ~max_dim_in_projected =
    let abstract m plt =
      logf ~level:`debug "abstract_sc...";
      let abstract_lw =
        let abstract =
          LocalAbstraction.compose
            (LW.abstract_lw ~elim:(fun dim -> dim > max_dim_in_projected))
            (Ddify.abstract ~max_dim_in_projected)
        in
        LocalAbstraction.apply abstract m
      in
      let p =
        P.enum_constraints plt.Plt.poly_part
        |> BatEnum.append (BatList.enum (plt.Plt.universe_p))
        |> P.of_constraints
      in
      let l_constraints =
        L.basis plt.lattice_part
        |> BatList.append plt.universe_l
      in
      let closed_p = closure p in
      let (polyhedron_abstraction, _) = abstract_lw closed_p in
      let (subspace_abstraction, _) =
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
        match subspace_constraints with
        | [] -> (polyhedron_abstraction, max_dim_in_projected)
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
      let dd = BatEnum.append (DD.enum_generators subspace_abstraction) recession_cone
               |> DD.of_generators (max_dim_in_projected + 1) in
      ((dd, max_dim_in_projected), (fun m -> m))
    in
    LocalAbstraction.{ abstract }

end

module LocalGlobal: sig

  open Syntax
  open Interpretation

  val localize:
    ('concept1, 'point1, 'concept2, 'point2) Abstraction.t ->
    ('concept1, 'point1, 'concept2, 'point2) LocalAbstraction.t

  val lift_dd_abstraction:
    'a context -> max_dim:int -> term_of_dim:(int -> 'a Syntax.arith_term) ->
    ('a formula, 'a interpretation, dd, int -> QQ.t) LocalAbstraction.t ->
    ('a formula, 'a interpretation, dd, int -> QQ.t) Abstraction.t

  val lift_plt_abstraction:
    'a context -> term_of_dim:(int -> 'a Syntax.arith_term) ->
    ('a formula, 'a interpretation, Plt.t, int -> QQ.t) LocalAbstraction.t ->
    ('a formula, 'a interpretation, Plt.t list, int -> QQ.t) Abstraction.t

end = struct

  open Syntax
  open Interpretation

  let localize
        (abstraction : ('concept1, 'point1, 'concept2, 'point2) Abstraction.t) =
    LocalAbstraction.
    { abstract = (fun _x c -> abstraction.abstract c) }

  let lift_abstraction srk join formula_of top bottom term_of_dim
        (local_abs: ('a formula, 'a interpretation, 'concept, 'point) LocalAbstraction.t) =
    let abstract phi =
      let domain =
        Abstract.
        { join
        ; of_model =
            (fun m ->
              match m with
              | `LIRR _ -> assert false
              | `LIRA m ->
                 let (result, _univ_translation) = local_abs.abstract m phi in result
            )
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

  let lift_dd_abstraction (srk: 'a context) ~max_dim ~term_of_dim
        (local_abs: ('a formula, 'a interpretation, dd, int -> QQ.t) LocalAbstraction.t) =
    let ambient_dim = max_dim + 1 in
    let join (dd1, n1) (dd2, n2) =
      assert (n1 = n2 && n1 = max_dim);
      (DD.join dd1 dd2, max_dim)
    in
    let formula_of (dd, _) = formula_of_dd srk term_of_dim dd in
    let top = (P.dd_of ambient_dim P.top, max_dim) in
    let bottom = (P.dd_of ambient_dim P.bottom, max_dim) in
    lift_abstraction srk join formula_of top bottom term_of_dim local_abs

  let lift_plt_abstraction srk ~term_of_dim local_abs =
    let local_abs' =
      let abstract m phi =
        let (plt, univ_translation) =
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
    let top = [Plt.top ~max_dim:0] (* shouldn't matter *) in
    let bottom = [] in
    lift_abstraction srk join formula_of top bottom term_of_dim local_abs'

end

type plt = Plt.t

let formula_of_plt = Plt.formula_of_plt

let abstract_lw = LoosWeispfenning.abstract_lw

let abstract_sc = SubspaceCone.abstract_sc

let abstract_cooper = MixedCooper.abstract_cooper

let standard_plt_abstraction srk terms phi =
  let num_terms = Array.length terms in
  let max_dim =
    match Symbol.Set.max_elt_opt (Syntax.symbols phi) with
    | None -> num_terms - 1
    | Some dim -> Syntax.int_of_symbol dim + num_terms
  in
  logf ~level:`debug "initial plt abstraction: max_dim: %d, num_terms = %d@;" max_dim num_terms;
  let dim_of_symbol sym = Syntax.int_of_symbol sym + num_terms in
  let interp_dim interp dim =
    if dim >= num_terms then
      Interpretation.real interp (Syntax.symbol_of_int (dim - num_terms))
    else if dim >= 0 && dim < num_terms then
      Interpretation.evaluate_term interp terms.(dim)
    else
      begin
        logf "interp_dim: %d not defined" dim;
        assert false
      end
  in
  let universe_p =
    let term_defs = BatEnum.empty () in
    Array.iteri
      (fun dim term ->
        let (v, lincond) =
          SyntaxVector.linearize_term
            srk
            (fun sym -> V.of_term QQ.one (dim_of_symbol sym))
            ~free_dim:0
            term
        in
        (* Terms should be in pure LRA *)
        assert (lincond.free_dim = 0);
        ( `Zero
        , V.add_term (QQ.of_int (-1)) dim v
        )
        |> BatEnum.push term_defs)
      terms;
    term_defs
  in
  Plt.abstract_to_standard_plt srk ~universe_p ~max_dim dim_of_symbol interp_dim

let convex_hull_sc srk phi terms =
  let num_terms = Array.length terms in
  let plt_abstraction = standard_plt_abstraction srk terms phi in
  let sc_abstraction =
    LocalAbstraction.compose plt_abstraction
      (SubspaceCone.abstract_sc ~max_dim_in_projected:(num_terms - 1))
  in
  let term_of_dim dim =
    if dim >= 0 && dim < num_terms then terms.(dim)
    else failwith (Format.asprintf "term_of_dim: %d" dim)
  in
  let abstract =
    LocalGlobal.lift_dd_abstraction srk
      ~max_dim:(num_terms - 1)
      ~term_of_dim
      sc_abstraction
  in
  fst (Abstraction.apply abstract phi)

let cooper_project srk phi terms =
  let num_terms = Array.length terms in
  let plt_abstraction = standard_plt_abstraction srk terms phi in
  let cooper_abstraction =
    let elim dim = dim > num_terms in
    let ceiling v _m = (v, [], []) in
    LocalAbstraction.compose plt_abstraction
      (MixedCooper.abstract_cooper ~elim ~ceiling)
  in
  let term_of_dim dim =
    if dim >= 0 && dim < num_terms then terms.(dim)
    else failwith (Format.asprintf "term_of_dim: %d" dim)
  in
  let abstract = LocalGlobal.lift_plt_abstraction srk ~term_of_dim
                   cooper_abstraction
  in
  Abstraction.apply abstract phi
