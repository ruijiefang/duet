open Syntax
module P = Polyhedron
module L = IntLattice
module T = IntLattice

include Log.Make (struct let name = "polyhedronLatticeTiling" end)

let () = my_verbosity_level := `trace
(* let () = Log.set_verbosity_level "srk.srkZ3" `trace *)

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

module SyntaxVector: sig

  open Syntax

  type 'a lin_cond =
    {
      p_cond: (Polyhedron.constraint_kind * Linear.QQVector.t) list
    ; l_cond: Linear.QQVector.t list
    ; t_cond: Linear.QQVector.t list
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
    'a context -> (Syntax.symbol -> Linear.QQVector.t) ->
    free_dim: int -> 'a arith_term -> (Linear.QQVector.t * 'a lin_cond)

  val formula_of_dd: 'a context -> (int -> 'a arith_term) -> 'b DD.t -> 'a formula

end = struct

  open Syntax

  type 'a lin_cond =
    {
      p_cond: (Polyhedron.constraint_kind * Linear.QQVector.t) list
    ; l_cond: Linear.QQVector.t list
    ; t_cond: Linear.QQVector.t list
    ; free_dim: int
    ; extension: QQ.t IntMap.t -> QQ.t IntMap.t
    }

  let real_of v =
    let (r, v') = Linear.QQVector.pivot Linear.const_dim v in
    if Linear.QQVector.is_zero v' then r
    else invalid_arg "not a constant"

  let mul_vec v1 v2 =
    try Linear.QQVector.scalar_mul (real_of v1) v2
    with Invalid_argument _ ->
      begin
        try Linear.QQVector.scalar_mul (real_of v2) v1
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
             (lift_binop Linear.QQVector.add)
             (Linear.QQVector.zero, tru ~free_dim)
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
                 Linear.QQVector.scalar_mul (QQ.inverse divisor) v1
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
             let quotient = Linear.QQVector.of_term QQ.one free_dim in
             logf ~level:`debug "linearize_term: introducing dimension %d for quotient" free_dim;
             let remainder =
               Linear.QQVector.sub
                 v1 (Linear.QQVector.scalar_mul modulus quotient) in
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
               p_cond = [(`Nonneg, remainder); (`Pos, Linear.QQVector.sub v2 remainder)]
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
             let floored = Linear.QQVector.of_term QQ.one free_dim in
             logf ~level:`debug "introducing dimension %d for floor" free_dim;
             let lower_bound = Linear.QQVector.sub v floored in
             let upper_bound =
               Linear.QQVector.sub floored v |>
                 Linear.QQVector.add_term QQ.one Linear.const_dim in
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
           (Linear.QQVector.negate v, ln)
        | `Ite _ -> assert false
        | `Select _ -> raise Linear.Nonlinear
      ) t

  let term_of_vector srk term_of_dim v =
    let open Syntax in
    Linear.QQVector.enum v
    |> BatEnum.fold
         (fun summands (coeff, dim) ->
           if dim <> Linear.const_dim then
             mk_mul srk [mk_real srk coeff; term_of_dim dim] :: summands
           else
             mk_real srk coeff :: summands)
         []
    |> mk_add srk

  let formula_of_dd srk term_of_dim dd =
    DD.enum_constraints dd
    |> BatEnum.fold (fun atoms (kind, v) ->
           let t = term_of_vector srk term_of_dim v in
           match kind with
           | `Zero -> mk_eq srk t (mk_zero srk) :: atoms
           | `Nonneg -> mk_leq srk (mk_zero srk) t :: atoms
           | `Pos -> mk_lt srk (mk_zero srk) t :: atoms
         )
         []
    |> List.rev
    |> mk_and srk
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

end = struct

  open Syntax
  open Interpretation

  let localize
        (abstraction : ('concept1, 'point1, 'concept2, 'point2) Abstraction.t) =
    LocalAbstraction.
    { abstract = (fun _x c -> abstraction.abstract c) }

  let lift_dd_abstraction (srk: 'a context) ~max_dim ~term_of_dim
        (local_abs: ('a formula, 'a interpretation, dd, int -> QQ.t) LocalAbstraction.t) =
    let ambient_dim = max_dim + 1 in
    let formula_of (dd, _) = SyntaxVector.formula_of_dd srk term_of_dim dd in
    let abstract phi =
      let domain =
        Abstract.
        {
          join = (fun (dd1, n1) (dd2, n2) ->
            assert (n1 = n2 && n1 = max_dim);
            (DD.join dd1 dd2, max_dim))
        ; of_model = (fun m ->
          match m with
          | `LIRR _ -> assert false
          | `LIRA m ->
             let (result, _univ_translation) = local_abs.abstract m phi in
             assert (snd result = max_dim);
             result)
        ; formula_of
        ; top = (Polyhedron.dd_of ambient_dim Polyhedron.top, max_dim)
        ; bottom = (Polyhedron.dd_of ambient_dim Polyhedron.bottom, max_dim)
        }
      in
      let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
      ( Abstract.Solver.abstract solver domain
      , fun interp -> (fun dim -> Interpretation.evaluate_term interp (term_of_dim dim))
      )
    in
    Abstraction.{abstract}

end

let collect_dimensions vector_of constraints =
  let dims = ref IntSet.empty in
  BatList.iter
    (fun constr ->
      Linear.QQVector.enum (vector_of constr)
      |> BatEnum.iter
           (fun (_, dim) ->
             if dim <> Linear.const_dim
             then dims := IntSet.add dim !dims
             else ())
    )
    constraints;
  !dims

module Plt : sig

  type t =
    {
      poly_part: Polyhedron.t
    ; lattice_part: IntLattice.t
    ; tiling_part: IntLattice.t
    ; universe_p: (Polyhedron.constraint_kind * Linear.QQVector.t) list
    ; universe_l: Linear.QQVector.t list
    ; universe_t: Linear.QQVector.t list
    ; max_dim: int
    }

  val abstract_formula:
    'a Syntax.context ->
    ?universe_p:(Polyhedron.constraint_kind * Linear.QQVector.t) BatEnum.t ->
    ?universe_l:([`IsInt] * Linear.QQVector.t) BatEnum.t ->
    ?universe_t:([`NotInt] * Linear.QQVector.t) BatEnum.t ->
    max_dim:int ->
    (Syntax.symbol -> int) ->
    ('a Interpretation.interpretation -> (int -> QQ.t)) ->
    ('a Syntax.formula, 'a Interpretation.interpretation, t, int -> QQ.t) LocalAbstraction.t

end = struct

  open SyntaxVector

  type t =
    {
      poly_part: Polyhedron.t
    ; lattice_part: IntLattice.t
    ; tiling_part: IntLattice.t
    ; universe_p: (Polyhedron.constraint_kind * Linear.QQVector.t) list
    ; universe_l: Linear.QQVector.t list
    ; universe_t: Linear.QQVector.t list
    ; max_dim: int
    }

  let plt_ineq srk vec_of_symbol ~free_dim (sign: [`Lt | `Leq | `Eq]) t1 t2 =
    let (v2, lin2) = linearize_term srk vec_of_symbol
                       ~free_dim t2 in
    let (v1, lin1) = linearize_term srk vec_of_symbol
                       ~free_dim:(lin2.free_dim) t1 in
    let v = Linear.QQVector.sub v2 v1 in
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
       ( Polyhedron.of_constraints (BatList.enum lin.p_cond)
       , IntLattice.hermitize (lin.l_cond)
       , IntLattice.hermitize (lin.t_cond)
       , free_dim - 1
       , lin.extension
       )

  let abstract_formula srk
        ?(universe_p=(BatList.enum []))
        ?(universe_l=(BatList.enum []))
        ?(universe_t=(BatList.enum []))
        ~max_dim
        dim_of_symbol univ_translation =
    let universe_p = BatList.of_enum universe_p in
    let universe_l = BatList.of_enum universe_l |> List.map (fun (_, v) -> v) in
    let universe_t = BatList.of_enum universe_t |> List.map (fun (_, v) -> v) in
    let abstract m phi =
      logf ~level:`debug "abstract_formula...";
      let implicant = Interpretation.select_implicant m phi in
      logf ~level:`debug "abstract_formula: abstracting @[%a@]"
        (Format.pp_print_list
           ~pp_sep: (fun fmt () -> Format.fprintf fmt ", ")
           (fun fmt atom -> Syntax.Formula.pp srk fmt atom)
        )
        (Option.get implicant);
      let (p, l, t, max_dim_plt, extension) =
        plt_implicant_of_implicant srk
          (fun sym -> Linear.QQVector.of_term QQ.one (dim_of_symbol sym))
          ~free_dim:(max_dim + 1)
          m
          implicant
      in
      logf ~level:`debug "abstract_formula: abstracted @[%a@]"
        (Polyhedron.pp Format.pp_print_int) p;
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
        let rec to_int_map n map =
          try
            if n = -1 then map
            else
              to_int_map (n-1) (IntMap.add n (m n) map)
          with _ ->
            (*
            let msg =
              Format.asprintf
                "abstract_formula: dimension %d not defined, max_dim = %d, max_dim_plt = %d"
                n max_dim max_dim_plt
            in
            failwith msg
             *)
            to_int_map (n-1) map
        in
        let map = to_int_map max_dim IntMap.empty in
        let map' = extension map in
        (fun dim ->
          try IntMap.find dim map' with
          | Not_found -> m dim)
      in
      (plt, extended_univ_translation)
    in
    LocalAbstraction.{ abstract }

end

module LoosWeispfenning: sig

  val abstract_lw:
    max_dim_in_projected: int ->
    (Polyhedron.t, int -> QQ.t, dd, int -> QQ.t) LocalAbstraction.t

end = struct

  let abstract_lw ~max_dim_in_projected =
    let abstract m p =
      (*
      let () =
        BatEnum.iter
          (fun (kind, v) ->
            logf "abstract_lw: testing vector: %a" Linear.QQVector.pp v;
            let result = Linear.evaluate_affine m v in
            match kind with
            | `Zero ->
               if not (QQ.equal result QQ.zero) then
                 failwith
                   (Format.asprintf "abstract_lw: evaluated vector to %a, expected 0"
                      QQ.pp result)
               else ()
            | `Nonneg -> assert (QQ.leq QQ.zero result)
            | `Pos -> assert (QQ.lt QQ.zero result)
          )
          (Polyhedron.enum_constraints p)
      in
       *)
      let to_project =
        BatList.of_enum (Polyhedron.enum_constraints p)
        |> collect_dimensions (fun (_, v) -> v)
        |> IntSet.filter (fun dim -> dim > max_dim_in_projected)
        |> IntSet.to_list
      in
      logf ~level:`debug "abstract_lw: eliminating dimensions @[%a@] from @[%a@]"
        (Format.pp_print_list ~pp_sep:(fun fmt _ -> Format.fprintf fmt ", ")
           Format.pp_print_int)
        to_project
        (Polyhedron.pp Format.pp_print_int) p;
      let abstracted = Polyhedron.local_project m to_project p in
      logf ~level:`debug "abstract_lw: abstracted @[%a@], max_dim_in_projected = %d\n"
        (Polyhedron.pp Format.pp_print_int) abstracted max_dim_in_projected;
      let dd = abstracted
               |> Polyhedron.dd_of (max_dim_in_projected + 1) in
      ((dd, max_dim_in_projected), fun m -> m)
    in
    LocalAbstraction.{ abstract }

end

module SubspaceCone : sig

  val abstract_sc:
    max_dim_in_projected: int ->
    (Plt.t, int -> QQ.t, dd, int -> QQ.t) LocalAbstraction.t

end = struct

  module LW = LoosWeispfenning

  let closure p =
    Polyhedron.enum_constraints p
    |> BatEnum.map
         (fun (kind, v) ->
           match kind with
           | `Zero | `Nonneg -> (kind, v)
           | `Pos -> (`Nonneg, v)
         )
    |> Polyhedron.of_constraints

  let abstract_sc ~max_dim_in_projected =
    let abstract m plt =
      logf ~level:`debug "abstract_sc...";
      let abstract_lw =
        LocalAbstraction.apply (LW.abstract_lw ~max_dim_in_projected) m
      in
      let p =
        Polyhedron.enum_constraints plt.Plt.poly_part
        |> BatEnum.append (BatList.enum (plt.Plt.universe_p))
        |> Polyhedron.of_constraints
      in
      let l_constraints =
        IntLattice.basis plt.lattice_part
        |> BatList.append plt.universe_l
      in
      let closed_p = closure p in
      let (polyhedron_abstraction, _) = abstract_lw closed_p in
      let (subspace_abstraction, _) =
        let subspace_constraints =
          List.map
            (fun v ->
              ( `Zero
              , Linear.QQVector.add_term
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
             (Polyhedron.enum_constraints closed_p)
           |> Polyhedron.of_constraints
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

type plt = Plt.t

let formula_of_dd = SyntaxVector.formula_of_dd

let abstract_lw = LoosWeispfenning.abstract_lw

let abstract_sc = SubspaceCone.abstract_sc

let convex_hull srk phi terms =
  let num_terms = Array.length terms in
  let max_dim =
    match Symbol.Set.max_elt_opt (Syntax.symbols phi) with
    | None -> num_terms - 1
    | Some dim -> Syntax.int_of_symbol dim + num_terms
  in
  Format.printf "max_dim: %d, num_terms = %d@;" max_dim num_terms;
  let plt_abstraction =
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
              (fun sym -> Linear.QQVector.of_term QQ.one (dim_of_symbol sym))
              ~free_dim:0
              term
          in
          (* Terms should be in pure LRA *)
          assert (lincond.free_dim = 0);
          ( `Zero
          , Linear.QQVector.add_term (QQ.of_int (-1)) dim v
          )
          |> BatEnum.push term_defs)
        terms;
      term_defs
    in
    Plt.abstract_formula srk ~universe_p ~max_dim dim_of_symbol interp_dim
  in
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
