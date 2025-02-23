open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.iteration" end)

module V = Linear.QQVector
module CS = CoordinateSystem
module TF = TransitionFormula
module WG = WeightedGraph

module Solver = struct

  module A = BatDynArray
  type 'a t =
    { solver : 'a Abstract.Solver.t
    ; symbols : (symbol * symbol) list
    (* For wedge_hull, need to maintain formulas without preprocessing *)
    ; stack : ('a Formula.t list) A.t
    ; constants : Symbol.Set.t }

  let preprocess srk = function
    | `LIRR -> Syntax.eliminate_floor_mod_div srk
    | `LIRA -> rewrite srk ~down:(pos_rewriter srk) % (Nonlinear.linearize srk)

  let make srk ?(theory=get_theory srk) tf =
    let phi = preprocess srk theory (TF.formula tf) in
    let stack = A.singleton [TF.formula tf] in
    { solver = Abstract.Solver.make srk ~theory phi
    ; symbols = TF.symbols tf
    ; stack = stack
    ; constants = TF.symbolic_constants tf }


  let get_theory s = Abstract.Solver.get_theory s.solver

  let get_abstract_solver s = s.solver

  let get_context s = Abstract.Solver.get_context s.solver

  let get_formula s = mk_and (get_context s) (A.last s.stack)

  let get_symbols s = s.symbols

  let get_constants s = s.constants

  let get_transition_formula s =
    let all_symbols =
      List.fold_left
        (fun set (s,s') -> Symbol.Set.add s (Symbol.Set.add s' set))
        s.constants
        s.symbols
    in
    TransitionFormula.make
      ~exists:(fun s -> Symbol.Set.mem s all_symbols)
      (get_formula s)
      s.symbols

  let push s =
    Abstract.Solver.push s.solver;
    A.add s.stack (A.last s.stack)

  let pop s =
    Abstract.Solver.pop s.solver;
    A.delete_last s.stack

  let add s formulas =
    let pp_formulas =
      List.map (preprocess (get_context s) (get_theory s)) formulas
    in
    Abstract.Solver.add s.solver pp_formulas;
    A.upd s.stack (A.length s.stack - 1) (fun xs -> formulas@xs)

  let check s = Abstract.Solver.check s.solver

  let get_model s = Abstract.Solver.get_model s.solver

  let abstract s = Abstract.Solver.abstract s.solver

  let wedge_hull s =
    let post_symbols = TF.post_symbols s.symbols in
    let subterm x = not (Symbol.Set.mem x post_symbols) in
    let tf = get_transition_formula s in
    let srk = get_context s in
    Wedge.abstract ~exists:(TF.exists tf) ~subterm srk (get_formula s)
end

type 'a exp_op = 'a Solver.t -> 'a arith_term -> 'a formula

type 'a wedge_exp_op =
  'a context ->
  (symbol * symbol) list ->
  'a Wedge.t ->
  'a arith_term ->
  'a formula

module type Exp = sig
  val exp : 'a exp_op
end

module type WedgeExp = sig
  val wedge_exp : 'a wedge_exp_op
end

module type Domain = sig
  type 'a t
  val pp : 'a Solver.t -> Format.formatter -> 'a t -> unit
  val abstract : 'a Solver.t -> 'a t
  val exp_t : 'a Solver.t -> 'a t -> 'a arith_term -> 'a formula
  val exp : 'a exp_op
end

module type WedgeDomain = sig
  type 'a t
  val pp : 'a Solver.t -> Format.formatter -> 'a t -> unit
  val wedge_abstract : 'a context ->
    (symbol * symbol) list ->
    'a Wedge.t ->
    'a t
  val exp_t : 'a context -> (symbol * symbol) list -> 'a t -> 'a arith_term -> 'a formula
  val wedge_exp : 'a wedge_exp_op
end

let closure exp solver =
  let srk = Solver.get_context solver in
  let loop_counter_sym = mk_symbol srk ~name:"K" `TyInt in
  let loop_counter = mk_const srk loop_counter_sym in
  mk_and srk [ exp solver loop_counter
             ; mk_leq srk (mk_zero srk) loop_counter]

let product exps solver loop_counter =
  List.map (fun exp -> exp solver loop_counter) exps
  |> mk_and (Solver.get_context solver)

let wedge_product exps srk tr_symbols wedge loop_counter =
  List.map (fun exp -> exp srk tr_symbols wedge loop_counter) exps
  |> mk_and srk

let wedge_lift wedge_exp solver loop_counter =
  wedge_exp
    (Solver.get_context solver)
    (Solver.get_symbols solver)
    (Solver.wedge_hull solver)
    loop_counter

module Cartesian = struct
  type 'a t =
    { pre : 'a formula
    ; post : 'a formula }

  let pp solver formatter k =
    let srk = Solver.get_context solver in
    Format.fprintf formatter "pre:@;  @[<v 0>%a@]@;post:@;  @[<v 0>%a@]"
      (Formula.pp srk) k.pre
      (Formula.pp srk) k.post

  let exp srk tr_symbols k loop_counter =
    let identity = TF.formula (TF.identity srk tr_symbols) in
    mk_or srk [ mk_and srk [ mk_eq srk loop_counter (mk_real srk QQ.zero)
                           ; identity ]
              ; mk_and srk [ mk_leq srk (mk_real srk QQ.one) loop_counter
                           ; k.pre
                           ; k.post ] ]

  let precondition k = k.pre

  let postcondition k = k.post
end

module LIRRGuard = struct
  type 'a t = 'a Cartesian.t

  let pp = Cartesian.pp

  let abstract solver =
    let srk = Solver.get_context solver in
    let consts = Solver.get_constants solver in
    let abs_solver = Solver.get_abstract_solver solver in
    let pre_simulation =
      Symbol.Set.union consts (TF.pre_symbols (Solver.get_symbols solver))
      |> Symbol.Set.elements
      |> List.map (mk_const srk)
      |> Array.of_list
    in
    let post_simulation =
      Symbol.Set.union consts (TF.post_symbols (Solver.get_symbols solver))
      |> Symbol.Set.elements
      |> List.map (mk_const srk)
      |> Array.of_list
    in
    let pre =
      ConsequenceCone.abstract abs_solver pre_simulation
      |> PolynomialCone.to_formula srk (Array.get pre_simulation)
    in
    let post =
      ConsequenceCone.abstract abs_solver post_simulation
      |> PolynomialCone.to_formula srk (Array.get post_simulation)
    in
    Cartesian.{ pre; post }

  let exp_t solver =
    Cartesian.exp (Solver.get_context solver) (Solver.get_symbols solver)

  let exp solver loop_counter = exp_t solver (abstract solver) loop_counter
end

module WedgeGuard = struct
  type 'a t = 'a Cartesian.t

  let pp = Cartesian.pp

  let wedge_abstract _srk tr_symbols wedge =
    let pre_symbols = TF.pre_symbols tr_symbols in
    let post_symbols = TF.post_symbols tr_symbols in
    let pre =
      Wedge.exists (not % flip Symbol.Set.mem post_symbols) wedge
      |> Wedge.to_formula
    in
    let post =
      Wedge.exists (not % flip Symbol.Set.mem pre_symbols) wedge
      |> Wedge.to_formula
    in
    Cartesian.{ pre; post }

  let exp_t = Cartesian.exp

  let wedge_exp srk tr_symbols wedge loop_counter =
    exp_t srk tr_symbols (wedge_abstract srk tr_symbols wedge) loop_counter
end

module PolyhedronGuard = struct
  type 'a t = 'a Cartesian.t

  let pp = Cartesian.pp

  let abstract solver =
    let srk = Solver.get_context solver in
    let consts = Solver.get_constants solver in
    let pre_simulation =
      Symbol.Set.union consts (TF.pre_symbols (Solver.get_symbols solver))
      |> Symbol.Set.elements
      |> List.map (mk_const srk)
      |> Array.of_list
    in
    let post_simulation =
      Symbol.Set.union consts (TF.post_symbols (Solver.get_symbols solver))
      |> Symbol.Set.elements
      |> List.map (mk_const srk)
      |> Array.of_list
    in
    let abs_solver = Solver.get_abstract_solver solver in
    let pre =
      ConvexHull.abstract abs_solver pre_simulation
      |> DD.enum_constraints
      |> BatEnum.map (Polyhedron.formula_of_constraint srk (Array.get pre_simulation))
      |> BatList.of_enum
      |> mk_and srk
    in
    let post =
      ConvexHull.abstract abs_solver post_simulation
      |> DD.enum_constraints
      |> BatEnum.map (Polyhedron.formula_of_constraint srk (Array.get post_simulation))
      |> BatList.of_enum
      |> mk_and srk
    in
    Cartesian.{ pre; post }

  let exp_t solver =
    Cartesian.exp (Solver.get_context solver) (Solver.get_symbols solver)

  let exp solver loop_counter =
    exp_t solver (abstract solver) loop_counter
end

module LinearGuard = struct
  type 'a t = 'a Cartesian.t

  let pp = Cartesian.pp

  let abstract solver =
    let tr_symbols = Solver.get_symbols solver in
    let pre_symbols = TF.pre_symbols tr_symbols in
    let post_symbols = TF.post_symbols tr_symbols in
    let constants = Solver.get_constants solver in
    let abs_solver = Solver.get_abstract_solver solver in
    let pre =
      Quantifier.exists_elim
        abs_solver
        (fun x -> Symbol.Set.mem x constants || Symbol.Set.mem x pre_symbols)
    in
    let post =
      Quantifier.exists_elim
        abs_solver
        (fun x -> Symbol.Set.mem x constants || Symbol.Set.mem x post_symbols)
    in
    Cartesian.{ pre; post }

  let exp_t solver =
    Cartesian.exp (Solver.get_context solver) (Solver.get_symbols solver)

  let exp solver loop_counter =
    exp_t solver (abstract solver) loop_counter
end

module GuardedTranslation = struct
  type 'a t =
    { simulation : 'a arith_term array;
      translation : QQ.t array;

      (* Guard is expressed over free variables 0..n, where n is
         dimension of the translation (minus 1). *)
      guard : 'a formula
    }

  let pp solver formatter gt =
    let srk = Solver.get_context solver in
    Format.fprintf formatter "@[<v 0>";
    gt.simulation |> Array.iteri (fun i t ->
        Format.fprintf formatter "%a += %a@;"
          (ArithTerm.pp srk) t
          QQ.pp gt.translation.(i));
    Format.fprintf formatter "@;when @[<v 0>%a@]"
      (Formula.pp srk)
      (substitute srk (fun (i, _) -> gt.simulation.(i)) gt.guard);
    Format.fprintf formatter "@]"

  let abstract solver =
    let srk = Solver.get_context solver in
    let zz_symbols = (* int-sorted transition symbols *)
      List.filter (fun (s,s') ->
          typ_symbol srk s = `TyInt
          && typ_symbol srk s' = `TyInt)
        (Solver.get_symbols solver)
    in
    (* [1, x0' - x0, ..., xn' - xn] *)
    let delta =
      [mk_one srk]
      @(List.map (fun (s,s') ->
            mk_sub srk (mk_const srk s') (mk_const srk s))
          zz_symbols)
      |> Array.of_list
    in
    let abs_solver = Solver.get_abstract_solver solver in
    let (simulation, translation) =
      let pre_symbols =
        List.map (fun (s,_) -> mk_const srk s) zz_symbols
        |> BatArray.of_list
      in
      List.fold_left (fun (sim,tr) vec ->
          (* Scale vec so that it has integer coefficients. *)
          let common_denom =
            (BatEnum.fold
               (fun lcm (coeff, _) -> ZZ.lcm lcm (QQ.denominator coeff))
               ZZ.one
               (V.enum vec))
          in
          let vec = V.scalar_mul (QQ.of_zz common_denom) vec in
          let (const, functional) = V.pivot 0 vec in
          (Linear.term_of_vec srk (fun i -> pre_symbols.(i-1)) functional::sim,
           const::tr))
        ([], [])
        (Abstract.LinearSpan.abstract abs_solver delta)
    in
    (* exists x,x'. F(x,x') /\ Sx = y *)
    let guard =
      let fresh_symbols =
        List.map (fun _ -> mk_symbol srk `TyInt) simulation
      in
      let sym_to_var =
        BatList.fold_lefti (fun m i s ->
            Symbol.Map.add s (mk_var srk i `TyInt) m)
          Symbol.Map.empty
          fresh_symbols
      in
      let sx_eq_y =
        List.map2 (fun s t -> mk_eq srk (mk_const srk s) t) fresh_symbols simulation
      in
      Abstract.Solver.push abs_solver;
      Abstract.Solver.add abs_solver sx_eq_y;
      let result =
        Quantifier.exists_elim
          abs_solver
          (fun x -> Symbol.Map.mem x sym_to_var)
        |> substitute_map srk sym_to_var
      in
      Abstract.Solver.pop abs_solver;
      result
    in
    { simulation = Array.of_list simulation;
      translation = Array.of_list translation;
      guard = guard }

  let exp_translation srk term_of_dim loop_counter gt =
    BatList.init
      (Array.length gt.simulation)
      (fun i ->
        mk_eq srk (term_of_dim i)
          (mk_mul srk [mk_real srk gt.translation.(i);
                       loop_counter]))
    |> mk_and srk

  let exp_t solver gt loop_counter =
    let srk = Solver.get_context solver in
    let tr_symbols = Solver.get_symbols solver in
    let post_map = (* map pre-state vars to post-state vars *)
      TF.post_map srk tr_symbols
    in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          Symbol.Map.find sym post_map
        else
          mk_const srk sym
      in
      substitute_const srk subst
    in
    (* forall subcounter. 0 <= subcounter < loop_counter ==> G(Sx + t*subcounter) *)
    let subcounter = mk_symbol srk `TyInt in
    let subcounter_term = mk_const srk subcounter in
    let guard =
      let cf = (* Sx + t*subcounter *)
        Array.mapi (fun i t ->
            mk_add srk [t; mk_mul srk [subcounter_term; mk_real srk gt.translation.(i)]])
          gt.simulation
      in
      mk_if srk
        (mk_and srk [mk_leq srk (mk_int srk 0) subcounter_term;
                     mk_lt srk subcounter_term loop_counter])
        (substitute srk (fun (i,_) -> cf.(i)) gt.guard)
      |> mk_not srk
      |> Quantifier.mbp srk (fun x -> x != subcounter)
      |> mk_not srk
    in
    let delta i =
      mk_sub srk (postify gt.simulation.(i)) (gt.simulation.(i))
    in
    mk_and srk
      [guard;
       exp_translation srk delta loop_counter gt]

  let exp solver loop_counter =
    exp_t solver (abstract solver) loop_counter
end

module LossyTranslation = struct
  type 'a t = ('a arith_term * [ `Geq | `Eq ] * QQ.t) list

  let pp solver formatter lr =
    let srk = Solver.get_context solver in
    Format.fprintf formatter "@[<v 0>";
    lr |> List.iter (fun (t, op, k) ->
        let opstring = match op with
          | `Geq -> ">="
          | `Eq -> "="
        in
        Format.fprintf formatter "%a %s %a@;" (ArithTerm.pp srk) t opstring QQ.pp k);
    Format.fprintf formatter "@]"

  let abstract solver =
    let srk = Solver.get_context solver in
    let delta =
      List.map
        (fun (s,s') -> mk_sub srk (mk_const srk s') (mk_const srk s))
        (Solver.get_symbols solver)
      |> Array.of_list
    in
    let abs_solver = Solver.get_abstract_solver solver in
    DD.enum_constraints (ConvexHull.abstract abs_solver delta)
    /@ (fun (kind, vec) ->
        let (k, vec) = V.pivot Linear.const_dim vec in
        let t = Linear.term_of_vec srk (Array.get delta) vec in
        let k = QQ.negate k in
        match kind with
        | `Zero -> (t, `Eq, k)
        | `Nonneg | `Pos -> (t, `Geq, k))
    |> BatList.of_enum

  let exp_t solver lr loop_counter =
    let srk = Solver.get_context solver in
    List.map (fun (delta, op, c) ->
        match op with
        | `Eq ->
          mk_eq srk (mk_mul srk [mk_real srk c; loop_counter]) delta
        | `Geq ->
          mk_leq srk (mk_mul srk [mk_real srk c; loop_counter]) delta)
      lr
    |> mk_and srk

  let exp solver loop_counter =
    exp_t solver (abstract solver) loop_counter
end

module NonlinearRecurrenceInequation = struct
  type 'a t = ('a arith_term * [ `Geq | `Eq ] * 'a arith_term) list

  let pp solver formatter lr =
    let srk = Solver.get_context solver in
    Format.fprintf formatter "NLE: @[<v 0>";
    lr |> List.iter (fun (t, op, k) ->
        let opstring = match op with
          | `Geq -> ">="
          | `Eq -> "="
        in
        Format.fprintf formatter "%a %s %a@;" (ArithTerm.pp srk) t opstring (ArithTerm.pp srk) k);
    Format.fprintf formatter "@]"

  module QQXs = Polynomial.QQXs

  let abstract_delta_wedge srk delta_wedge delta delta_map =
    let cs = Wedge.coordinate_system delta_wedge in
    let delta_dim =
      let dims =
        List.fold_left (fun dims delta ->
            try SrkUtil.Int.Set.add (CS.cs_term_id cs (`App (delta, []))) dims
            with Not_found -> dims)
          SrkUtil.Int.Set.empty
          delta
      in
      fun i -> SrkUtil.Int.Set.mem i dims
    in
    let constraint_of_atom atom =
      match Formula.destruct srk atom with
      | `Atom (`Arith (op, s, t)) ->
        let t = V.sub (CS.vec_of_term cs t) (CS.vec_of_term cs s) in
        let (lhs, rhs) =
          BatEnum.fold (fun (lhs, rhs) (coeff, dim) ->
              if delta_dim dim then
                (V.add_term coeff dim lhs, rhs)
              else
                (lhs, V.add_term (QQ.negate coeff) dim rhs))
            (V.zero, V.zero)
            (V.enum t)
        in
        if V.equal lhs V.zero then
          None
        else
          let lhs = substitute_map srk delta_map (CS.term_of_vec cs lhs) in
          let rhs = CS.term_of_vec cs rhs in
          begin match op with
            | `Leq | `Lt -> Some (lhs, `Geq, rhs)
            | `Eq -> Some (lhs, `Eq, rhs)
          end
      | _ -> assert false
    in
    if Wedge.is_bottom delta_wedge then
      []
    else
      BatList.filter_map constraint_of_atom (Wedge.to_atoms delta_wedge)

  let make_deltas srk tr_symbols =
    let delta =
      List.map (fun (s,_) ->
          let name = "delta_" ^ (show_symbol srk s) in
          mk_symbol srk ~name (typ_symbol srk s))
        tr_symbols
    in
    let delta_map =
      List.fold_left2 (fun map delta (s,s') ->
          Symbol.Map.add
            delta
            (mk_sub srk (mk_const srk s') (mk_const srk s))
            map)
        Symbol.Map.empty
        delta
        tr_symbols
    in
    (delta, delta_map)

  let wedge_abstract srk tr_symbols wedge =
    let (delta,delta_map) = make_deltas srk tr_symbols in
    let syms =
      List.fold_left (fun set (s,s') ->
          Symbol.Set.add s (Symbol.Set.add s' set))
        Symbol.Set.empty
        tr_symbols
    in
    let delta_wedge =
      let exists x = not (Symbol.Set.mem x syms) in
      let subterm x = not (Symbol.Map.mem x delta_map) in
      let delta_constraints =
        Symbol.Map.fold (fun s diff xs ->
            (mk_eq srk (mk_const srk s) diff)::xs)
          delta_map
          []
      in
      let delta_wedge = Wedge.copy wedge in
      Wedge.meet_atoms delta_wedge delta_constraints;
      Wedge.exists ~subterm exists delta_wedge
    in
    abstract_delta_wedge srk delta_wedge delta delta_map

  let exp_t srk _ lr loop_counter =
    List.map (fun (delta, op, c) ->
        match op with
        | `Eq ->
          mk_eq srk (mk_mul srk [c; loop_counter]) delta
        | `Geq ->
          mk_leq srk (mk_mul srk [c; loop_counter]) delta)
      lr
    |> mk_and srk

  let wedge_exp srk tr_symbols wedge loop_counter =
    exp_t srk tr_symbols (wedge_abstract srk tr_symbols wedge) loop_counter
end

let split exp solver loop_counter =
  let srk = Solver.get_context solver in
  let tr_symbols = Solver.get_symbols solver in
  let constants = Solver.get_constants solver in
  let pre_symbols = TF.pre_symbols tr_symbols in
  let prestate sym =
    Symbol.Set.mem sym pre_symbols || Symbol.Set.mem sym constants
  in
  let body = Solver.get_formula solver in
  let predicates =
    let preds = ref Expr.Set.empty in
    let rr expr =
      match destruct srk expr with
      | `Not phi ->
        if Symbol.Set.for_all prestate (symbols phi) then
          preds := Expr.Set.add phi (!preds);
        expr
      | `Atom (`Arith (op, s, t)) ->
        let phi =
          match op with
          | `Eq -> mk_eq srk s t
          | `Leq -> mk_leq srk s t
          | `Lt -> mk_lt srk s t
        in
        begin
          if Symbol.Set.for_all prestate (symbols phi) then
            let redundant = match op with
              | `Eq -> false
              | `Leq ->
                Expr.Set.mem (SrkSimplify.simplify_terms srk (mk_lt srk t s)) (!preds)
              | `Lt ->
                Expr.Set.mem (SrkSimplify.simplify_terms srk (mk_leq srk t s)) (!preds)
            in
            if not redundant then
              preds := Expr.Set.add phi (!preds)
        end;
        expr
      | _ -> expr
    in
    ignore (rewrite srk ~up:rr body);
    BatList.of_enum (Expr.Set.enum (!preds))
  in
  let sat_modulo_body psi =
    let psi =
      rewrite srk
        ~up:(Nonlinear.uninterpret_rewriter srk)
        psi
    in
    Solver.push solver;
    Solver.add solver [psi];
    let result = Solver.check solver in
    Solver.pop solver;
    result
  in
  let is_split_predicate psi =
    (sat_modulo_body psi = `Sat)
    && (sat_modulo_body (mk_not srk psi) = `Sat)
  in
  let post_map = TF.post_map srk tr_symbols in
  let postify =
    let subst sym =
      if Symbol.Map.mem sym post_map then
        Symbol.Map.find sym post_map
      else
        mk_const srk sym
    in
    substitute_const srk subst
  in
  let exp_modulo predicate loop_counter =
    Solver.push solver;
    Solver.add solver [predicate];
    let result = exp solver loop_counter in
    Solver.pop solver;
    mk_and srk [ result
               ; mk_or srk [ mk_eq srk (mk_zero srk) loop_counter
                           ; predicate ] ]
  in
  let split_exp p not_p =
    let left_counter = mk_const srk (mk_symbol srk ~name:"K" `TyInt) in
    let right_counter = mk_const srk (mk_symbol srk ~name:"K" `TyInt) in
    let left_exp = exp_modulo not_p left_counter in
    let right_exp = exp_modulo p right_counter in
    let left_right =
      TF.mul srk
        (TF.make left_exp tr_symbols)
        (TF.make right_exp tr_symbols)
      |> TF.formula
    in
    mk_and srk [left_right;
                mk_eq srk (mk_add srk [left_counter; right_counter]) loop_counter]
  in
  let try_split_predicate psi =
    if is_split_predicate psi then
      let not_psi = mk_not srk psi in
      let post_psi = postify psi in
      let post_not_psi = postify not_psi in
      if sat_modulo_body (mk_and srk [psi; post_not_psi]) = `Unsat then
        (* {psi} body {psi} -> body* = ([not psi]body)*([psi]body)* *)
        Some (split_exp psi not_psi)
      else if sat_modulo_body (mk_and srk [not_psi; post_psi]) = `Unsat then
        (* {not phi} body {not phi} -> body* = ([phi]body)*([not phi]body)* *)
        Some (split_exp not_psi psi)
      else
        None
    else
      None
  in
  let split_iter = BatList.filter_map try_split_predicate predicates in
  match split_iter with
  | [] ->
    (* If there are no predicates that can split the loop, default to exp *)
    exp solver loop_counter
  | _ -> mk_and srk split_iter


(* A transition p(x,x') predicate is invariant for a transition relation T(x,x') if
   T(x,x') /\ T(x',x'') /\ p(x,x') |= p(x',x'')
   (i.e., if p holds on some iteration, it must hold on all subsequent iterations).
   This procedure finds the subset of the input set of predicates that are invariant *)
let invariant_transition_predicates srk tf predicates =
  (* map' sends primed vars to midpoints; map sends unprimed vars to midpoints *)
  let (map', map) =
    List.fold_left (fun (subst1, subst2) (sym, sym') ->
        let mid_name = "mid_" ^ (show_symbol srk sym) in
        let mid_symbol =
          mk_symbol srk ~name:mid_name (typ_symbol srk sym)
        in
        let mid = mk_const srk mid_symbol in
        (Symbol.Map.add sym' mid subst1,
         Symbol.Map.add sym mid subst2))
      (Symbol.Map.empty, Symbol.Map.empty)
      (TF.symbols tf)
  in
  let seq = (* T(x,x_mid) /\ T(x_mid,x') *)
    let rename = (* rename Skolem constants *)
      Memo.memo (fun symbol ->
          mk_const srk (mk_symbol srk (typ_symbol srk symbol)))
    in
    (* substitution for first iteration *)
    let subst1 symbol =
      if Symbol.Map.mem symbol map' then
        Symbol.Map.find symbol map'
      else if TF.exists tf symbol then
        mk_const srk symbol
      else rename symbol
    in
    mk_and srk [substitute_const srk subst1 (TF.formula tf);
                substitute_map srk map (TF.formula tf)]
  in
  let solver = Smt.Solver.make srk in
  let models = ref [] in
  Smt.Solver.add solver [seq];
  let is_invariant p =
    let inv = mk_if srk (substitute_map srk map' p) (substitute_map srk map p) in
    List.for_all (fun m -> Smt.Model.sat m inv) !models && begin
        Smt.Solver.push solver;
        Smt.Solver.add solver [mk_not srk inv];
        match Smt.Solver.get_model solver with
        | `Sat m ->
           Smt.Solver.pop solver 1;
           models := m::(!models);
           false
        | `Unsat ->
           Smt.Solver.pop solver 1;
           true
        | `Unknown ->
           Smt.Solver.pop solver 1;
           false
      end
  in
  if Smt.Solver.check solver = `Unsat then
    []
  else
    List.filter is_invariant predicates

(* Each cell is i, (pos_pred_indices, neg_pred_indices), cell_formula *)
let invariant_partition srk candidates tf =
    let tf = if get_theory srk = `LIRR then tf else TF.linearize srk tf in
    logf "formula to be partitioned: %a" (Formula.pp srk) (TF.formula tf);
    let predicates =
      invariant_transition_predicates srk tf candidates
      |> BatArray.of_list
    in
    let solver = Smt.Solver.make srk in
    Smt.Solver.add solver [TF.formula tf];
    (* The predicate induce a parition of the transitions of T by
       their valuation of the predicates; find the cells of this
       partition *)
    let rec find_cells cells =
      Smt.Solver.push solver;
      match Smt.Solver.get_model solver with
      | `Sat m ->
        logf "transition formula SAT, finding cell";
         let cell =
           Array.map (Smt.Model.sat m) predicates
         in
         let new_cell =
          BatList.fold_lefti (
            fun (true_preds, false_preds) i sat ->
              if sat then (BatSet.Int.add i true_preds, false_preds)
              else (true_preds, BatSet.Int.add i false_preds))
              (BatSet.Int.empty, BatSet.Int.empty)
              (Array.to_list cell)
          in
         let new_cell_formula =
           List.mapi (fun i sat ->
               if sat then predicates.(i)
               else mk_not srk predicates.(i))
             (Array.to_list cell)
           |> mk_and srk
         in
         logf "adding cell: %a" (Formula.pp srk) new_cell_formula;
         Smt.Solver.add solver [mk_not srk new_cell_formula];
         find_cells ((new_cell, new_cell_formula)::cells)
      | `Unsat ->
        logf "transition formula UNSAT, no further cells";
        cells
      | `Unknown -> assert false (* to do *)
    in
    predicates, find_cells []

let mp_algebra srk nonterm = WG.{
      omega = (fun tf -> nonterm (Solver.make srk tf));
      omega_add = (fun p1 p2 -> Syntax.mk_or srk [p1; p2]);
      omega_mul = (fun transition state -> TF.preimage srk transition state ) }

let tf_algebra srk symbols star = WG.{
      mul = TF.mul srk;
      add = TF.add srk;
      one = TF.identity srk symbols;
      zero = TF.zero srk symbols;
      star = (fun tf -> star (Solver.make srk tf))
    }

let phase_graph srk tf candidates algebra =
  let inv_predicates, cells = invariant_partition srk candidates tf in
  let num_cells = BatList.length cells in
  (* map' sends primed vars to midpoints; map sends unprimed vars to midpoints *)
  logf "start building phase transition graph";
  let (map', map) =
    List.fold_left (fun (subst1, subst2) (sym, sym') ->
        let mid_name = "mid_" ^ (show_symbol srk sym) in
        let mid_symbol =
          mk_symbol srk ~name:mid_name (typ_symbol srk sym)
        in
        let mid = mk_const srk mid_symbol in
        (Symbol.Map.add sym' mid subst1,
         Symbol.Map.add sym mid subst2))
      (Symbol.Map.empty, Symbol.Map.empty)
      (TF.symbols tf)
  in
  let seq = (* T(x,x_mid) /\ T(x_mid,x') *)
    let rename = (* rename Skolem constants *)
      Memo.memo (fun symbol ->
          mk_const srk (mk_symbol srk (typ_symbol srk symbol)))
    in
    (* substitution for first iteration *)
    let subst1 symbol =
      if Symbol.Map.mem symbol map' then
        Symbol.Map.find symbol map'
      else if TF.exists tf symbol then
        mk_const srk symbol
      else rename symbol
    in
    mk_and srk [substitute_const srk subst1 (TF.formula tf);
                substitute_map srk map (TF.formula tf)]
  in
  let solver = Smt.Solver.make srk in
  Smt.Solver.add solver [seq];
  let indicators =
    BatArray.mapi (fun ind predicate ->
        let indicator =
          mk_symbol srk ~name:("ind_1_for_pred_" ^ (string_of_int ind)) `TyBool
          |> mk_const srk
        in
        let indicator' =
          mk_symbol srk ~name:("ind_2_for_pred_" ^ (string_of_int ind)) `TyBool
          |> mk_const srk
        in
        let pred = (* p(x, x_mid) *) substitute_map srk map' predicate in
        let pred' = (* p(x_mid, x') *) substitute_map srk map predicate in
        Smt.Solver.add solver
          [mk_iff srk indicator pred;
           mk_iff srk indicator' pred'];
        (indicator, indicator'))
      inv_predicates
  in

  let can_follow (cell1_pos,cell1_neg) (cell2_pos,cell2_neg) =
    BatSet.Int.subset cell1_pos cell2_pos &&
      begin
        let cond_pos_clause =
          (BatSet.Int.to_list cell1_pos)
          |> BatList.map (fun ind -> fst (indicators.(ind)))
        in
        let cond_neg_clause =
          (BatSet.Int.to_list cell1_neg)
          |> BatList.map (fun ind -> mk_not srk (fst (indicators.(ind))))
        in
        let new_pos_inds = BatSet.Int.diff cell2_pos cell1_pos in
        let result_pos_clause =
          (BatSet.Int.to_list new_pos_inds)
          |> BatList.map (fun ind -> snd (indicators.(ind)))
        in
        let result_neg_clause =
          (BatSet.Int.to_list cell2_neg)
          |> BatList.map (fun ind -> mk_not srk (snd (indicators.(ind))))
        in
        let cell2_can_follow_cell1 =
          cond_neg_clause@cond_pos_clause@result_neg_clause@result_pos_clause
        in
        Smt.Solver.check ~assumptions:cell2_can_follow_cell1 solver != `Unsat
      end
  in

  (* self-loop for every cell with weight tf /\ cell_formula *)
  let wg =
    ref (BatList.fold_lefti (fun wg cell_ind ((_, _), cell_formula) ->
             let cell_tf = TF.map_formula (fun f -> mk_and srk [f; cell_formula]) tf in
             WG.add_edge (WG.add_vertex wg cell_ind) cell_ind cell_tf cell_ind)
           (WG.empty algebra)
           cells)
  in

  (*  Ranked cells is a map from int to (list of sets), where int is the number of
      positive predicates. *)
  let ranked_cells =
    BatList.fold_lefti
      (fun m i ((positive_preds, negative_preds), _) ->
        BatMap.Int.modify_def []
          (BatSet.Int.cardinal positive_preds)
          (fun xs -> (i, (positive_preds, negative_preds))::xs)
          m)
      BatMap.Int.empty
      cells
  in
  let levels = BatArray.of_enum (BatMap.Int.keys ranked_cells) in
  let ancestors = BatArray.make num_cells BatSet.Int.empty in
  let descendants = BatArray.make num_cells BatSet.Int.empty in
  (* There can be an edge i -> j only if rank i < rank j *)
  for current_level_idx = 1 to (BatArray.length levels) - 1 do
    let current_level = levels.(current_level_idx) in
    logf "current level = %d" current_level;
    let targets = BatMap.Int.find current_level ranked_cells in
    for prev_level_idx = current_level_idx - 1 downto 0 do
      let prev_level = levels.(prev_level_idx) in
      logf "previous level = %d" prev_level;
      let sources = BatMap.Int.find prev_level ranked_cells in
      BatList.iter (fun (i, cell_i) ->
          BatList.iter (fun (j, cell_j) ->
              if not (BatSet.Int.mem j descendants.(i))
                 && can_follow cell_i cell_j then
                begin
                  wg := WG.add_edge !wg i algebra.one j;
                  (* Add i and i's ancestors into j's ancestors set *)
                  ancestors.(j) <-
                    BatSet.Int.add i (BatSet.Int.union ancestors.(i) ancestors.(j));
                  (* Add j to all its ancestors' descendants sets *)
                  BatSet.Int.iter (fun k ->
                      descendants.(k) <- BatSet.Int.add j descendants.(k))
                    ancestors.(j);
                end)
            targets)
        sources;
    done;
  done;
  !wg

let phase_mp srk candidate_predicates star nonterm solver =
  let tf = Solver.get_transition_formula solver in
  let algebra = tf_algebra srk (Solver.get_symbols solver) star in
  let wg = phase_graph srk tf candidate_predicates algebra in
  (* node (-1) is virtual entry.  Add edges to all isolated vertices
     (only one in-edge, from its self-loop).  *)
  let wg =
    WG.fold_vertex (fun v wg ->
        if WG.U.in_degree (WG.forget_weights wg) v == 1 then
            WG.add_edge wg (-1) algebra.one v
        else
          wg)
      wg
      (WG.add_vertex wg (-1))
  in
  WG.omega_path_weight wg (mp_algebra srk nonterm) (-1)

let invariant_direction exp solver loop_counter =
  let tr_symbols = Solver.get_symbols solver in
  let srk = Solver.get_context solver in
  let abs_solver = Solver.get_abstract_solver solver in
  (* Use variable directions as candidate transition invariants *)
  let predicates =
    List.concat (List.map (fun (x,x') ->
        let x = mk_const srk x in
        let x' = mk_const srk x' in
        [mk_lt srk x x';
         mk_lt srk x' x;
         mk_eq srk x x'])
        tr_symbols)
    |> invariant_transition_predicates srk (Solver.get_transition_formula solver)
    |> BatArray.of_list
  in
  (* The predicate induce a parition of the transitions of T by
     their valuation of the predicates; find the cells of this
     partition *)
  let rec find_cells cells =
    match Abstract.Solver.get_model abs_solver with
    | `Sat m ->
      let cell =
        Array.map (Abstract.Model.sat srk m) predicates
      in
      let cell_formula =
        List.mapi (fun i sat ->
            if sat then predicates.(i)
            else mk_not srk predicates.(i))
          (Array.to_list cell)
        |> mk_and srk
      in
      Abstract.Solver.block abs_solver cell_formula;
      find_cells (cell::cells)
    | `Unsat -> cells
    | `Unknown -> assert false (* to do *)
  in
  (* # of true predicates.  Since they're invariant, transitions
     belonging to a low-weight cell must precede transitions from
     higher-weight cells, and cells with equal weight can't appear
     in an execution *)
  let compare_weight cell1 cell2 =
    let weight cell =
      Array.fold_left (fun i v -> if v then i+1 else i) 0 cell
    in
    compare (weight cell1) (weight cell2)
  in
  let cells = Abstract.Solver.with_blocking abs_solver find_cells [] in
  let exp_cell subst k cell =
    let cell_predicates =
      BatArray.fold_lefti
        (fun ps i v ->
           if v then predicates.(i)::ps
           else mk_not srk predicates.(i)::ps)
        []
        cell
    in
    Solver.push solver;
    Solver.add solver cell_predicates;
    let result = exp solver k in
    Solver.pop solver;
    substitute_map srk subst result
  in
  let exp_group mid_symbols k cells =
    let subst =
      BatList.fold_left2 (fun m (x, x') (sym, sym') ->
          Symbol.Map.add sym (mk_const srk x)
            (Symbol.Map.add sym' (mk_const srk x') m))
        Symbol.Map.empty
        mid_symbols
        tr_symbols
    in
    List.map (exp_cell subst k) cells
    |> mk_or srk
  in
  let groups =
    BatList.sort compare_weight cells
    |> BatList.group_consecutive (fun x y -> compare_weight x y = 0)
  in
  let rec go groups tr_symbols exp_formulas loop_counters =
    match groups with
    | [ ] ->
      (* formula is unsat *)
      assert (loop_counters == []);
      assert (exp_formulas == []);
      ([TF.formula (TF.identity srk tr_symbols)],
       [mk_real srk QQ.zero])
    | [x] ->
      let k = mk_const srk (mk_symbol srk ~name:"k" `TyInt) in
      ((exp_group tr_symbols k x)::exp_formulas,
       k::loop_counters)
    | (x::xs) ->
      let mid =
        List.map (fun (sym, _) ->
            let name = "mid_" ^ (show_symbol srk sym) in
            mk_symbol srk ~name:name (typ_symbol srk sym))
          tr_symbols
      in
      let tr_symbols1 =
        BatList.map2 (fun (sym, _) sym' -> (sym, sym')) tr_symbols mid
      in
      let tr_symbols2 =
        BatList.map2 (fun sym (_, sym') -> (sym, sym')) mid tr_symbols
      in
      let k = mk_const srk (mk_symbol srk ~name:"k" `TyInt) in
      go xs tr_symbols2 ((exp_group tr_symbols1 k x)::exp_formulas) (k::loop_counters)
  in
  let (formulas, loop_counters) =
    go groups tr_symbols [] []
  in
  mk_and srk (mk_eq srk loop_counter (mk_add srk loop_counters)::formulas)
