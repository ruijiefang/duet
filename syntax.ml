open BatHashcons

type typ = [
  | `TyInt
  | `TyReal
  | `TyBool
  | `TyFun of (typ list) * typ
] [@@ deriving ord]

type typ_arith = [ `TyInt | `TyReal ] [@@ deriving ord]
type typ_bool = [ `TyBool ]
type typ_fo = [ `TyInt | `TyReal | `TyBool ] [@@ deriving ord]
type 'a typ_fun = [ `TyFun of (typ list) * 'a ]

type const_sym = int

let rec pp_typ formatter = function
  | `TyReal -> Format.pp_print_string formatter "real"
  | `TyInt -> Format.pp_print_string formatter "int"
  | `TyBool -> Format.pp_print_string formatter "bool"
  | `TyFun (dom, cod) ->
    let pp_sep formatter () = Format.fprintf formatter "@ * " in
    Format.fprintf formatter "(@[%a@ -> %a@])"
      (ApakEnum.pp_print_enum ~pp_sep pp_typ) (BatList.enum dom)
      pp_typ cod

let pp_typ_arith = pp_typ
let pp_typ_fo = pp_typ

type label =
  | True
  | False
  | And
  | Or
  | Not
  | Exists of string * typ_fo
  | Forall of string * typ_fo
  | Eq
  | Leq
  | Lt
  | Const of const_sym
  | Var of int * typ_fo
  | Add
  | Mul
  | Div
  | Mod
  | Floor
  | Neg
  | Real of QQ.t

type sexpr = Node of label * ((sexpr hobj) list)
type formula = sexpr hobj
type term = sexpr hobj

module HC = BatHashcons.MakeTable(struct
    type t = sexpr
    let equal (Node (label, args)) (Node (label', args')) =
      (match label, label' with
       | Exists (_, typ), Exists (_, typ') -> typ = typ'
       | Forall (_, typ), Forall (_, typ') -> typ = typ'
       | _, _ -> label = label')
      && List.length args == List.length args'
      && List.for_all2 (fun x y -> x.tag = y.tag) args args'
    let compare = Pervasives.compare
    let hash (Node (label, args)) =
      Hashtbl.hash (label, List.map (fun sexpr -> sexpr.tag) args)
  end)

module type Constant = sig
  type t
  val pp : Format.formatter -> t -> unit
  val typ : t -> typ
  val hash : t -> int
  val equal : t -> t -> bool
end

module ConstSymbol = Apak.Putil.PInt

module Var = struct
  module I = struct
    type t = int * typ_fo [@@deriving show,ord]
  end
  include I
  module Set = Apak.Putil.Set.Make(I)
  module Map = Apak.Putil.Map.Make(I)
end
module Env = struct
  type 'a t = 'a list
  let push x xs = x::xs
  let find xs i =
    try List.nth xs i
    with Failure _ -> raise Not_found
  let empty = []
end


module TypedString = struct
  type t = string * typ
  let pp formatter (name, _) = Format.pp_print_string formatter name
  let typ = snd
  let hash = Hashtbl.hash
  let equal = (=)
end

let rec eval_sexpr alg sexpr =
  let (Node (label, children)) = sexpr.obj in
  alg label (List.map (eval_sexpr alg) children)

let rec flatten_sexpr label sexpr =
  let Node (label', children) = sexpr.obj in
  if label = label' then
    List.concat (List.map (flatten_sexpr label) children)
  else
    [sexpr]

type 'a open_term = [
  | `Real of QQ.t
  | `Const of int
  | `Var of int * typ_arith
  | `Add of 'a list
  | `Mul of 'a list
  | `Binop of [ `Div | `Mod ] * 'a * 'a
  | `Unop of [ `Floor | `Neg ] * 'a
]

type ('a,'b) open_formula = [
  | `Tru
  | `Fls
  | `And of 'a list
  | `Or of 'a list
  | `Not of 'a
  | `Quantify of [`Exists | `Forall] * string * typ_fo * 'a
  | `Atom of [`Eq | `Leq | `Lt] * 'b * 'b
  | `Proposition of [ `Const of int | `Var of int ]
]

module Make (C : Constant) () = struct
  type 'a expr = sexpr hobj
  type term = typ_arith expr
  type formula = typ_bool expr

  module HT = Hashtbl.Make (C)
  module DynArray = BatDynArray

  let const_left = DynArray.make 512
  let const_right = HT.create 991

  let const_of_symbol sym =
    match DynArray.get const_left sym with
    | `Const k -> Some k
    | _ -> None

  let const_of_symbol_exn sym =
    match DynArray.get const_left sym with
    | `Const k -> k
    | _ -> invalid_arg "const_of_symbol"

  let symbol_of_const k =
    if HT.mem const_right k then
      HT.find const_right k
    else
      let id = DynArray.length const_left in
      HT.add const_right k id;
      DynArray.add const_left (`Const k);
      id

  let mk_skolem ?(name="K") typ =
    DynArray.add const_left (`Skolem (name, typ));
    DynArray.length const_left - 1

  let is_skolem sym =
    match DynArray.get const_left sym with
    | `Skolem (_, _) -> true
    | `Const _ -> false

  let const_typ sym =
    match DynArray.get const_left sym with
    | `Skolem (_, typ) -> typ
    | `Const k -> C.typ k

  let pp_const formatter sym =
    match DynArray.get const_left sym with
    | `Skolem (name, _) -> Format.fprintf formatter "%s:%d" name sym
    | `Const k -> C.pp formatter k

  let hashcons =
    let hc = HC.create 991 in
    HC.hashcons hc

  let mk_real qq = hashcons (Node (Real qq, []))
  let mk_zero = mk_real QQ.zero
  let mk_one = mk_real QQ.one
  let mk_const k =
    match const_typ k with
    | `TyInt | `TyReal -> hashcons (Node (Const k, []))
    | _ -> invalid_arg "mk_const: must be arithmetic type"
  let mk_var v typ = hashcons (Node (Var (v, (typ :> typ_fo)), []))
  let mk_neg t = hashcons (Node (Neg, [t]))
  let mk_div s t = hashcons (Node (Div, [s; t]))
  let mk_mod s t = hashcons (Node (Mod, [s; t]))
  let mk_floor t = hashcons (Node (Floor, [t]))
  let mk_idiv s t = mk_floor (mk_div s t)

  let mk_add = function
    | [] -> mk_zero
    | [x] -> x
    | sum -> hashcons (Node (Add, sum))

  let mk_mul = function
    | [] -> mk_one
    | [x] -> x
    | product -> hashcons (Node (Mul, product))

  let mk_sub s t = mk_add [s; (mk_neg t)]

  let mk_true = hashcons (Node (True, []))
  let mk_false = hashcons (Node (False, []))
  let mk_prop_const k =
    match const_typ k with
    | `TyBool -> hashcons (Node (Const k, []))
    | _ -> invalid_arg "mk_prop_const: not a propositional constant"
  let mk_prop_var i = hashcons (Node (Var (i, `TyBool), []))
  let mk_not phi =
    if phi.tag = mk_false.tag then mk_true
    else if phi.tag = mk_true.tag then mk_false
    else hashcons (Node (Not, [phi]))
  let mk_leq s t = hashcons (Node (Leq, [s; t]))
  let mk_lt s t = hashcons (Node (Lt, [s; t]))
  let mk_eq s t = hashcons (Node (Eq, [s; t]))

  let mk_forall ?name:(name="_") typ phi =
    hashcons (Node (Forall (name, typ), [phi]))

  let mk_exists ?name:(name="_") typ phi =
    hashcons (Node (Exists (name, typ), [phi]))

  let mk_and conjuncts =
    if List.exists (fun x -> x.tag = mk_false.tag) conjuncts then
      mk_false
    else
      match List.filter (fun x -> x.tag != mk_true.tag) conjuncts with
      | [] -> mk_true
      | [x] -> x
      | conjuncts -> hashcons (Node (And, conjuncts))

  let mk_or disjuncts =
    if List.exists (fun x -> x.tag = mk_true.tag) disjuncts then
      mk_true
    else
      match List.filter (fun x -> x.tag != mk_false.tag) disjuncts with
      | [] -> mk_false
      | [x] -> x
      | disjuncts -> hashcons (Node (Or, disjuncts))

  let mk_iff phi psi =
    mk_or [mk_and [phi; psi];
           mk_not (mk_or [phi; psi])]

  module Sexpr = struct
    type t = sexpr hobj

    let equal s t = s.tag = t.tag
    let compare s t = Pervasives.compare s.tag t.tag
    let hash t = t.hcode

    (* Avoid capture by incrementing bound variables *)
    let rec decapture depth incr sexpr =
      let Node (label, children) = sexpr.obj in
      match label with
      | Exists (_, _) | Forall (_, _) ->
        decapture_children label (depth + 1) incr children
      | Var (v, typ) ->
        if v < depth then
          (* v is bound *)
          sexpr
        else
          hashcons (Node (Var (v + incr, typ), []))
      | _ -> decapture_children label depth incr children
    and decapture_children label depth incr children =
      hashcons (Node (label, List.map (decapture depth incr) children))

    let substitute subst sexpr =
      let rec go depth sexpr =
        let Node (label, children) = sexpr.obj in
        match label with
        | Exists (_, _) | Forall (_, _) ->
          go_children label (depth + 1) children
        | Var (v, _) ->
          if v < depth then (* bound var *)
            sexpr
          else
            decapture 0 depth (subst (v - depth))
        | _ -> go_children label depth children
      and go_children label depth children =
        hashcons (Node (label, List.map (go depth) children))
      in
      go 0 sexpr

    let substitute_const subst sexpr =
      let rec go depth sexpr =
        let Node (label, children) = sexpr.obj in
        match label with
        | Exists (_, _) | Forall (_, _) ->
          go_children label (depth + 1) children
        | Const k -> decapture 0 depth (subst k)
        | _ -> go_children label depth children
      and go_children label depth children =
        hashcons (Node (label, List.map (go depth) children))
      in
      go 0 sexpr

    let fold_constants f sexpr acc =
      let rec go acc sexpr =
        let Node (label, children) = sexpr.obj in
        match label with
        | Const k -> f k acc
        | _ -> List.fold_left go acc children
      in
      go acc sexpr

    let vars sexpr =
      let rec go depth sexpr =
        let Node (label, children) = sexpr.obj in
        match label with
        | Exists (_, _) | Forall (_, _) ->
          go_children (depth + 1) children
        | Var (v, typ) ->
          if v < depth then Var.Set.empty
          else Var.Set.singleton (v - depth, typ)
        | _ -> go_children depth children
      and go_children depth children =
        List.fold_left
          Var.Set.union
          Var.Set.empty
          (List.map (go depth) children)
      in
      go 0 sexpr
  end

  module Term = struct
    include Sexpr

    let eval alg t =
      let f label children = match label, children with
        | Real qq, [] -> alg (`Real qq)
        | Const k, [] ->
          begin match const_typ k with
            | `TyInt | `TyReal -> alg (`Const k)
            | `TyBool | `TyFun _ -> invalid_arg "eval: not a term"
          end
        | Var (v, typ), [] ->
          begin match typ with
            | `TyInt -> alg (`Var (v, `TyInt))
            | `TyReal -> alg (`Var (v, `TyReal))
            | `TyBool -> invalid_arg "eval: not a term"
          end
        | Add, sum -> alg (`Add sum)
        | Mul, product -> alg (`Mul product)
        | Div, [s; t] -> alg (`Binop (`Div, s, t))
        | Mod, [s; t] -> alg (`Binop (`Mod, s, t))
        | Floor, [t] -> alg (`Unop (`Floor, t))
        | Neg, [t] -> alg (`Unop (`Neg, t))
        | _ -> invalid_arg "eval: not a term"
      in
      eval_sexpr f t

    let destruct t = match t.obj with
      | Node (Real qq, []) -> `Real qq
      | Node (Const k, []) ->
        begin match const_typ k with
          | `TyInt | `TyReal -> `Const k
          | `TyBool | `TyFun _ -> invalid_arg "destruct: not a term"
        end
      | Node (Var (v, typ), []) ->
        begin match typ with
          | `TyInt -> `Var (v, `TyInt)
          | `TyReal -> `Var (v, `TyReal)
          | `TyBool -> invalid_arg "destruct: not a term"
        end
      | Node (Add, sum) -> `Add sum
      | Node (Mul, product) -> `Mul product
      | Node (Div, [s; t]) -> `Binop (`Div, s, t)
      | Node (Mod, [s; t]) -> `Binop (`Mod, s, t)
      | Node (Floor, [t]) -> `Unop (`Floor, t)
      | Node (Neg, [t]) -> `Unop (`Neg, t)
      | _ -> invalid_arg "destruct: not a term"

    let rec open_pp ?(env=Env.empty) formatter t =
      let open Format in
      match destruct t with
      | `Real qq -> QQ.pp formatter qq
      | `Const k -> pp_const formatter k
      | `Var (v, typ) ->
        (try fprintf formatter "[%s:%d]" (Env.find env v) v
         with Not_found -> fprintf formatter "[free:%d]" v)
      | `Add terms ->
        fprintf formatter "(@[";
        ApakEnum.pp_print_enum
          ~pp_sep:(fun formatter () -> fprintf formatter "@ + ")
          (open_pp ~env)
          formatter
          (BatList.enum terms);
        fprintf formatter "@])"
      | `Mul terms ->
        fprintf formatter "(@[";
        ApakEnum.pp_print_enum
          ~pp_sep:(fun formatter () -> fprintf formatter "@ * ")
          (open_pp ~env)
          formatter
          (BatList.enum terms);
        fprintf formatter "@])"
      | `Binop (`Div, s, t) ->
        fprintf formatter "(@[%a@ / %a@])"
          (open_pp ~env) s
          (open_pp ~env) t
      | `Binop (`Mod, s, t) ->
        fprintf formatter "(@[%a@ mod %a@])"
          (open_pp ~env) s
          (open_pp ~env) t
      | `Unop (`Floor, t) ->
        fprintf formatter "floor(@[%a@])" (open_pp ~env) t
      | `Unop (`Neg, t) ->
        begin match destruct t with
          | `Real qq -> QQ.pp formatter (QQ.negate qq)
          | `Const _ | `Var (_, _) ->
            fprintf formatter "-%a" (open_pp ~env) t
          | _ -> fprintf formatter "-(@[%a@])" (open_pp ~env) t
        end
    let open_show ?(env=Env.empty) t = Apak.Putil.mk_show (open_pp ~env) t
    let pp = open_pp ~env:Env.empty
    let show = open_show ~env:Env.empty
  end
  module Formula = struct
    include Sexpr
    let destruct phi = match phi.obj with
      | Node (True, []) -> `Tru
      | Node (False, []) -> `Fls
      | Node (And, conjuncts) -> `And conjuncts
      | Node (Or, disjuncts) -> `Or disjuncts
      | Node (Not, [phi]) -> `Not phi
      | Node (Exists (name, typ), [phi]) -> `Quantify (`Exists, name, typ, phi)
      | Node (Forall (name, typ), [phi]) -> `Quantify (`Forall, name, typ, phi)
      | Node (Eq, [s; t]) -> `Atom (`Eq, s, t)
      | Node (Leq, [s; t]) -> `Atom (`Leq, s, t)
      | Node (Lt, [s; t]) -> `Atom (`Lt, s, t)
      | Node (Const k, []) ->
        begin match const_typ k with
          | `TyBool -> `Proposition (`Const k)
          | `TyInt | `TyReal | `TyFun _ -> invalid_arg "destruct: not a formula"
          end
      | Node (Var (v, `TyBool), []) -> `Proposition (`Var v)
      | _ -> invalid_arg "destruct: not a formula"

    let rec eval : (('a, term) open_formula -> 'a) -> t -> 'a =
        fun alg phi -> match destruct phi with
      | `Tru -> alg `Tru
      | `Fls -> alg `Fls
      | `Or disjuncts -> alg (`Or (List.map (eval alg) disjuncts))
      | `And conjuncts -> alg (`And (List.map (eval alg) conjuncts))
      | `Quantify (qt, name, typ, phi) ->
        alg (`Quantify (qt, name, typ, eval alg phi))
      | `Not phi -> alg (`Not (eval alg phi))
      | `Atom (op, s, t) -> alg (`Atom (op, s, t))
      | `Proposition p -> alg (`Proposition p)

    let rec flatten_universal phi = match phi.obj with
      | Node (Forall (name, typ), [phi]) ->
        let (varinfo, phi') = flatten_universal phi in
        ((name,typ)::varinfo, phi')
      | _ -> ([], phi)

    let rec flatten_existential phi = match phi.obj with
      | Node (Exists (name, typ), [phi]) ->
        let (varinfo, phi') = flatten_existential phi in
        ((name,typ)::varinfo, phi')
      | _ -> ([], phi)

    let destruct_flat phi = match phi.obj with
      | Node (True, []) -> `Tru
      | Node (False, []) -> `Fls
      | Node (And, conjuncts) ->
        `And (List.concat (List.map (flatten_sexpr And) conjuncts))
      | Node (Or, disjuncts) ->
        `Or (List.concat (List.map (flatten_sexpr Or) disjuncts))
      | Node (Not, [phi]) -> `Not phi
      | Node (Exists (name, typ), [phi]) ->
        let varinfo, phi' = flatten_existential phi in
        `Quantify (`Exists, (name,typ)::varinfo, phi')
      | Node (Forall (name, typ), [phi]) ->
        let varinfo, phi' = flatten_universal phi in
        `Quantify (`Forall, (name, typ)::varinfo, phi')
      | Node (Eq, [s; t]) -> `Atom (`Eq, s, t)
      | Node (Leq, [s; t]) -> `Atom (`Leq, s, t)
      | Node (Lt, [s; t]) -> `Atom (`Lt, s, t)
      | Node (Const k, []) ->
        begin match const_typ k with
          | `TyBool -> `Proposition (`Const k)
          | `TyInt | `TyReal | `TyFun _ -> invalid_arg "destruct: not a formula"
        end
      | Node (Var (v, `TyBool), []) -> `Proposition (`Var v)

      | _ -> invalid_arg "Formula.destruct_flat: not a formula"

    let rec open_pp ?(env=Env.empty) formatter phi =
      let open Format in
      match destruct_flat phi with
      | `Tru -> pp_print_string formatter "true"
      | `Fls -> pp_print_string formatter "false"
      | `Not phi ->
        fprintf formatter "!(@[%a@])" (open_pp ~env) phi
      | `And conjuncts ->
        fprintf formatter "(@[";
        ApakEnum.pp_print_enum
          ~pp_sep:(fun formatter () -> fprintf formatter "@ /\\ ")
          (open_pp ~env)
          formatter
          (BatList.enum conjuncts);
        fprintf formatter "@])"
      | `Or conjuncts ->
        fprintf formatter "(@[";
        ApakEnum.pp_print_enum
          ~pp_sep:(fun formatter () -> fprintf formatter "@ \\/ ")
          (open_pp ~env)
          formatter
          (BatList.enum conjuncts);
        fprintf formatter "@])"
      | `Proposition (`Const k) -> pp_const formatter k
      | `Proposition (`Var v) ->
        (try fprintf formatter "[%s:%d]" (Env.find env v) v
         with Not_found -> fprintf formatter "[free:%d]" v)
      | `Atom (op, x, y) ->
        let op_string = match op with
          | `Eq -> "="
          | `Leq -> "<="
          | `Lt -> "<"
        in
        fprintf formatter "@[%a %s %a@]"
          (Term.open_pp ~env) x
          op_string
          (Term.open_pp ~env) y
      | `Quantify (qt, varinfo, psi) ->
        let quantifier_name =
          match qt with
          | `Exists -> "exists"
          | `Forall -> "forall"
        in
        let env =
          List.fold_left (fun env (x,_) -> Env.push x env) env varinfo
        in
        fprintf formatter "(@[%s@ " quantifier_name;
        ApakEnum.pp_print_enum
          ~pp_sep:pp_print_space
          (fun formatter (name, typ) ->
             fprintf formatter "(%s : %a)" name pp_typ typ)
          formatter
          (BatList.enum varinfo);
        fprintf formatter ".@ %a@])" (open_pp ~env) psi

    let open_show ?(env=Env.empty) t = Apak.Putil.mk_show (open_pp ~env) t

    let pp = open_pp ~env:Env.empty
    let show = open_show ~env:Env.empty

    let existential_closure phi =
      let vars = vars phi in
      let types = Array.make (Var.Set.cardinal vars) `TyInt in
      let rename =
        let n = ref (-1) in
        let map =
          Var.Set.fold (fun (v, typ) m ->
              incr n;
              types.(!n) <- typ;
              Apak.Putil.PInt.Map.add v (mk_var (!n) typ) m
            )
            vars
            Apak.Putil.PInt.Map.empty
        in
        fun v -> Apak.Putil.PInt.Map.find v map
      in
      Array.fold_left
        (fun psi typ -> mk_exists typ psi)
        (substitute rename phi)
        types

    let skolemize_free phi =
      let skolem = Apak.Memo.memo (fun (i, typ) -> mk_const (mk_skolem typ)) in
      let rec go sexpr =
        let (Node (label, children)) = sexpr.obj in
        match label with
        | Var (i, typ) -> skolem (i, (typ :> typ))
        | _ -> hashcons (Node (label, List.map go children))
      in
      go phi

    let prenex phi =
      let negate_prefix =
        List.map (function
            | `Exists (name, typ) -> `Forall (name, typ)
            | `Forall (name, typ) -> `Exists (name, typ))
      in
      let combine phis =
        let f (qf_pre0, phi0) (qf_pre, phis) =
          let depth = List.length qf_pre in
          let depth0 = List.length qf_pre0 in
          let phis = List.map (Sexpr.decapture depth depth0) phis in
          (qf_pre0@qf_pre, (Sexpr.decapture 0 depth phi0)::phis)
        in
        List.fold_right f phis ([], [])
      in

      let alg = function
        | `Tru -> ([], mk_true)
        | `Fls -> ([], mk_false)
        | `Atom (`Eq, x, y) -> ([], mk_eq x y)
        | `Atom (`Lt, x, y) -> ([], mk_lt x y)
        | `Atom (`Leq, x, y) -> ([], mk_leq x y)
        | `And conjuncts ->
          let (qf_pre, conjuncts) = combine conjuncts in
          (qf_pre, mk_and conjuncts)
        | `Or disjuncts ->
          let (qf_pre, disjuncts) = combine disjuncts in
          (qf_pre, mk_or disjuncts)
        | `Quantify (`Exists, name, typ, (qf_pre, phi)) ->
          (`Exists (name, typ)::qf_pre, phi)
        | `Quantify (`Forall, name, typ, (qf_pre, phi)) ->
          (`Forall (name, typ)::qf_pre, phi)
        | `Not (qf_pre, phi) -> (negate_prefix qf_pre, mk_not phi)
        | `Proposition (`Const p) -> ([], mk_prop_const p)
        | `Proposition (`Var i) -> ([], mk_prop_var i)
      in
      let (qf_pre, matrix) = eval alg phi in
      List.fold_right
        (fun qf phi ->
          match qf with
          | `Exists (name, typ) -> mk_exists ~name typ phi
          | `Forall (name, typ) -> mk_forall ~name typ phi)
        qf_pre
        matrix
  end
end

module type BuilderContext = sig
  type term
  type formula

  val mk_add : term list -> term
  val mk_mul : term list -> term
  val mk_div : term -> term -> term
  val mk_mod : term -> term -> term
  val mk_var : int -> typ_arith -> term
  val mk_real : QQ.t -> term
  val mk_const : int -> term
  val mk_floor : term -> term
  val mk_neg : term -> term

  val mk_forall : ?name:string -> typ_fo -> formula -> formula
  val mk_exists : ?name:string -> typ_fo -> formula -> formula
  val mk_and : formula list -> formula
  val mk_or : formula list -> formula
  val mk_true : formula
  val mk_false : formula
  val mk_prop_const : const_sym -> formula
  val mk_prop_var : int -> formula
  val mk_not : formula -> formula
  val mk_eq : term -> term -> formula
  val mk_lt : term -> term -> formula
  val mk_leq : term -> term -> formula
end

module type EvalContext = sig
  type term
  type formula
  module Formula : sig
    type t = formula
    val eval : (('a, term) open_formula -> 'a) -> t -> 'a    
  end
  module Term : sig
    type t = term
    val eval : ('a open_term -> 'a) -> t -> 'a
  end
end

module Infix (C : BuilderContext) =
struct
  let ( ! ) = C.mk_not
  let ( && ) x y = C.mk_and [x; y]
  let ( || ) x y = C.mk_or [x; y]
  let ( < ) = C.mk_lt
  let ( <= ) = C.mk_leq
  let ( = ) = C.mk_eq
  let tru = C.mk_and []
  let fls = C.mk_or []
      
  let ( + ) x y = C.mk_add [x; y]
  let ( - ) x y = C.mk_add [x; C.mk_neg y]
  let ( * ) x y = C.mk_mul [x; y]
  let ( / ) = C.mk_div
  let ( mod ) = C.mk_mod

  let const = C.mk_const
  let forall = C.mk_forall
  let exists = C.mk_exists
  let var = C.mk_var
end
