open Srk
open Syntax

module Ctx = SrkAst.Ctx
module Infix = Syntax.Infix(Ctx)
let srk = Ctx.context

let generator_rep = ref false

let file_contents filename =
  let chan = open_in filename in
  let len = in_channel_length chan in
  let buf = Bytes.create len in
  really_input chan buf 0 len;
  close_in chan;
  buf

let load_math_formula filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try SrkParse.math_main SrkLex.math_token lexbuf with
  | _ ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

let load_smtlib2 filename =
  SrkZ3.load_smtlib2 srk (Bytes.to_string (file_contents filename))

let load_chc fp filename = Chc.ChcSrkZ3.parse_file srk fp filename


let load_formula filename =
  let formula =
    if Filename.check_suffix filename "m" then load_math_formula filename
    else if Filename.check_suffix filename "smt2" then load_smtlib2 filename
    else Log.fatalf "Unrecognized file extension for %s" filename
  in
  Nonlinear.ensure_symbols srk;
  let subst f =
    match typ_symbol srk f with
    | `TyReal | `TyInt | `TyBool | `TyArr -> mk_const srk f
    | `TyFun (args, _) ->
      let f =
        try get_named_symbol srk (show_symbol srk f)
        with Not_found -> f
      in
      mk_app srk f (List.mapi (fun i typ -> mk_var srk i typ) args)
  in
  substitute_sym srk subst formula

let load_math_opt filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try SrkParse.math_opt_main SrkLex.math_token lexbuf with
  | _ ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

let print_result = function
  | `Sat -> Format.printf "sat@\n"
  | `Unsat -> Format.printf "unsat@\n"
  | `Unknown -> Format.printf "unknown@\n"

let of_formula ctx phi =
  let module P = Polyhedron in
  let module V = Linear.QQVector in
  let linearize = Linear.linterm_of ctx in
  let alg = function
    | `Tru -> P.top
    | `Fls -> P.bottom
    | `And xs -> List.fold_left P.meet P.top xs
    | `Atom (`Arith (`Eq, x, y)) ->
      P.of_constraints (BatList.enum [(`Zero, V.sub (linearize y) (linearize x))])
    | `Atom (`Arith (`Leq, x, y)) ->
      P.of_constraints (BatList.enum [(`Nonneg, V.sub (linearize y) (linearize x))])
    | `Atom (`Arith (`Lt, x, y)) ->
      P.of_constraints (BatList.enum [(`Pos, V.sub (linearize y) (linearize x))])
    | `Or _ | `Not _ | `Quantify (_, _, _, _) | `Proposition _
    | `Ite (_, _, _) | `Atom (`ArrEq _)
    | `Atom (`IsInt _) -> invalid_arg "Polyhedron.of_formula"
  in
  Formula.eval ctx alg phi

let int_quantifiers_only (_q, sym) = match typ_symbol srk sym with
  | `TyInt -> true
  | _ -> false

let free_vars_and_existentials keep_quantified (quantifiers, phi) =
  if List.exists (fun (q, _) -> q = `Forall) quantifiers then
    failwith "universal quantification not supported";
  let pp_quantifier_prefix fmt prefix =
    let (prefix, symbol) = prefix in
    match prefix with
    | `Forall -> Format.fprintf fmt "forall @[%a@]" (Syntax.pp_symbol srk) symbol
    | `Exists -> Format.fprintf fmt "exists @[%a@]" (Syntax.pp_symbol srk) symbol
  in
  Format.printf "Quantifiers are: @[%a@]@;"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_quantifier_prefix)
    quantifiers;
  let quantified_vars =
    List.filter keep_quantified quantifiers
    |> List.map (fun (_, sym) -> sym)
    |> Symbol.Set.of_list
  in
  let preserved_symbols =
    Symbol.Set.filter (fun sym -> not (Symbol.Set.mem sym quantified_vars))
      (Syntax.symbols phi) in
  Format.printf "variables to preserve are: @[%a@]@;"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space
       (Syntax.pp_symbol srk)) (Symbol.Set.to_list preserved_symbols);
  (quantified_vars, preserved_symbols)

let formula_of_dd terms dd =
  let term_of_vector terms v =
    Linear.term_of_vec srk (fun dim ->
        if dim = Linear.const_dim then mk_real srk QQ.one
        else terms.(dim))
      v
  in
  let zero = Syntax.mk_real srk QQ.zero in
  let conjuncts =
    BatEnum.fold (fun l (ckind, v) ->
        let t = match ckind with
          | `Nonneg ->
             Syntax.mk_leq srk zero (term_of_vector terms v)
          | `Pos -> Syntax.mk_lt srk zero (term_of_vector terms v)
          | `Zero -> Syntax.mk_eq srk zero (term_of_vector terms v)
        in
        t :: l
      )
      []
      (DD.enum_constraints dd)
  in
  if conjuncts = [] then Syntax.mk_true srk
  else Syntax.mk_and srk conjuncts

let simplify srk phi =
  Syntax.eliminate_ite srk phi
  |> Syntax.eliminate_floor_mod_div srk

let do_qe keep_quantifiers abstract phi =
  Format.printf "Abstracting @[%a@]@;" (Syntax.Formula.pp srk) phi;
  let (quantifiers, phi) = Quantifier.normalize srk phi in
  let (_quantified_vars, preserved_symbols) =
    free_vars_and_existentials keep_quantifiers
      (quantifiers, phi) in
  let simplified_phi = simplify srk phi in
  let terms = BatArray.of_enum
                (BatEnum.map (Syntax.mk_const srk)
                   (Symbol.Set.enum preserved_symbols))
  in
  let lattice_constraints =
    Symbol.Set.fold (fun sym l ->
        match Syntax.typ_symbol srk sym with
        | `TyInt -> Syntax.mk_is_int srk (Syntax.mk_const srk sym) :: l
        | _ -> l
      )
      (symbols simplified_phi) []
  in
  let phi_with_int_constraints =
    Syntax.mk_and srk (simplified_phi :: lattice_constraints) in
  let () = Format.printf "phi with lattice constraints: @[%a@]@;"
             (Syntax.Formula.pp srk) phi_with_int_constraints
  in
  let hull = abstract phi_with_int_constraints terms in
  let () =
    Format.printf "Abstracted @[%a@] (with lattice constraints) to:@\n @[<v 0>%a@]@\n"
      (Syntax.Formula.pp srk) phi_with_int_constraints
      (DD.pp (fun fmt i ->
           if i = Linear.const_dim then
             Format.pp_print_int fmt i
           else
             pp_symbol srk fmt
               (Array.get (Symbol.Set.to_array preserved_symbols) i)))
      hull
  in
  (phi_with_int_constraints, terms, hull)

let run_eliminate (what: [`IntegerQuantifiersOnly | `AllQuantifiers]) abstract file =
  let filter = match what with
    | `IntegerQuantifiersOnly -> int_quantifiers_only
    | `AllQuantifiers -> (fun _ -> true) in
  let phi = load_formula file in
  try
    let (phi_with_int_constraints, terms, hull) =
      do_qe filter abstract phi in
    match Smt.entails srk phi_with_int_constraints (formula_of_dd terms hull) with
    | `Yes -> Format.printf "Result: success"
    | `No -> Format.printf "Result: unsound projection (fail implication check)"
    | `Unknown -> Format.printf "Result: unknown"
  with
  | LatticePolyhedron.PositiveIneqOverRealVar (v, dim) ->
     Format.printf "Result: unknown (cannot convert strict inequality @[%a@], dimension %d is real)@;"
       (Linear.QQVector.pp_term Format.pp_print_int) v dim
  | Linear.Nonlinear ->
     Format.printf "Result: unknown (nonlinear)"

let compare_integer_hull file =
  let (_quantifiers, phi) = Quantifier.normalize srk (load_formula file) in
  let ambient_dim = Syntax.int_of_symbol
                      (Syntax.Symbol.Set.max_elt (Syntax.symbols phi)) + 1 in
  Format.printf "Computing mixed hull@;";

  let binding = FormulaVector.mk_standard_binding srk phi in
  let mixed_hull =
    LatticePolyhedron.abstract_lattice_hull srk binding `Mixed
      ~ambient_dim phi in
  Format.printf "Computing pure hull@;";
  let pure_hull =
    LatticePolyhedron.abstract_lattice_hull srk binding `PureGomoryChvatal
      ~ambient_dim phi in
  Format.printf "Mixed hull: @[%a@]@;" (DD.pp Format.pp_print_int) mixed_hull;
  Format.printf "Pure hull: @[%a@]@;" (DD.pp Format.pp_print_int) pure_hull

let compare_convex_hull file =
  let (qf, phi) = Quantifier.normalize srk (load_formula file) in
  if List.exists (fun (q, _) -> q = `Forall) qf then
    failwith "universal quantification not supported";
  let exists v =
    (* QE on integer-typed variables only *)
    not (List.exists (fun (_, x) -> x = v && typ_symbol srk x == `TyInt) qf)
  in
  let polka = Polka.manager_alloc_strict () in
  let pp_hull formatter hull =
    if !generator_rep then begin
        let env = SrkApron.get_env hull in
        let dim = SrkApron.Env.dimension env in
        Format.printf "Symbols:   [%a]@\n@[<v 0>"
          (SrkUtil.pp_print_enum (Syntax.pp_symbol srk)) (SrkApron.Env.vars env);
        SrkApron.generators hull
        |> List.iter (fun (generator, typ) ->
               Format.printf "%s [@[<hov 1>"
                 (match typ with
                  | `Line    -> "line:     "
                  | `Vertex  -> "vertex:   "
                  | `Ray     -> "ray:      "
                  | `LineMod -> "line mod: "
                  | `RayMod  -> "ray mod:  ");
               for i = 0 to dim - 2 do
                 Format.printf "%a@;" QQ.pp (Linear.QQVector.coeff i generator)
               done;
               Format.printf "%a]@]@;" QQ.pp (Linear.QQVector.coeff (dim - 1) generator));
        Format.printf "@]"
      end else
      SrkApron.pp formatter hull
  in
  let hull_abstract = Abstract.abstract ~exists srk polka phi in
  Format.printf "Convex hull computed using abstract:@\n @[<v 0>%a@]@\n@."
    pp_hull hull_abstract;
  Format.printf "Now computing using local projection@\n";
  let quantified_int =
    BatList.filter_map (fun (_, sym) ->
        match typ_symbol srk sym with
        | `TyInt -> Some sym
        | _ -> None) qf
    |> Symbol.Set.of_list
  in
  let symbol_list = Symbol.Set.elements (symbols phi) in
  let preserved_symbols =
    List.filter (fun sym -> not (Symbol.Set.mem sym quantified_int))
      symbol_list in
  let hull_local = SymbolicAbstraction.integer_hull_by_recession_cone srk phi preserved_symbols in
  Format.printf "Convex hull computed using local projection:@\n @[<v 0>%a@]@\n"
    (DD.pp (fun fmt i ->
         if i = Linear.const_dim then
           Format.pp_print_int fmt i
         else pp_symbol srk fmt (symbol_of_int i))) hull_local;
  let hull_abstract = of_formula srk (SrkApron.formula_of_property hull_abstract) in
  if (Polyhedron.equal (Polyhedron.of_dd hull_local) hull_abstract)
  then Format.printf "equal@\n"
  else Format.printf "unequal@\n";
  ()

let compare_projection
      (algs: [`RealConvHull | `Lira | `HullRealProjectDoubleElim | `HullRealProjectSingleElim] list)
      (what: [`IntegerQuantifiersOnly | `AllQuantifiers])
      file =
  let phi = load_formula file in
  let keep_quantifiers = match what with
    | `IntegerQuantifiersOnly -> int_quantifiers_only
    | `AllQuantifiers -> (fun _ -> true)
  in
  let do_qe = do_qe keep_quantifiers in
  let attempt f =
    try f ()
    with
    | LatticePolyhedron.PositiveIneqOverRealVar (v, dim) ->
       Format.printf "Result: unknown (cannot convert strict inequality @[%a@], dimension %d is real)@;"
         (Linear.QQVector.pp_term Format.pp_print_int) v dim;
       assert false
    | Linear.Nonlinear ->
       Format.printf "Result: unknown (nonlinear)";
       assert false
  in
  let compute phi = function
    | `RealConvHull ->
       (`RealConvHull, attempt (fun () -> do_qe (ConvexHull.conv_hull srk) phi))
    | `Lira -> (`Lira, do_qe (Lira.project srk) phi)
    | `HullRealProjectDoubleElim ->
       ( `HullRealProjectDoubleElim
       , attempt
           (fun () ->
             do_qe
               (LatticePolyhedron.abstract_by_local_hull_and_project_real
                  srk `TwoPhaseElim) phi
           )
       )
    | `HullRealProjectSingleElim ->
       ( `HullRealProjectSingleElim
       , attempt
           (fun () ->
             do_qe (LatticePolyhedron.abstract_by_local_hull_and_project_real
                      srk `OnePhaseElim) phi
           )
       )
  in
  let string_of = function
    | `RealConvHull -> "real hull"
    | `Lira -> "lira hull"
    | `HullRealProjectDoubleElim -> "hull&project-double-elim hull"
    | `HullRealProjectSingleElim -> "hull&project-single-elim hull"
  in
  let expect meth1 meth2 result =
    match (meth1, meth2, result) with
    | (`Lira, `HullRealProjectDoubleElim, `Equal)
      | (`Lira, `HullRealProjectSingleElim, `Equal)
      | (`Lira, `RealConvHull, `Equal)
      | (`Lira, `RealConvHull, `Smaller)
      | (`HullRealProjectDoubleElim, `Lira, `Equal)
      | (`HullRealProjectDoubleElim, `HullRealProjectSingleElim, `Equal)
      | (`HullRealProjectDoubleElim, `RealConvHull, `Equal)
      | (`HullRealProjectDoubleElim, `RealConvHull, `Smaller)
      | (`HullRealProjectSingleElim, `Lira, `Equal)
      | (`HullRealProjectSingleElim, `HullRealProjectDoubleElim, `Equal)
      | (`HullRealProjectSingleElim, `RealConvHull, `Equal)
      | (`HullRealProjectSingleElim, `RealConvHull, `Smaller) -> true
    | _ -> false
  in
  let hulls = List.map (compute phi) algs in
  let (_, (_, terms, _)) = List.hd hulls in
  let rec test_all_pairs test l =
    match l with
    | [] -> []
    | x :: ys ->
       List.fold_left
         (fun l y -> test x y :: l)
         (test_all_pairs test ys) ys
  in    
  let test (meth1, (_, _, hull1)) (meth2, (_, _, hull2)) =
    let hull1_phi, hull2_phi =
      formula_of_dd terms hull1, formula_of_dd terms hull2 in
    match Smt.entails srk hull1_phi hull2_phi
        , Smt.entails srk hull2_phi hull1_phi with
    | `Yes, `Yes -> (meth1, meth2, `Equal, expect meth1 meth2 `Equal)
    | `Yes, `No -> (meth1, meth2, `Smaller, expect meth1 meth2 `Smaller)
    | `No, `Yes -> (meth2, meth1, `Smaller, expect meth2 meth1 `Smaller)
    | `No, `No -> (meth1, meth2, `Incomparable, false)
    | `Unknown, _ -> (meth1, meth2, `Incomparable, false)
    | _, `Unknown -> (meth1, meth2, `Incomparable, false)
  in
  let comparisons = test_all_pairs test hulls in
  let unexpected = List.filter (fun (_, _, _, b) -> not b) comparisons in
  match unexpected with
  | _ :: _ ->
     List.iter (fun (meth1, meth2, result, _) ->
         Format.printf "Result: unsound projection (%s is %a %s)@;"
           (string_of meth1)
           (fun fmt comparison ->
             match comparison with
             | `Equal -> Format.fprintf fmt "equal to"
             | `Smaller -> Format.fprintf fmt "smaller than"
             | `Incomparable -> Format.fprintf fmt "incomparable with")
           result
           (string_of meth2)
       ) unexpected
  | [] ->
     let unequal_hulls =
       List.filter (fun (_, _, comparison, _) -> comparison <> `Equal) comparisons in
     match unequal_hulls with
     | _ :: _ ->
        List.iter (fun (meth1, meth2, result, _) ->
            Format.printf "Result: Smaller than (%s is %a %s)@;"
              (string_of meth1)
              (fun fmt comparison ->
                match comparison with
                | `Equal -> assert false
                | `Smaller -> Format.fprintf fmt "smaller than"
                | `Incomparable -> Format.fprintf fmt "incomparable with")
              result
              (string_of meth2)
          ) unequal_hulls
     | [] -> Format.printf "Result: all hulls equal@;"

let spec_list = [
  ("-simsat",
   Arg.String (fun file ->
       let phi = load_formula file in
       print_result (Quantifier.simsat srk phi)),
   " Test satisfiability of an LRA or LIA formula (IJCAI'16)");

  ("-nlsat",
   Arg.String (fun file ->
       let phi = load_formula file in
       print_result (Wedge.is_sat srk (snd (Quantifier.normalize srk phi)))),
   " Test satisfiability of a non-linear ground formula (POPL'18)");

  ("-lirrsat",
   Arg.String (fun file ->
       let phi = load_formula file in
       print_result (Lirr.is_sat srk (snd (Quantifier.normalize srk phi)))),
   " Test satisfiability of a non-linear ground formula using theory of linear integer real rings");

  ("-normaliz",
   Arg.Unit (fun () -> PolynomialConeCpClosure.set_cutting_plane_method `Normaliz),
   "Set weak theory solver to use Normaliz's integer hull computation (instead of Gomory-Chvatal");

  ("-generator",
   Arg.Set generator_rep,
   " Print generator representation of convex hull");

  (*
  ("-compare-integer-hull",
   Arg.String compare_integer_hull,
   "Compare integer hulls computed by Gomory-Chvatal, Normaliz, and recession cone generalization");

  ("-compare-convex-hull",
   Arg.String compare_convex_hull,
   "Compare convex hulls computed by local projection and abstract");

  ("-compare-lira-real-convhull",
   Arg.String
     (compare_projection [`Lira; `RealConvHull] `AllQuantifiers)
   , "Compare projected hulls computed by LIRA and real convex hull");

  ("-compare-lira-hull-and-project-double-elim",
   Arg.String
     (compare_projection [`Lira; `HullRealProjectDoubleElim] `AllQuantifiers)
   , "Compare projected hulls computed by LIRA and hull&project");

  ("-local-hull-and-project"
  , Arg.String
      (fun s ->
        ignore
          (run_eliminate `AllQuantifiers
             (LatticePolyhedron.abstract_by_local_hull_and_project_real srk `TwoPhaseElim) s))
  , " May diverge when formula contains real-valued variables (why?)"
  );

  ("-lira-project"
  , Arg.String (fun s -> ignore (run_eliminate `AllQuantifiers (Lira.project srk) s))
  , " Compute the lattice hull of an existential formula by model-based projection of recession cones"
  );

  ("-project-by-real-conv-hull"
  , Arg.String (fun s -> ignore (run_eliminate `AllQuantifiers (ConvexHull.conv_hull srk) s))
  , " Compute the convex hull of an existential linear arithmetic formula (silently ignoring real-typed quantifiers)");
   *)

  ("-lira-convex-hull-sc",
   Arg.String (fun file ->
       let (qf, phi) = Quantifier.normalize srk (load_formula file) in
       if List.exists (fun (q, _) -> q = `Forall) qf then
         failwith "universal quantification not supported";
       let module S = Syntax.Symbol.Set in
       let module PLT = PolyhedronLatticeTiling in
       let terms = S.filter
                     (fun sym -> not (List.exists (fun (_, quant) -> quant = sym) qf))
                     (Syntax.symbols phi)
                   |> (fun set -> S.fold (fun sym terms -> Ctx.mk_const sym :: terms) set [])
                   |> Array.of_list
       in
       let integer_constraints =
         S.fold
           (fun sym l ->
             match Syntax.typ_symbol srk sym with
             | `TyInt -> Syntax.mk_is_int srk (Syntax.mk_const srk sym) :: l
             | _ -> l
           )
           (Syntax.symbols phi)
           []
       in
       Format.printf "Symbols to eliminate: @[%a@]@;"
         (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
            (fun fmt sym ->
              Format.fprintf fmt "%a: %a"
                (Syntax.pp_symbol srk) sym pp_typ (typ_symbol srk sym)))
         (List.map snd qf);
       let _hull =
         PLT.convex_hull
           srk (Syntax.mk_and srk (phi :: integer_constraints))
           terms in
       (*
       Format.printf "Symbols to eliminate: @[%a@]@;"
         (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
            (fun fmt sym ->
              Format.fprintf fmt "%a: %a"
                (Syntax.pp_symbol srk) sym pp_typ (typ_symbol srk sym)))
         (List.map snd qf);
       Format.printf "Convex hull:@\n @[<v 0>%a@]@\n"
         (Syntax.Formula.pp srk)
         (PLT.formula_of_dd srk (fun dim -> terms.(dim)) hull);
        *)
       Format.printf "Result: success"
     ),
   "Compute the convex hull of an existential formula in integer-real linear arithmetic"
  );

  ("-convex-hull",
   Arg.String (fun file ->
       let (qf, phi) = Quantifier.normalize srk (load_formula file) in
       if List.exists (fun (q, _) -> q = `Forall) qf then
         failwith "universal quantification not supported";
       let exists v =
         not (List.exists (fun (_, x) -> x = v) qf)
       in
       let polka = Polka.manager_alloc_strict () in
       let pp_hull formatter hull =
         if !generator_rep then begin
           let env = SrkApron.get_env hull in
           let dim = SrkApron.Env.dimension env in
           Format.printf "Symbols:   [%a]@\n@[<v 0>"
             (SrkUtil.pp_print_enum (Syntax.pp_symbol srk)) (SrkApron.Env.vars env);
           SrkApron.generators hull
           |> List.iter (fun (generator, typ) ->
               Format.printf "%s [@[<hov 1>"
                 (match typ with
                  | `Line    -> "line:     "
                  | `Vertex  -> "vertex:   "
                  | `Ray     -> "ray:      "
                  | `LineMod -> "line mod: "
                  | `RayMod  -> "ray mod:  ");
               for i = 0 to dim - 2 do
                 Format.printf "%a@;" QQ.pp (Linear.QQVector.coeff i generator)
               done;
               Format.printf "%a]@]@;" QQ.pp (Linear.QQVector.coeff (dim - 1) generator));
           Format.printf "@]"
         end else
           SrkApron.pp formatter hull
       in
       Format.printf "Convex hull:@\n @[<v 0>%a@]@\n"
         pp_hull (Abstract.abstract ~exists srk polka phi)),
   " Compute the convex hull of an existential linear arithmetic formula");

  ("-wedge-hull",
   Arg.String (fun file ->
       let (qf, phi) = Quantifier.normalize srk (load_formula file) in
       if List.exists (fun (q, _) -> q = `Forall) qf then
         failwith "universal quantification not supported";
       let exists v =
         not (List.exists (fun (_, x) -> x = v) qf)
       in
       let wedge = Wedge.abstract ~exists srk phi in
       Format.printf "Wedge hull:@\n @[<v 0>%a@]@\n" Wedge.pp wedge),
   " Compute the wedge hull of an existential non-linear arithmetic formula");

  ("-affine-hull",
   Arg.String (fun file ->
       let phi = load_formula file in
       let qf = fst (Quantifier.normalize srk phi) in
       if List.exists (fun (q, _) -> q = `Forall) qf then
         failwith "universal quantification not supported";
       let symbols = (* omits skolem constants *)
         Symbol.Set.elements (symbols phi)
       in
       let aff_hull = Abstract.affine_hull srk phi symbols in
       Format.printf "Affine hull:@\n %a@\n"
         (SrkUtil.pp_print_enum (ArithTerm.pp srk)) (BatList.enum aff_hull)),
   " Compute the affine hull of an existential linear arithmetic formula");

  ("-qe",
   Arg.String (fun file ->
       let open Syntax in
       let phi = load_formula file in
       let result =
         Quantifier.qe_mbp srk phi
         |> SrkSimplify.simplify_dda srk
       in
       Format.printf "%a@\n" (pp_smtlib2 srk) result),
   " Eliminate quantifiers");

  ("-stats",
   Arg.String (fun file ->
       let open Syntax in
       let phi = load_formula file in
       let phi = Formula.prenex srk phi in
       let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
       let rec go phi =
         match Formula.destruct srk phi with
         | `Quantify (`Exists, _, _, psi) -> "E" ^ (go psi)
         | `Quantify (`Forall, _, _, psi) -> "A" ^ (go psi)
         | _ -> ""
       in
       let qf_pre =
         (String.concat ""
            (List.map (fun _ -> "E") (Symbol.Set.elements constants)))
         ^ (go phi)
       in
       Format.printf "Quantifier prefix: %s" qf_pre;
       Format.printf "Variables: %d" (String.length qf_pre);
       Format.printf "Matrix size: %d" (size phi)),
   " Print formula statistics");

  ("-random",
   Arg.Tuple [
     Arg.String (fun arg ->
         let qf_pre = ref [] in
         String.iter (function
             | 'E' -> qf_pre := `Exists::(!qf_pre)
             | 'A' -> qf_pre := `Forall::(!qf_pre)
             | _ -> assert false)
           arg;
         RandomFormula.quantifier_prefix := List.rev (!qf_pre));
     Arg.Set_int RandomFormula.formula_uq_depth;
     Arg.String (fun arg ->
         begin match arg with
         | "dense" -> RandomFormula.dense := true
         | "sparse" -> RandomFormula.dense := false
         | x -> Log.fatalf "unknown argument: %s" x;
         end;
         Random.self_init ();
         let z3 = Z3.mk_context [] in
         Z3.SMT.benchmark_to_smtstring
           z3
           "random"
           ""
           "unknown"
           ""
           []
           (SrkZ3.z3_of_formula srk z3 (RandomFormula.mk_random_formula srk))
         |> print_endline)
   ],
   " Generate a random formula");

  ("-chc",
   Arg.String (fun file ->
       let open Iteration in
       let fp = Chc.Fp.create () in
       let fp = load_chc fp file in
       let pd =
         (module Product(LossyTranslation)(PolyhedronGuard) : PreDomain)
       in (*TODO: let user pick iter operation*)
       let rels = Chc.Fp.get_relations_used fp in
       let sln = Chc.Fp.solve srk fp pd in
       Format.printf "(Solution is:\n@[";
       SrkUtil.pp_print_enum
         ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ \n ")
         (fun formatter rel ->
            let syms, phi = sln rel in
            let syms = BatArray.to_list syms in
            Format.fprintf formatter "@%a : %a@"
            (Chc.pp_rel_atom srk fp)
            (Chc.mk_rel_atom srk fp rel syms)
            (Formula.pp srk)
            phi)
         Format.std_formatter
         (Chc.Relation.Set.enum rels)),
   " Output solution to system of constrained horn clauses");

  ("-verbosity",
   Arg.String (fun v -> Log.verbosity_level := (Log.level_of_string v)),
   " Set verbosity level (higher = more verbose; defaults to 0)");

  ("-verbose",
   Arg.String (fun v -> Log.set_verbosity_level v `info),
   " Raise verbosity for a particular module");

  ("-verbose-list",
   Arg.Unit (fun () ->
       print_endline "Available modules for setting verbosity:";
       Hashtbl.iter (fun k _ ->
           print_endline (" - " ^ k);
         ) Log.loggers;
       exit 0;
     ),
   " List modules which can be used with -verbose")
]

let usage_msg = "bigtop: command line interface to srk \n\
  Usage:\n\
  \tbigtop [options] [-simsat|-nlsat] formula.smt2\n\
  \tbigtop [-generator] -convex-hull formula.smt2\n\
  \tbigtop -affine-hull formula.smt2\n\
  \tbigtop -wedge-hull formula.smt2\n\
  \tbigtop -qe formula.smt2\n\
  \tbigtop -stats formula.smt2\n\
  \tbigtop -random (A|E)* depth [dense|sparse]\n\
  \tbigtop -reachable-goal chc.smt2\n"

let anon_fun s = failwith ("Unknown option: " ^ s)

let () =
  if Array.length Sys.argv == 1 then
    Arg.usage (Arg.align spec_list) usage_msg
  else
    Arg.parse (Arg.align spec_list) anon_fun usage_msg
