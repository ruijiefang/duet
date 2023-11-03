open BatEnum.Infix
module P = Polyhedron
module L = IntLattice
module V = Linear.QQVector

module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "symbolicAbstraction" end)

let () = my_verbosity_level := `debug

module Util = struct

  let is_int context dim =
    if dim = Linear.const_dim then true
    else (Syntax.typ_symbol context (Syntax.symbol_of_int dim) = `TyInt)

  let dims_of_symbols symbols =
    List.fold_left (fun s sym -> IntSet.add (Syntax.int_of_symbol sym) s)
      IntSet.empty symbols

  let max_dim_in_symbols symbols =
    List.fold_left (fun n sym -> Int.max n (Syntax.int_of_symbol sym))
      (-1) symbols + 1

  let non_constant_dimensions vector =
    BatEnum.fold
      (fun s (_, dim) ->
        if dim <> Linear.const_dim then
          IntSet.add dim s
        else s)
      IntSet.empty
      (V.enum vector)

  let map_of m =
    BatEnum.fold
      (fun f (s, typ) ->
        match typ with
        | `Real q ->
           let k = Syntax.int_of_symbol s in
           (fun dim -> if dim = k then q else f dim)
        | _ -> f)
      (fun _ -> QQ.zero)
      (Interpretation.enum m)

  let formula_of_constraint context (ckind, cnstrnt) =
    let zero = Syntax.mk_zero context in
    let term = Linear.of_linterm context cnstrnt in
    let mk_compare cmp term = Syntax.mk_compare cmp context zero term in
    match ckind with
    | `Zero -> mk_compare `Eq term
    | `Nonneg -> mk_compare `Leq term
    | `Pos -> mk_compare `Lt term

  let linearize context t =
    try
      Linear.linterm_of context t
    with Linear.Nonlinear ->
      let s = Format.asprintf "Term %a is not linear" (Syntax.ArithTerm.pp context) t in
      failwith s

  let constraint_of_atom context = function
    | `ArithComparison (`Lt, t1, t2) ->
       (* `Ineq (`Pos, V.sub (linearize context t2) (linearize context t1)) *)
       (* Silently convert to non-strict inequality *)
       logf "Warning: Silently converting > to >= 0@.";
       `Ineq (`Nonneg, V.sub (linearize context t2) (linearize context t1))
    | `ArithComparison (`Leq, t1, t2) ->
       `Ineq (`Nonneg, V.sub (linearize context t2) (linearize context t1))
    | `ArithComparison (`Eq, t1, t2) ->
       `Ineq (`Zero, V.sub (linearize context t2) (linearize context t1))
    | `IsInt s ->
       `InLat (linearize context s)
    | `Literal _
      | `ArrEq _ -> failwith "Cannot handle atoms"

  let collect_non_constant_dimensions vector_of s cnstrnt =
    IntSet.union s (non_constant_dimensions (vector_of cnstrnt))

  let constraints_of_implicant context = function
    | None -> failwith "No implicant found"
    | Some atoms ->
       List.fold_left
         (fun (inequalities, lattice_constraints) atom ->
           match constraint_of_atom context
                   (Interpretation.destruct_atom context atom) with
           | `Ineq cnstrnt -> (cnstrnt :: inequalities, lattice_constraints)
           | `InLat v -> (inequalities, v :: lattice_constraints)
         )
         ([], [])
         atoms

  let pp_pconstraint fmt (kind, v) =
    Format.fprintf fmt "%a %s"
      V.pp v
      (match kind with | `Zero -> " = 0"
                       | `Nonneg -> " >= 0"
                       | `Pos -> " > 0")

  let _pp_generator fmt (kind, v) =
    match kind with
    | `Vertex -> Format.fprintf fmt "vertex (%a)" V.pp v
    | `Ray -> Format.fprintf fmt "ray (%a)" V.pp v
    | `Line -> Format.fprintf fmt "line (%a)" V.pp v

  let pp_dim = fun fmt d -> Format.fprintf fmt "%d" d

end

module LatticePolyhedron : sig

  val lattice_polyhedron_of : P.t -> IntLattice.t -> P.t

end = struct

  module T = Linear.MakeLinearMap(QQ)(Int)(V)(V)

  let pp_linear_map fmt linear_map =
    BatEnum.iter (fun (s, t) ->
        Format.fprintf fmt "(%a, %a); " Linear.QQVector.pp s Linear.QQVector.pp t)
      (T.enum linear_map)

  let force_transform (forward, inverse, num_dimensions) p =
    let q = BatEnum.empty () in
    let (forward, inverse, num_dimensions) =
      BatEnum.fold
        (fun (forward, inverse, num_dimensions) (kind, v) ->
          match T.apply forward v with
          | None ->
             let image = V.of_term QQ.one num_dimensions in
             BatEnum.push q (kind, image);
             let new_forward =
               match T.add v image forward with
               | Some forward' -> forward'
               | None ->
                  logf "force_transform forward: %a is already in the domain of %a@."
                    Linear.QQVector.pp v pp_linear_map forward;
                 failwith "force_transform: forward extension conflict"
             in
             let new_backward =
               match T.add image v inverse with
               | Some backward' -> backward'
               | None ->
                  logf "force_transform inverse: %a is already in the domain of %a@."
                    Linear.QQVector.pp image pp_linear_map inverse;
                  failwith "force_transform: inverse extension conflict"
             in
             ( new_forward, new_backward, num_dimensions + 1)
          | Some image ->
             BatEnum.push q (kind, image);
             (forward, inverse, num_dimensions)
        )
        (forward, inverse, num_dimensions)
        (P.enum_constraints p)
    in
    (forward, inverse, num_dimensions, P.of_constraints q)

  let transform map p =
    let q = BatEnum.empty () in
    BatEnum.iter (fun (kind, v) ->
        match T.apply map v with
        | None -> failwith "transformation is malformed"
        | Some image ->
           BatEnum.push q (kind, image)
      )
      (P.enum_constraints p);
    P.of_constraints q

  let lattice_polyhedron_of p l =
    let basis = IntLattice.basis l in
    let (forward_l, inverse_l, num_dimensions_l) =
      List.fold_left (fun (forward, inverse, index) v ->
          let f = T.add_exn v (V.of_term QQ.one index) forward in
          let b = T.add_exn (V.of_term QQ.one index) v inverse in
          (f, b, index + 1))
        (T.empty, T.empty, 0)
        basis
    in
    logf "Forcing transform";
    let (_forward, inverse, _num_dimensions, q) =
      force_transform (forward_l, inverse_l, num_dimensions_l) p
    in
    logf "Forced transform";
    let hull = Polyhedron.integer_hull `GomoryChvatal q in
    transform inverse hull

end

module IntegerMbp : sig
  (** All variables (dimensions) must be integer variables, i.e.,
      the formula should entail that the variable is an integer,
      whether enforced by its syntactic type or because of an
      integer constraint. Otherwise we may diverge:
      for recession cone, we have to make enough progress towards
      boundaries, and for Cooper's, the number of residue classes
      has to be finite.
      Both are guaranteed when all variables are integer-valued.
   *)

  val local_project_recession :
    (int -> QQ.t) -> eliminate:IntSet.t -> Polyhedron.t -> Polyhedron.t

  (** All variables (dimensions) to be eliminated must be integer-valued.
      TODO: Remove the [is_int] and just require that these variables
      are in the lattice.
   *)
  val local_project_cooper :
    (int -> bool) -> (int -> QQ.t) -> eliminate:IntSet.t ->
    Polyhedron.t * IntLattice.t -> Polyhedron.t * IntLattice.t

end = struct

  let evaluate_linear a m =
    let (_, v) = V.pivot Linear.const_dim a in
    Linear.evaluate_affine m v

  let normalize a dim =
    let c = V.coeff dim a in
    if QQ.equal c QQ.zero then a
    else V.scalar_mul (QQ.inverse (QQ.abs c)) a

  let get_bound dim v =
    let drop_dim v = V.pivot dim v |> snd in
    if QQ.lt (V.coeff dim v) Q.zero then
      normalize v dim |> drop_dim
    else if QQ.lt Q.zero (V.coeff dim v) then
      normalize v dim |> drop_dim |> V.negate
    else
      failwith "Vector is 0 in the dimension"

  let evaluate_bound dim v m =
    Linear.evaluate_affine m (get_bound dim v)

  let substitute_term t dim v =
    let (c, v') = V.pivot dim v in
    V.add v' (V.scalar_mul c t)

  (* A classified system of constraints with respect to a chosen dimension x and
   a model m contains:
   - The row a^T Y - cx + b >= 0 (or = 0) that gives the lub, if one exists,
     where c is positive
   - The row a^T Y + cx + b >= 0 (or = 0) that gives the lub, if one exists,
     where c is positive
   - The other constraints that involve x
   - The independent constraints that don't involve x
   *)
  type classified =
    {
      lub_row : (QQ.t * P.constraint_kind * V.t) option
    ; glb_row : (QQ.t * P.constraint_kind * V.t) option
    ; others : (P.constraint_kind * V.t) BatEnum.t
    ; independent : (P.constraint_kind * V.t) BatEnum.t
    }

  let pp_bounding_row fmt = function
    | Some (q, kind, v) ->
       Format.fprintf fmt "(%a, %a %s)"
         QQ.pp q V.pp v
         (match kind with | `Zero -> " = 0"
                          | `Nonneg -> " >= 0"
                          | `Pos -> " > 0")
    | None -> Format.fprintf fmt ""

  let pp_classified fmt classified =
    let others = BatEnum.clone classified.others in
    let independent = BatEnum.clone classified.independent in
    Format.fprintf fmt
      "@[<v 0>{ lub_row : %a ;@. glb_row : %a ;@. others : %a ;@. independent : %a }@]"
      pp_bounding_row classified.lub_row
      pp_bounding_row classified.glb_row
      (Format.pp_print_list ~pp_sep:Format.pp_print_cut Util.pp_pconstraint)
      (BatList.of_enum others)
      (Format.pp_print_list ~pp_sep:Format.pp_print_cut Util.pp_pconstraint)
      (BatList.of_enum independent)

  let lub_row classified = classified.lub_row
  let glb_row classified = classified.glb_row
  let update_lub value classified = { classified with lub_row = Some value }
  let update_glb value classified = { classified with glb_row = Some value }

  let update_row_if getter updater pred value kind row classified =
    match getter classified with
    | Some (value_bound, kind_bound, row_bound) ->
       if pred value value_bound then
         begin
           BatEnum.push classified.others (kind_bound, row_bound);
           updater (value, kind, row) classified
         end
       else
         begin
           BatEnum.push classified.others (kind, row);
           classified
         end
    | None ->
       updater (value, kind, row) classified

  let update_lub_if = update_row_if lub_row update_lub
  let update_glb_if = update_row_if glb_row update_glb

  let classify_constraints m dim constraints =
    BatEnum.fold (fun classified (kind, v) ->
        if QQ.equal (V.coeff dim v) QQ.zero then
          begin
            BatEnum.push classified.independent (kind, v);
            classified
          end
        else
          let value = evaluate_bound dim v m in
          match kind with
          | `Pos ->
             let tt = fun _ _ -> true in
             update_lub_if tt value kind v classified
             |> update_glb_if tt value `Zero v
          | `Zero ->
             let tt = fun _ _ -> true in
             update_lub_if tt value kind v classified
             |> update_glb_if tt value kind v
          | `Nonneg ->
             if QQ.lt (V.coeff dim v) QQ.zero then
               update_lub_if QQ.lt value kind v classified
             else if QQ.lt QQ.zero (V.coeff dim v) then
               update_glb_if (fun v1 v2 -> QQ.lt v2 v1) value kind v classified
             else failwith "Impossible"
      )
      {
        lub_row = None
      ; glb_row = None
      ; others = BatEnum.empty ()
      ; independent = BatEnum.empty ()
      }
      constraints

  let recession_cone_at m p =
    P.enum_constraints p
    /@ (fun (kind, a) ->
      match kind with
      | `Zero -> (kind, a)
      | `Pos
        | `Nonneg ->
         let (_, normal) = V.pivot Linear.const_dim a in
         let recession = V.add_term (QQ.negate (evaluate_linear normal m))
                           Linear.const_dim normal
         in (`Nonneg, recession))
    |> P.of_constraints

  let get_solution dim classified =
    match classified.lub_row, classified.glb_row with
    | None, _
      | _, None ->
       `Infinite
    | Some (_, _, _), Some (_, _, glb_row) ->
       let glb_term = get_bound dim glb_row in
       `Finite glb_term

  let local_project_recession m ~eliminate:dims p =
    logf "local_projection_recession: dims to eliminate: %a@."
      IntSet.pp dims;
    IntSet.fold
      (fun dim p ->
        let cone = recession_cone_at m p in
        logf "recession cone is: %a@." (P.pp Util.pp_dim) cone;
        let classified = classify_constraints m dim (P.enum_constraints cone) in
        logf "local_project_recession: classified: @.@[%a@]@."
          pp_classified
          classified;
        match get_solution dim classified with
        | `Infinite -> P.of_constraints classified.independent
        | `Finite glb_term ->
           logf "substituting solution: %a@." V.pp glb_term;
           let solution = glb_term in
           let () = match classified.lub_row with
             | None -> ()
             | Some (_, kind, row) -> BatEnum.push classified.others (kind, row)
           in
           let constraints =
             classified.others
             /@ (fun (kind, a) ->
               (kind, substitute_term solution dim a))
             |> BatEnum.append classified.independent
           in
           let l = BatList.of_enum constraints in
           logf "new constraints: %a@."
             (Format.pp_print_list ~pp_sep:Format.pp_print_space
                Util.pp_pconstraint)
             l;
           P.of_constraints (BatList.enum l))
      dims p

  let local_project_cooper is_int m ~eliminate:dims (p, l) =
    IntSet.fold (fun dim (p, l) ->
        let classified = classify_constraints m dim
                           (P.enum_constraints p) in
        match get_solution dim classified with
        | `Infinite ->
           ( P.of_constraints classified.independent
           , IntLattice.project (fun dim -> not (IntSet.mem dim dims)) l )
        | `Finite glb_term ->
           logf "obtained lower bound: %a@." V.pp glb_term;
           if BatEnum.exists (fun (_, dim) -> not (is_int dim))
                (Linear.QQVector.enum glb_term)
           then failwith "May diverge; lower bound term contains rational variable"
           else ();
           (* Integrality constraint from lattice can be stronger
              than just [Int(dim)].
            *)
           let divisor =
             BatList.fold_left
               (fun m v ->
                 let coeff = Linear.QQVector.coeff dim v in
                 if QQ.equal coeff QQ.zero then m
                 else ZZ.lcm m (QQ.denominator coeff))
               ZZ.one
               (L.basis l)
           in
           let difference = QQ.sub (m dim) (Linear.evaluate_affine m glb_term) in
           let residue = QQ.modulo difference (QQ.of_zz divisor) in
           let solution = V.add_term residue Linear.const_dim glb_term in
           logf "substituting solution: %a@." V.pp solution;
           let () = match classified.lub_row with
             | None -> ()
             | Some (_, kind, row) -> BatEnum.push classified.others (kind, row)
           in
           (* TODO: Do we need to substitute? *)
           let new_p =
             classified.others
             /@ (fun (kind, a) ->
               (kind, substitute_term solution dim a))
             |> BatEnum.append classified.independent
             |> P.of_constraints in
           let new_l =
             List.map (substitute_term solution dim) (IntLattice.basis l)
             |> List.cons solution
             (* [F[soln/x] /\ Int(soln) |= exists x. Int(x) /\ F[x]].
                while
                [F[soln/x] |/= exists x. Int(x) /\ F[x]]; we lose the integrality
                constraint.
              *)
             |> IntLattice.hermitize
           in
           (new_p, new_l)
      ) dims (p, l)

end

(** Abstract domain that supports symbolic abstraction *)
module type AbstractDomain = sig
  type t
  type context
  val context : context Syntax.context

  (** Set of symbols that the abstraction is over *)
  val symbols : Syntax.symbol list

  val bottom : t
  val join : t -> t -> t
  val concretize : t -> context Syntax.formula
  val abstract : context Syntax.formula -> context Interpretation.interpretation -> t

  val pp : Format.formatter -> t -> unit

end

module type Context = sig type t val context : t Syntax.context end
module type PreservedSymbols = sig val symbols : Syntax.symbol list end

module CooperProjection (C : Context) (S : PreservedSymbols)
       : (AbstractDomain with type t = DD.closed DD.t * IntLattice.t
                          and type context = C.t) = struct

  type t = DD.closed DD.t * IntLattice.t
  type context = C.t
  let context = C.context

  let symbols = S.symbols
  let dimensions = Util.dims_of_symbols symbols

  (* Symbols are 0-indexed *)
  let num_dims = Util.max_dim_in_symbols symbols + 1

  let bottom = ( P.dd_of num_dims P.bottom
               , IntLattice.hermitize [V.of_term QQ.one Linear.const_dim]
               )

  let join (p1, l1) (p2, l2) = (DD.join p1 p2, IntLattice.intersect l1 l2)

  let concretize (p, l) =
    let p_formulas = DD.enum_constraints p
                     /@ Util.formula_of_constraint context
                     |> BatList.of_enum in
    let l_formulas = List.map (fun v -> Syntax.mk_is_int context (Linear.of_linterm context v))
                       (IntLattice.basis l) in
    Syntax.mk_and context (p_formulas @ l_formulas)

  let abstract formula interp =
    let (inequalities, lattice_constraints) =
      Util.constraints_of_implicant context
        (Interpretation.select_implicant interp formula) in
    let p = P.of_constraints (BatList.enum inequalities) in
    let (all_dims, codims) =
      let p_dims = BatList.fold_left (Util.collect_non_constant_dimensions snd)
                     IntSet.empty inequalities in
      let l_dims = BatList.fold_left (Util.collect_non_constant_dimensions (fun x -> x))
                     IntSet.empty lattice_constraints in
      let all_nonconstant_dims = IntSet.union p_dims l_dims in
      (all_nonconstant_dims, IntSet.diff all_nonconstant_dims dimensions)
    in
    let (integer_codims, real_codims) = IntSet.partition (Util.is_int context) codims in
    let () = if not (IntSet.is_empty real_codims) then
               failwith "Cannot eliminate real variable"
             else () in
    let m = Util.map_of interp in
    let l =
      let symbol_dimensions =
        IntSet.fold
          (fun dim l ->
            if (Util.is_int context dim) then V.of_term QQ.one dim :: l else l)
          all_dims [] in
      IntLattice.hermitize (lattice_constraints @ symbol_dimensions) in
    let (projected_p, projected_l) =
      IntegerMbp.local_project_cooper (Util.is_int context) m
        ~eliminate:integer_codims (p, l) in
    logf "Computing lattice polyhedron after Cooper...@.";
    let hull = LatticePolyhedron.lattice_polyhedron_of projected_p projected_l in
    logf "Computed lattice polyhedron after Cooper@.";
    ( DD.of_constraints_closed num_dims (P.enum_constraints hull)
    , projected_l)

  let pp fmt (p, l) =
    Format.fprintf fmt "{ polyhedron : %a @. lattice: %a }"
      (DD.pp (fun fmt d -> Format.fprintf fmt "%d" d)) p
      (IntLattice.pp Util.pp_dim) l

end

module RecessionConeProjection (C : Context) (S : PreservedSymbols)
       : (AbstractDomain with type t = DD.closed DD.t
                          and type context = C.t) = struct

  type t = DD.closed DD.t
  type context = C.t
  let context = C.context

  let symbols = S.symbols
  let dimensions = Util.dims_of_symbols symbols

  let num_dims = Util.max_dim_in_symbols symbols + 1

  let bottom = P.dd_of num_dims P.bottom

  let join p1 p2 = DD.join p1 p2

  let concretize p =
    let p_formulas = DD.enum_constraints p
                     /@ Util.formula_of_constraint context
                     |> BatList.of_enum in
    Syntax.mk_and context p_formulas

  let abstract formula interp =
    let (inequalities, _lattice_constraints) =
      Util.constraints_of_implicant context
        (Interpretation.select_implicant interp formula) in
    let p = P.of_constraints (BatList.enum inequalities) in
    let codims = BatList.fold_left (Util.collect_non_constant_dimensions snd)
                   IntSet.empty inequalities
                 |> (fun s -> IntSet.diff s dimensions)
    in
    let (integer_codims, real_codims) =
      IntSet.partition (Util.is_int context) codims in
    let () = if not (IntSet.is_empty real_codims) then
               failwith "Cannot eliminate real variable"
             else () in
    let m = Util.map_of interp in
    let projected_p =
      IntegerMbp.local_project_recession m ~eliminate:integer_codims p in
    P.dd_of num_dims projected_p

  let pp fmt p =
    Format.fprintf fmt "{ polyhedron : %a }"
      (DD.pp (fun fmt d -> Format.fprintf fmt "%d" d)) p

end

module IntHullProjection (C : Context) (S : PreservedSymbols)
         (F : sig val max_dim : int end)
       : (AbstractDomain with type t = DD.closed DD.t
                          and type context = C.t) = struct

  type t = DD.closed DD.t
  type context = C.t
  let context = C.context

  let symbols = S.symbols
  let dimensions = Util.dims_of_symbols symbols

  let num_dims = F.max_dim + 1

  let bottom = P.dd_of num_dims P.bottom

  let join p1 p2 = DD.join p1 p2

  let concretize p =
    let p_formulas = DD.enum_constraints p
                     /@ Util.formula_of_constraint context
                     |> BatList.of_enum in
    Syntax.mk_and context p_formulas

  let abstract formula interp =
    let (inequalities, _lattice_constraints) =
      Util.constraints_of_implicant context
        (Interpretation.select_implicant interp formula) in
    let p = DD.of_constraints_closed num_dims (BatList.enum inequalities) in
    let hull = DD.integer_hull p in
    let codims = BatList.fold_left (Util.collect_non_constant_dimensions snd)
                   IntSet.empty inequalities
                 |> (fun s -> IntSet.diff s dimensions)
    in
    DD.project (IntSet.to_list codims) hull

  let pp fmt p =
    Format.fprintf fmt "{ polyhedron : %a }"
      (DD.pp (fun fmt d -> Format.fprintf fmt "%d" d)) p

end

module Abstract (A : AbstractDomain) : sig

  val abstract : A.context Syntax.formula -> A.t

end = struct

  type t =
    {
      solver : A.context Smt.StdSolver.t
    ; value : A.t
    }

  let init formula =
    let solver = Smt.StdSolver.make A.context in
    Smt.StdSolver.add solver [formula];
    { solver ; value = A.bottom }

  let abstract formula =
    let state = init formula in
    let rec go bound n state =
      logf "Iteration %d@." n;
      match Smt.StdSolver.get_model state.solver with
      | `Sat interp ->
         let rho = A.abstract formula interp in
         logf "abstract: abstracted, now joining";
         let joined = A.join state.value rho in
         logf "abstract: joining rho %a with %a to get %a@."
           A.pp rho
           A.pp state.value
           A.pp joined;
         let formula = A.concretize joined in
         logf "abstract: new constraint to negate: %a@." (Syntax.pp_smtlib2 A.context) formula;
         Smt.StdSolver.add state.solver
           [Syntax.mk_not A.context formula];
         let next = { state with value = joined } in
         begin match bound with
         | Some b -> if n <= b then go (Some b) (n + 1) next
                     else state
         | None -> go bound (n + 1) next
         end
      | `Unsat ->
         state
      | `Unknown -> failwith "Can't get model"
    in (go None 1 state).value

end

let integer_hull_by_recession_cone (type a) (context : a Syntax.context)
      (formula : a Syntax.formula) symbols =
  let module C = struct type t = a let context = context end in
  let module S = struct let symbols = symbols end in
  let module Abstraction = RecessionConeProjection(C)(S) in
  let module Compute = Abstract(Abstraction) in
  Compute.abstract formula

let integer_hull_by_cooper (type a) (context : a Syntax.context)
      (formula : a Syntax.formula) symbols =
  let module C = struct type t = a let context = context end in
  let module S = struct let symbols = symbols end in
  let module Abstraction = CooperProjection(C)(S) in
  let module Compute = Abstract(Abstraction) in
  Compute.abstract formula

let integer_hull_standard (type a) (context : a Syntax.context)
      (formula : a Syntax.formula) symbols =
  let module C = struct type t = a let context = context end in
  let module S = struct let symbols = symbols end in
  let max_dim = Util.max_dim_in_symbols
                  (Syntax.Symbol.Set.elements (Syntax.symbols formula)) in
  let module F = struct let max_dim = max_dim end in
  let module Abstraction = IntHullProjection(C)(S)(F) in
  let module Compute = Abstract(Abstraction) in
  Compute.abstract formula
