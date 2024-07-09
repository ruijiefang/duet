(** Concept space of polyhedron-lattice-tilings (PLTs) *)

module P = Polyhedron
module V = Linear.QQVector

module LocalAbstraction: sig

  type ('concept1, 'point1, 'concept2, 'point2) t

  val apply: ('concept1, 'point1, 'concept2, 'point2) t ->
             'point1 -> 'concept1 -> 'concept2

  val compose:
    ('concept2, 'point2, 'concept3, 'point3) t ->
    ('concept1, 'point1, 'concept2, 'point2) t ->
    ('concept1, 'point1, 'concept3, 'point3) t

end

module Abstraction: sig

  type ('concept1, 'point1, 'concept2, 'point2) t

  val apply: ('concept1, 'point1, 'concept2, 'point2) t -> 'concept1 -> 'concept2

end

module LocalGlobal: sig

  val localize:
    ('concept1, 'point1, 'concept2, 'point2) Abstraction.t ->
    ('concept1, 'point1, 'concept2, 'point2) LocalAbstraction.t

  val lift_dd_abstraction:
    ?solver: 'a Abstract.Solver.t option ->
    ?bottom: DD.closed DD.t option ->
    man:(DD.closed Apron.Manager.t) ->
    'a Syntax.context -> max_dim:int -> term_of_dim:(int -> 'a Syntax.arith_term) ->
    ('a Syntax.formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> QQ.t)
      LocalAbstraction.t ->
    ('a Syntax.formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> QQ.t)
      Abstraction.t

end

type standard
type intfrac
type 'layout plt

val formula_of_dd:
  'a Syntax.context -> (int -> 'a Syntax.arith_term) -> DD.closed DD.t ->
  'a Syntax.formula

val formula_of_plt:
  'a Syntax.context -> (int -> 'a Syntax.arith_term) -> 'layout plt ->
  'a Syntax.formula

val cooper_project: 'a Syntax.context -> 'a Syntax.formula ->
                    ('a Syntax.arith_term ) Array.t -> standard plt list

val disjunctive_normal_form:
  'a Syntax.context -> base_dim:int -> 'a Syntax.formula ->
  (standard plt list * 'a Syntax.arith_term SrkUtil.Int.Map.t)

val convex_hull_of_lira_model:
  [ `SubspaceCone
  | `SubspaceConeAccelerated
  | `IntFrac
  | `IntFracAccelerated
  | `LwCooper of
      [ `IntRealHullAfterProjection
      | `IntHullAfterProjection
      | `NoIntHullAfterProjection
      ]
  | `Lw ] ->
  'a Abstract.Solver.t ->
  DD.closed Apron.Manager.t ->
  ('a Syntax.arith_term) array -> 'a Abstract.smt_model ->
  DD.closed DD.t

val abstract: [ `SubspaceCone
              | `SubspaceConeAccelerated
              | `SubspaceConePrecondAccelerate
              | `Subspace
              | `IntFrac
              | `IntFracAccelerated
              | `LwCooper of
                  [ `IntRealHullAfterProjection
                  | `IntHullAfterProjection
                  | `NoIntHullAfterProjection]
              | `Lw
              ] ->
              'a Abstract.Solver.t ->
              ?man:(DD.closed Apron.Manager.t) ->
              ?bottom:(DD.closed DD.t option) ->
              'a Syntax.arith_term array ->
              DD.closed DD.t

val convex_hull:
  [ `SubspaceCone
  | `SubspaceConeAccelerated
  | `SubspaceConePrecondAccelerate
  | `Subspace
  | `IntFrac
  | `IntFracAccelerated
  | `LwCooper of
      [ `IntRealHullAfterProjection
      | `IntHullAfterProjection
      | `NoIntHullAfterProjection]
  | `Lw
  ] ->
  ?man:(DD.closed Apron.Manager.t) ->
  'a Syntax.context -> 'a Syntax.formula ->
  ('a Syntax.arith_term) Array.t -> DD.closed DD.t

(** Sound only when all variables in the formula are of integer type,
    and there are no integrality constraints.
    Integrality constraints apart from integrality of variables are
    completely ignored.
    The correspondence between symbols and dimensions are
    via [Syntax.symbol_of_int] and [Syntax.int_of_symbol].
*)
val full_integer_hull_then_project:
  ?man:(DD.closed Apron.Manager.t) ->
  [`GomoryChvatal | `Normaliz] ->
  to_keep:Syntax.Symbol.Set.t ->
  'a Syntax.context -> 'a Syntax.formula ->
  DD.closed DD.t

(** Sound only when all variables in the formula are of integer type,
    and there are no integrality constraints.
    Integrality constraints apart from integrality of variables are
    completely ignored.
*)
val full_integer_hull_then_project_onto_terms:
  ?man:(DD.closed Apron.Manager.t) ->
  [`GomoryChvatal | `Normaliz] ->
  'a Syntax.context -> 'a Syntax.formula ->
  ('a Syntax.arith_term) Array.t -> DD.closed DD.t


val convex_hull_lia:
  'a Syntax.context -> 'a Syntax.formula ->
  ('a Syntax.arith_term) Array.t -> DD.closed DD.t

val convex_hull_lra:
  'a Syntax.context -> 'a Syntax.formula ->
  ('a Syntax.arith_term) Array.t -> DD.closed DD.t

module PolyhedralFormula: sig

  (** Let Sigma = (=, <, <=, Int, +, -, *, /, floor, mod, QQ). *)

  (** For [phi] a quantifier-free formula in [Sigma],
      [polyhedral_formula_of_qf srk phi = (psi, new_symbols)] is such that
      [psi] is equivalent to [phi] modulo the standard theory of reals, whose symbols
      is among the symbols of [phi] and [new_symbols], and [psi] is a polyhedral
      formula, i.e., one with no Int constraints.
   *)
  val polyhedral_formula_of_qf: 'a Syntax.context -> 'a Syntax.Formula.t ->
                                'a Syntax.Formula.t * Syntax.Symbol.Set.t

  (** For [phi] a quantifier-free formula in [Sigma],
      [retype_as srk forced_typ phi = (psi, remap)] is such that
      [psi] is a polyhedral formula,
      all symbols in [psi] are of type [forced_typ], and [remap] maps
      symbols in [phi] that have a different type from [forced_typ] to
      new symbols of type [forced_typ] that replaces them to get [psi].

      If [remap] is empty, projecting [psi] onto the symbols of [phi]
      is equivalent to [phi].
      Otherwise, [remap phi |= psi], where [remap phi] is obtained by
      substituting [remap s] for symbols [s] in the domain of [remap].
   *)
  val retype_as:
    'a Syntax.context -> [`TyInt | `TyReal] -> 'a Syntax.Formula.t ->
    'a Syntax.Formula.t * (Syntax.symbol Syntax.Symbol.Map.t)

end
