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

val abstract_lw:
    elim: (int -> bool) ->
    (Polyhedron.t, int -> QQ.t, Polyhedron.t, int -> QQ.t) LocalAbstraction.t

val abstract_cooper:
    elim: (int -> bool) ->
    ceiling: (V.t -> (int -> QQ.t) -> (V.t * (P.constraint_kind * V.t) list * V.t list)) ->
    ('layout plt, int -> QQ.t, 'layout plt, int -> QQ.t) LocalAbstraction.t

val abstract_sc:
  max_dim_in_projected: int ->
  ('layout plt, int -> QQ.t, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t

val convex_hull_sc: [`ReplaceModFloor | `NoModFloor] ->
                    'a Syntax.context -> 'a Syntax.formula ->
                    ('a Syntax.arith_term ) Array.t -> DD.closed DD.t

val cooper_project: [`ReplaceModFloor | `NoModFloor] ->
                    'a Syntax.context -> 'a Syntax.formula ->
                    ('a Syntax.arith_term ) Array.t -> standard plt list

val convex_hull_lia: [`ReplaceModFloor | `NoModFloor] ->
                     'a Syntax.context -> 'a Syntax.formula ->
                     ('a Syntax.arith_term ) Array.t -> DD.closed DD.t

val convex_hull_lra: [`ReplaceModFloor | `NoModFloor] ->
                     'a Syntax.context -> 'a Syntax.formula ->
                     ('a Syntax.arith_term ) Array.t -> DD.closed DD.t
