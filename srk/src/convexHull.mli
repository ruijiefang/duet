open Syntax

type t = DD.closed DD.t

(** Given terms [t_0,...,t_n], compute the closed convex hull all points [ {
   (t_0(x),...,t_n(x)) : x |= F } ], where [F] is the underlying formula of
   the solver. *)
val abstract : 'a Abstract.Solver.t ->
  ?man:(DD.closed Apron.Manager.t) ->
  ?bottom:(t option) ->
  'a arith_term array ->
  t

(** Given a formula [F] and terms [t_0,...,t_n], compute the closed convex
   hull all points [ { (t_0(x),...,t_n(x)) : x |= F } ]. *)
val conv_hull : ?man:(DD.closed Apron.Manager.t) ->
  'a context ->
  'a formula ->
  ('a arith_term) array ->
  DD.closed DD.t

val of_model_lira : 'a Abstract.Solver.t ->
  (DD.closed Apron.Manager.t) ->
  ('a arith_term) array ->
  'a Abstract.smt_model ->
  DD.closed DD.t

val of_model_lirr : 'a Abstract.Solver.t ->
  (DD.closed Apron.Manager.t) ->
  ('a arith_term) array ->
  'a Abstract.smt_model ->
  DD.closed DD.t
