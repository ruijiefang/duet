(** This module performs operations on polyhedron-lattice pairs.
    A polyhedron-lattice pair (P, L) represents a mixed linear integer-real
    set of points {x: x |= constraints_of(P) /\ x |= Int(v), v \in L}.
    That is, the vectors in L are generators of the constraints for Int(),
    while the constraints of P are constraints for inequalities.
    Inequalities for polyhedra in this module can be strict.
 *)

(** Given a point [m] in the intersection of [P] and [L],
    [local_mixed_lattice_hull m P L = P'] is a subpolyhedron in the lattice hull
    of [P] with respect to L that contains [m].
    If [P /\ L |= a^T x >= b], then [P' |= a^T x >= b].
    This procedure has finite image.
*)
val local_mixed_lattice_hull:
  (int -> QQ.t) -> Polyhedron.t * IntLattice.t -> Polyhedron.t

(** Compute the lattice hull of points satisfying
    (P1 /\ L1) \/ ... \/ (Pn /\ Ln), i.e., a polyhedron [P] such that
    - [(P1 /\ L1) \/ ... \/ (Pn /\ Ln) |= ax >= b] for each constraint
      [ax >= b] of [P].
    - For all [ax >= b] that is implied by [\/ (P_i /\ Li)],
      [P |= ax >= b].
 *)
val mixed_lattice_hull:
  'a Syntax.context ->
  symbol_of_dim:(int -> Syntax.symbol option) ->
  dim_of_symbol:(Syntax.symbol -> int) ->
  (Polyhedron.t * IntLattice.t) list -> DD.closed DD.t

(** A ceiling (f, g) is such that
    - The image of [f] is a lattice of QQ that contains ZZ.
      (This is needed for [local_project_cooper] to be sound and image-finite.)
    - [f `Nonneg x = y] only if [y] is the smallest number in the image of [f]
      that is at least [x].
    - [f `Pos x = y] only if [y] is the smallest number in the image of [f]
      that is strictly greater than [x].
    - [g ckind lower_bound m = (t, ineqs, ints)] only if
      + [m |= ineqs /\ ints]
      + For all valuations [m] satisfying [ineqs /\ ints],
        [m(t) = f ckind m(lower_bound)].
      + [ineqs], [ints], and [t] all involve only dimensions in [lower_bound].
 *)
type ceiling =
  {
    round_value: [`Nonneg | `Pos] -> QQ.t -> QQ.t
  ; round_term:
      [`Nonneg | `Pos] -> Linear.QQVector.t -> (int -> QQ.t) ->
      Linear.QQVector.t * (Polyhedron.constraint_kind * Linear.QQVector.t) list *
        Linear.QQVector.t list
  }

(**
   Given (P, L) representing a linear arithmetic formula, a point [m] in
   [P /\ L], and [elim] a list of dimensions such that
   [P /\ L |= Int(x)] for each [x] in [elim],
   [local_project_cooper m elim (P, L)] computes (P', L', ts) such that
   (i)   [P'] and [L'] are in dimensions excluding [elim].
   (ii)  [m |= exists [elim]. P' /\ L'].
   (iii) [ts] are terms (corresponding order-wise to [elim]) such that
         [formula_of(P') = formula_of(P)[ts/elim]]
         and [formula_of(L') = formula_of(P)[ts/elim]].

   The algorithm generalizes Cooper-based model-based projection
   for LIA to mixed integer-real arithmetic. The default case
   assumes that all variables are integer-valued and every inequality
   is loose, in which case no rounding is necessary and the algorithm
   has finite image by Cooper's result. (Every formula with strict
   inequalities and only integer-valued variables has an equivalent
   form with only loose inequalities.)

   In the general case, it does not, and [local_project] takes
   a function [round] that discretizes the greatest lower bound term
   to get a finite image.

   Precisely, [round] has to be a function satisfying the following conditions.
   If [round ckind lower_bound m = (t, ineqs, ints)],
   - [ineqs /\ IsInt(ints) |= t >= lower_bound].
   - For all integers n,
     [ineqs /\ IsInt(ints) |= n <ckind> lower_bound -> n <ckind> t].
   - [ineqs], [ints], and [t] all involve only dimensions in [lower_bound].
   - [m |= ineqs /\ ints]
   These ensure soundness, i.e., that (i), (ii) and (iii) hold.

   For image-finiteness, [round] needs to satisfy the following.
   - [round ckind lower_bound] as a function from points of [P /\ L] to
     {(t, ineqs, ints)} has a finite image.
   - When [round ckind lower_bound m = (t, ineqs, ints)],
     {t(valuation): valuation in Q^{variables in t}} is a subset of
     {rn: n \in ZZ} for some rational [r].
 *)
val local_project_cooper:
  (int -> QQ.t) -> eliminate: int Array.t ->
  ?round_lower_bound: ceiling ->
  Polyhedron.t * IntLattice.t ->
  Polyhedron.t * IntLattice.t *
    [`MinusInfinity | `PlusInfinity | `Term of Linear.QQVector.t] Array.t

val project_cooper:
  'a Syntax.context -> symbol_of_dim:(int -> Syntax.symbol option) ->
  dim_of_symbol:(Syntax.symbol -> int) ->
  eliminate: int list -> ?round_lower_bound: ceiling ->
  (Polyhedron.t * IntLattice.t) list ->
  DD.closed DD.t * IntLattice.t

(*
(** [local_project_and_hull m elim (P, L) = P'] is a polyhedron
    whose constrained dimensions exclude [elim], [m |= P'], and
    for any inequality [a^T y >= b], if [P /\ L |= a^T y >= b],
    [P' |= a^T y >= b].
    Image-finiteness depends on [round_lower_bound] in general,
    which has the same meaning as the one for [local_project_cooper].
 *)
val local_project_and_hull:
  (int -> QQ.t) -> eliminate: int list -> ?round_lower_bound: ceiling ->
  Polyhedron.t * IntLattice.t ->
  Polyhedron.t
 *)


(** [hull_and_project elim round phis] computes the set of non-strict 
    inequalities in dimensions not in [elim] that are implied by [phis].
    This is done by [local_hull_and_project] until fixed point.
    This diverges in general when some variable is real-valued.
 *)
val project_and_hull:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    eliminate: int list -> ?round_lower_bound: ceiling ->
    (Polyhedron.t * IntLattice.t) list -> DD.closed DD.t

(** [hull_and_project elim round phis] computes the set of non-strict 
    inequalities in dimensions not in [elim] that are implied by [phis].
    This is done by [local_hull_and_project] until fixed point.
    This may diverge when variables in [elim] can be real-valued, but should
    converge otherwise.
 *)
val hull_and_project:
    'a Syntax.context ->
    symbol_of_dim:(int -> Syntax.symbol option) -> dim_of_symbol:(Syntax.symbol -> int) ->
    eliminate: int list -> ?round_lower_bound: ceiling ->
    (Polyhedron.t * IntLattice.t) list -> DD.closed DD.t
