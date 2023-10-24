(** This module performs operations on polyhedron-lattice pairs.
    A polyhedron-lattice pair (P, L) represents a mixed linear integer-real
    set of points {x: x |= constraints_of(P) /\ x |= Int(v), v \in L}.
    That is, the vectors in L are generators of the constraints for Int(),
    while the constraints of P are constraints for inequalities.
 *)

(** [mixed_lattice_hull p l] computes the "integer" hull of [p] w.r.t. [l],
    where [p] need not be in the linear space spanned by [l].
    The generators of [l] are the generators of the integrality
    constraints.
 *)
val mixed_lattice_hull: 'a Syntax.context -> Polyhedron.t -> IntLattice.t -> Polyhedron.t

(** 
    Given (P, L) representing a linear arithmetic formula and [elim] a list of
    integer variables, and a point [m] in [P /\ L],
    [local_project_cooper m elim p l] computes (P', L') such that
    (i)   [P'] and [L'] are in dimensions excluding [elim].
    (ii)  [m] is in [P' /\ L'].
    (iii) There exists terms [ts] such that 
          [formula_of(P') = formula_of(P)[ts/elim]]
          and [formula_of(L') = formula_of(P)[ts/elim]].
    The algorithm is a local projection version of Cooper's algorithm.
    When the linear span of [L] contains all dimensions of [P] (e.g., when all
    variables are integral), local projection is image-finite (i.e., the 
    number of terms [ts] over all [m] in [P /\ L] is finite) because of 
    Cooper's result.

    In the general case, it is not, and [local_project_cooper] takes 
    a function [round] that discretizes the greatest lower bound term 
    (of a variable to be eliminated) to possibly get a finite image.

    Precisely, [round] has to be a function satisfying the following conditions.
    If [round ckind lower_bound m = (t, ineqs, ints)],
    - [ineqs /\ IsInt(ints) |= t >= lower_bound].
    - For all integers n, 
      [ineqs /\ IsInt(ints) |= n <ckind> lower_bound -> n <ckind> t].
    - [ineqs], [ints], and [t] all involve only dimensions in [lower_bound].
    These ensure soundness, i.e., that (i), (ii) and (iii) hold.

    For image-finiteness, [round] needs to satisfy the following.
    - [round ckind lower_bound] as a function from points of [P /\ L] to 
      {(t, ineqs, ints)} has a finite image.
    - When [round ckind lower_bound m = (t, ineqs, ints)],
      {t(valuation): valuation in Q^{variables in t}} is a subset of 
      {rn: n \in ZZ} for some rational [r].
 *)
val local_project_cooper:
    (int -> QQ.t) -> eliminate: int list ->
    ?round_lower_bound:
      (Polyhedron.constraint_kind -> Linear.QQVector.t -> (int -> QQ.t) ->
       Linear.QQVector.t * (Polyhedron.constraint_kind * Linear.QQVector.t) list *
         Linear.QQVector.t list) ->
    Polyhedron.t -> IntLattice.t ->
    Polyhedron.t * IntLattice.t
