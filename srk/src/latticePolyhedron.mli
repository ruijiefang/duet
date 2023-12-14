(** This module performs operations on polyhedron-lattice pairs.
    A polyhedron-lattice pair (P, L) represents a mixed linear integer-real
    set of points {x: x |= constraints_of(P) /\ x |= Int(v), v \in L}.
    That is, the vectors in L are generators of the constraints for Int(),
    while the constraints of P are constraints for inequalities.
    Inequalities for polyhedra in this module can be strict.

    For [abstract] procedures, variables that have integer type within the
    syntactic context do not need to be asserted as integers via [is_int]
    explicitly.
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

    Ambient dimension should be at least as large as the maximum dimension
    occurring in the formula (computed via [dim_of_symbol]) + 1.
 *)
val mixed_lattice_hull:
  'a Syntax.context ->
  symbol_of_dim:(int -> Syntax.symbol option) ->
  ?term_of_dim:(int -> 'a Syntax.arith_term option) ->
  dim_of_symbol:(Syntax.symbol -> int) ->
  ambient_dim: int ->
  (Polyhedron.t * IntLattice.t) list -> DD.closed DD.t

(** `PureGomoryChvatal is guaranteed to work only when all variables are
    implied to be integer-valued, but this is not checked; the lattice part
    of the formula is ignored.
    TODO: This option is exported for testing purposes only; to be removed.
    Ambient dimension should be at least as large as the maximum dimension
    occurring in the formula (computed via [dim_of_symbol]) + 1.
 *)
val abstract_lattice_hull:
  'a Syntax.context ->
  how:[`Mixed | `PureGomoryChvatal] ->
  symbol_of_dim:(int -> Syntax.symbol option) ->
  dim_of_symbol:(Syntax.symbol -> int) ->
  ambient_dim:int ->
  'a Syntax.formula -> DD.closed DD.t

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

val all_variables_are_integral_and_no_strict_ineqs: ceiling

(**
   Given (P, L) representing a linear arithmetic formula, a point [m] in
   [P /\ L], and [elim] a list of dimensions such that
   [P /\ L |= Int(x)] for each [x] in [elim],
   and a [ceiling] that is sound (following the specification above),
   [local_project_cooper m elim ceiling round (P, L)] computes (P', L', ts)
   such that
   (i)   [P'] and [L'] are in dimensions excluding [elim].
   (ii)  [m |= exists [elim]. P' /\ L'].
   (iii) [ts] are terms (corresponding order-wise to [elim]) such that
         [formula_of(P') = formula_of(P)[ts/elim]]
         and [formula_of(L') = formula_of(P)[ts/elim]].

   The algorithm generalizes Cooper-based model-based projection
   for LIA to mixed integer-real arithmetic, where we use a suitable [ceiling]
   to ensure the algorithm has finite image, i.e., iterating
   [local_project_cooper] in a DPLL(T)-style loop terminates.

   When only non-strict inequalities are present, [`NonstrictIneqsOnly]
   is a sound ceiling; it guarantees (i) -- (iii) above.
   If [P /\ L] is a subset of ZZ^n, it is image-finite by Cooper's result.
   It is however NOT image-finite in general.

   When strict inequalities are present, [`RoundStrictWhenVariablesIntegral]
   converts strict inequalities to an equivalent loose non-strict inequality
   when possible, and raises PositiveIneqOverRealVar when this cannot be done.
 *)
val local_project_cooper:
  (int -> QQ.t) -> eliminate: int Array.t ->
  [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
  Polyhedron.t * IntLattice.t ->
  Polyhedron.t * IntLattice.t *
    [`MinusInfinity | `PlusInfinity | `Term of Linear.QQVector.t] Array.t

(** v > 0 with a dimension that may be real-valued *)
exception PositiveIneqOverRealVar of Linear.QQVector.t * int

val project_cooper:
  'a Syntax.context -> symbol_of_dim:(int -> Syntax.symbol option) ->
  ?term_of_dim:(int -> 'a Syntax.arith_term option) ->
  dim_of_symbol:(Syntax.symbol -> int) -> eliminate: int list ->
  [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
  (Polyhedron.t * IntLattice.t) list ->
  DD.closed DD.t * IntLattice.t

(** [project_and_hull elim round phis] computes the set of non-strict
    inequalities in dimensions not in [elim] that are implied by [phis].
    This is done by local projection ([local_project_cooper])
    followed by local hulling ([local_mixed_lattice_hull]),
    and repeating this until a fixed point is reached.
    This diverges in general when some variable is real-valued (whether
    the variable is to be eliminated or not).
 *)
val project_and_hull:
  'a Syntax.context ->
  symbol_of_dim:(int -> Syntax.symbol option) ->
  dim_of_symbol:(Syntax.symbol -> int) ->
  eliminate: int list ->
  [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
  (Polyhedron.t * IntLattice.t) list -> DD.closed DD.t

(** [hull_and_project elim round phis] computes the set of non-strict
    inequalities in dimensions not in [elim] that are implied by [phis].
    This is done by local hulling ([local_mixed_lattice_hull])
    followed by local projection ([local_project_cooper]), until a fixed point
    is reached.
    This may diverge when variables in [elim] can be real-valued, but should
    converge otherwise.
 *)
val hull_and_project:
  'a Syntax.context ->
  symbol_of_dim:(int -> Syntax.symbol option) ->
  dim_of_symbol:(Syntax.symbol -> int) ->
  eliminate: int list ->
  [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
  (Polyhedron.t * IntLattice.t) list -> DD.closed DD.t

val abstract_by_local_project_and_hull:
  'a Syntax.context ->
  [`DefineThenProject | `ProjectThenRealQe] ->
  [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
  'a Syntax.formula -> ('a Syntax.arith_term) array -> DD.closed DD.t

val abstract_by_local_hull_and_project:
  'a Syntax.context ->
  [`DefineThenProject | `ProjectThenRealQe] ->
  [`RoundLowerBound of ceiling | `NonstrictIneqsOnly | `RoundStrictWhenVariablesIntegral] ->
  'a Syntax.formula -> ('a Syntax.arith_term) array -> DD.closed DD.t
