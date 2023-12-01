
(** LIRA vectors represent a subset of LIRA terms: those that are linear in
    floor(x) and fractional(x) (0 <= fractional(x) < 1),
    where x ranges over a set of so-called "original" dimensions.

    LIRA vectors have to exist within a common [dimension_binding] that maps
    bijectively between dimensions [x] that can occur (original dimensions) and
    the "integer-fractional" dimensions [x_int] and [x_frac]
    (corresponding to floor(x), fractional(x)) of vectors.
    When formulas are involved, they should exist within a common [context]
    that includes a bijection [symbol_binding] between symbols and original
    dimensions.

    At the high level, these details are unnecessary: [project] computes, 
    for a LIRA formula [F], the strongest set of conjunctive non-strict 
    inequality consequences that are linear in a given set of terms [T].
    When working with polyhedra representations or with formulas themselves,
    the appropriate common context should be created.
 *)

type dimension_binding

(** Integer and fractional dimensions begin at the first even number >= [initial].
    To compute projections in terms of LRA-linear terms, [initial] should be
    greater than all dimensions corresponding to input formulas
    (e.g., > maximum symbol in a context).
 *)
val empty: initial:int -> dimension_binding

(** [add_dimension n binding] is a binding that associates [n]
    ("ordinary dimension") with a new dimension [n_int] and a new dimension
    [n_frac].
    The dimensions in the "ordinary" space (the one that [n] is drawn from)
    and the integer-fractional space are not guaranteed to be disjoint.
    To make them disjoint, initialize [binding] with an [initial] that is
    large enough.
 *)
val add_dimension: int -> dimension_binding -> dimension_binding

val int_frac_dim_of: int -> dimension_binding -> int * int

val original_dim_of: int -> dimension_binding -> int

(** Given [P], [L] in only integer-fractional dimensions making sense within
    [binding], and a point [m] in [P /\ L],
    [local_project_int_frac binding m onto_original (P, L) = (P', L')]
    implies that
    - [P'], [L'] are in only integer-fractional dimensions that corresponds
      to original dimensions in [onto_original].
    - [m] satisfies [P' /\ L']
    - If [Y] is the set of original dimensions not in [onto_original],
      [P' /\ L'] |= exists Y. (Int(Y_int) /\ 0 <= Y_frac < 1) /\ P /\ L].
 *)
val local_project_int_frac:
  dimension_binding -> (int -> QQ.t) ->
  onto_original:int list -> Polyhedron.t * IntLattice.t ->
  Polyhedron.t * IntLattice.t

(** Assuming that the integer-fractional dimensions of (P, L) are disjoint
    from the original dimensions corresponding to them,
    and [m] is a point in [P /\ L],
    [local_project_onto_original binding m (P, L) = (P', L')] implies that
    - [P'], [L'] are in original dimensions.
    - [m] satisfies [P' /\ L'], where each original dimension [x] is
      interpreted as [x_int + x_frac].
    - If [aX >= b] is an inequality that is in only original dimensions and
      [P /\ L /\ Int(X_int) /\ 0 <= X_frac < 1 /\ X = X_int + X_frac] 
      implies [aX >= b], then [(P', L') |= aX >= b].
      (The inequality must be non-strict.)
 *)
val local_project_onto_original:
  dimension_binding -> (int -> QQ.t) -> Polyhedron.t * IntLattice.t ->
  Polyhedron.t * IntLattice.t

type 'a context

(** A [syntax_dimension_map] consists of an isomorphism pair between the
    set of symbols that occur and the space of "ordinary" dimensions
    (introduced through [add_dimension]).
    The "ordinary" space can have dimensions that correspond to terms instead
    of just symbols, in which case [term_of_dim] gives them meaning.
 *)
type 'a symbol_binding =
  {
    dim_of_symbol: Syntax.symbol -> int
  ; symbol_of_dim: int -> Syntax.symbol option
  ; term_of_dim: int -> 'a Syntax.arith_term option
  }

(** [make symbol_binding dimension_binding] is a context that maps
    bijectively between symbols and integer-fractional dimensions.
*)
val make: 'a symbol_binding -> dimension_binding -> 'a context

(** Given a [ctx] that contains symbols occurring in [term]
    and an interpretation [interp],
    [linearize_term srk ctx interp term = (phi, v)], where
    (1) [v] has only integer-fractional dimensions, and corresponds to a LIRA
        term by interpreting its entries as coefficients of [x_int] and [x_frac],
        via [ctx].
    (2) [interp |= phi |= term = v] modulo LIRA and the constraints
        [x = x_int + x_frac /\ Int(x_int) /\ 0 <= x < 1] for each [x] in [ctx].
 *)
val linearize:
  'a Syntax.context -> 'a context ->
  'a Interpretation.interpretation -> 'a Syntax.arith_term ->
  (Polyhedron.t * IntLattice.t) * Linear.QQVector.t

(** Given a conjunctive formula [implicant] in the language of LIRA,
    a [ctx] that contains all symbols in [implicant],
    and an interpretation [interp] that satisfies [implicant],
    [lira_implicant srk ctx interp implicant = (P, L)] where
    (1) [P] and [L] are in only integer-fractional dimensions, and interpreted
        as constraints via [ctx].
    (2) [interp |= P /\ L |= implicant] modulo LIRA and the constraints
        [x = x_int + x_frac /\ Int(x_int) /\ 0 <= x < 1] for each [x] in [ctx].
 *)
val lira_implicant_of_implicant:
  'a Syntax.context -> 'a context -> 'a Interpretation.interpretation ->
  'a Syntax.formula list -> Polyhedron.t * IntLattice.t

val project:
  'a Syntax.context -> 'a Syntax.formula -> ('a Syntax.arith_term) array ->
  DD.closed DD.t
