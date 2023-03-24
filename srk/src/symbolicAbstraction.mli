(** Computing integer hull of existentially quantified formulas using
    model-based projection.
    The existential quantifiers have to be over integer-typed variables
    (for now).
*)

(** [integer_hull_by_recession_cone srk phi symbols] computes the
    smallest polyhedron in the dimensions spanned by [symbols]
    that contains all integer points satisfying [phi].
    The algorithm works by iteratively sampling a model and abstracting
    it to a recession cone contained in [psi],
    where [phi = exists symbols'. psi] and [symbols'] are the symbols in
    [phi] that do not occur in [symbols].
 *)
val integer_hull_by_recession_cone :
  'a Syntax.context -> 'a Syntax.formula -> Syntax.symbol list -> DD.closed DD.t

(** [integer_hull_by_cooper srk phi symbols = (P, L)] is such that
    the intersection of [P] and [L] is the set of points satisfying
    [phi].
    The algorithm works by iteratively sampling a model and abstracting it
    to a disjunct of Cooper's elimination.
 *)
val integer_hull_by_cooper :
  'a Syntax.context -> 'a Syntax.formula -> Syntax.symbol list ->
  DD.closed DD.t * IntLattice.t

val integer_hull_standard :
  'a Syntax.context -> 'a Syntax.formula -> Syntax.symbol list -> DD.closed DD.t
