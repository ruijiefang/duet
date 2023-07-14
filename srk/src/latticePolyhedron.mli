
(** [lattice_hull p l] computes the "integer" hull of [p] w.r.t. [l],
    where the generators of [l] are the generators of the integrality
    constraints, i.e., the dual lattice.
 *)
val lattice_hull : Polyhedron.t -> IntLattice.t -> Polyhedron.t

(** [local_project m ~eliminate (p, l) = (p', l')]:
    When [m] is a point in the intersection of [p] and [L], where [L] is the
    dual lattice of the constraint lattice [l],
    [m] is a point in the intersection of [p'] and [L'], where [L'] is the dual
    lattice of [l'].
    Moreover, [p' \cap L'] is a subset of [p \cap L].
    Considered as formulas, [constraints(p') /\ l' |= constraints(p) /\ l]
    in the theory of linear integer arithmetic.
 *)
val local_project:
  (int -> [`Int | `Frac]) -> (int -> QQ.t) -> eliminate:(int list) ->
  Polyhedron.t * IntLattice.t -> Polyhedron.t * IntLattice.t

