
(** A lattice is the ZZ-span of a finite set of QQ-vectors.
    When the set of generators is empty, the lattice is the zero lattice.
*)
type t

(** [hermitize generators] computes a basis B that is the
    row-Hermite normal form of [generators] considered as rows of a matrix.
    A vector is considered as a row in the matrix by ordering its dimensions
    with the smallest dimension (the constant dimension) on the right.
*)
val hermitize : Linear.QQVector.t list -> t

(** Obtain the basis of the lattice. The zero lattice has an empty basis. *)
val basis : t -> Linear.QQVector.t list

(** [member v t] = true iff v is a member of the lattice L. *)
val member : Linear.QQVector.t -> t -> bool

(** The highest dimension that appears in some generator, if the lattice is non-empty,
    and [Linear.const_dim] otherwise.
 *)
val max_dim : t -> Linear.QQVector.dim

(** [project p t] computes the projection of the lattice onto the dimensions
    marked true by [p].
*)
val project : (Linear.QQVector.dim -> bool) -> t -> t

(** [project_lower n t] computes the projection of the lattice onto the
    dimensions <= n. This is more efficient than [project].
*)
val project_lower : int -> t -> t

(** The zero lattice *)
val bottom : t

val sum : t -> t -> t

val intersect : t -> t -> t

val subset : t -> t -> bool

val equal : t -> t -> bool

val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit
