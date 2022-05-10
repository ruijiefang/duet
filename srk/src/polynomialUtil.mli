(** Some utility functions for polynomials *)

open Polynomial

module PrettyPrint : sig

  val pp_ascii_dim : Format.formatter -> int -> unit

  val pp_numeric_dim : string -> Format.formatter -> int -> unit

  val pp_qq_matrix : Format.formatter -> QQ.t list list -> unit

  val pp_zz_matrix : Format.formatter -> ZZ.t list list -> unit

  val pp_poly_list : (Format.formatter -> int -> unit)
    -> Format.formatter -> QQXs.t list -> unit

end

(* module MonomialMap = BatMap.Make(Monomial) *)

(** A polynomial-vector context is a bijective map between a set of monomials
    and the dimensions of the vector space spanned by that set of monomials.
*)
module PolyVectorContext : sig

  type t

  module MonomialMap : BatMap.S

  (** Raised when a monomial-dimension association cannot be found *)
  exception Not_in_context

  (** Monomials are assigned dimensions (integer indices) according to the
      monomial order given, with smallest dimension given to the smallest monomial
      if [increasing] is true, and smallest dimension given to the largest monomial
      if [increasing] is false. Monomials in the list do not have to be unique.
  *)
  val context: ?increasing:bool
    -> (Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt ])
    -> Monomial.t list -> t

  val mk_context: ?increasing:bool
    -> (Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt ])
    -> QQXs.t list -> t

  val get_mono_map: t -> int MonomialMap.t

  val dim_of : Monomial.t -> t -> Monomial.dim

  val monomial_of : Monomial.dim -> t -> Monomial.t

  val num_dimensions : t -> int

  (** Maximum variable that appears in some monomial in the context *)
  val max_variable : t -> int option

  val enum_by_dimension : t -> (Monomial.dim * Monomial.t) BatEnum.t

  val enum_by_monomial : t -> (Monomial.t * Monomial.dim) BatEnum.t

  val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit

  (*
  val reorder : t
    -> ?increasing: bool
    -> (Monomial.t -> Monomial.t -> [`Eq | `Lt | `Gt ])
    -> t
  *)

end with module MonomialMap = BatMap.Make(Monomial)

module PolyVectorConversion : sig

  (** Project polynomial into the vector space spanned by monomials in the context *)
  val poly_to_vector : PolyVectorContext.t -> QQXs.t -> Linear.QQVector.t

  (** Recover polynomial from its representation as a vector in the context *)
  val vector_to_poly : PolyVectorContext.t -> Linear.QQVector.t -> QQXs.t

end