(** This module handles conversion between LIRA vectors, vectors in original
    variables, and LIRA terms and formulas. It also implements operations on
    LIRA vectors and formulas.

    - A LIRA term is a term in the FOL with equality over 
      (QQ; +, scalar multiplication, floor(-); >, >=, Int(-)).

    - A LIRA vector is a vector where each coordinate corresponds to an
      integer-valued variable or a real-valued fractional variable 
      (i.e., 0 <= x < 1).
      When coordinates mean coefficients, it represents a term
      [sum_i a_i (x_int)_i + sum_j b_j (x_frac)_j] that is linear in
      integer and fractional variables.

      A LIRA vector exists in the context of a [dimension_binding] ("context")
      mapping "original" variables [x] in LIRA terms/formulas to an 
      integer-valued variable [x_int] and a fractional-valued variable [x_frac] 
      in the LIRA vector.
      The context corresponds to constraints between [x] and the integer-fractional
      counterparts: for each original variable [x], 
      [x = x_int + x_frac /\ 0 <= x_frac < 1 /\ Int(x_int)].

      LIRA vectors represent only a subset of LIRA terms: those that are linear
      in floor(v) and frac(v) (= v - floor(v)), for variables v.
      Nevertheless, any LIRA term is semantically equal to a LIRA vector (the
      linear term it represents) modulo some conditions, which can be expressed
      as a formula over LIRA vectors (that we call a [linear_formula] below).

    - A [linear_formula] is a conjunction of inequalities and integrality
      constraints in (terms represented by) LIRA vectors.
 *)

(** A context that associates each original variable with an integer-valued 
    variable and a fractional-valued variable.
 *)
type dimension_binding

(** A linear formula is a conjunction of (positive) inequalities and
    integrality constraints over LIRA vectors.
    Integrality constraints are "pure", i.e., in integer-valued variables only.
 *)
type linear_formula =
  {
    inequalities: (Polyhedron.constraint_kind * Linear.QQVector.t) list
  ; integral: Linear.QQVector.t list
  }

val to_formula: 'a Syntax.context -> linear_formula -> 'a Syntax.formula list

(** Compute (P, L), where [P] consists of [0 <= x_frac < 1] for each [x_frac]
    in [dimension_binding], and [L] consists of [Int(x_int)] for each
    [x_int] in [dimension_binding].
 *)
val context_constraints: dimension_binding -> linear_formula

val fold: ('a -> original_dim:int -> int_dim:int -> frac_dim:int -> 'a) ->
          dimension_binding -> 'a -> 'a

(** [mk_lira_context srk phi] create a LIRA context that associates a 
    fresh integer-valued variable and a fresh fractional-valued variable with 
    each variable that occurs free in [phi], and adds these variables to [srk].    
 *)
val mk_lira_context: 'a Syntax.context -> 'a Syntax.formula -> dimension_binding

(** [add srk x t] adds a fresh integer symbol [x_int] and a fresh fractional
    symbol [x_frac] to the context if [x] is not already in [t], and binds
    (the dimension corresponding to) [x] to these symbols (corresponding
    dimensions). [srk] is extended with these symbols.
 *)
val add_binding: 'a Syntax.context -> Syntax.symbol -> dimension_binding -> dimension_binding

val int_frac_dim_of: int -> dimension_binding -> int * int

(** Convert a vector representing a term over original variables to a LIRA
    vector representing a term over integer and fractional variables,
    where the map between original and integer-fractional variables
    is per [dimension_binding].
 *)
val to_int_frac: dimension_binding -> Linear.QQVector.t -> Linear.QQVector.t

(** Convert a LIRA vector over integer and fractional variables to a vector
    representing the same term over original and integer variables.
 *)
val to_int_and_floor: dimension_binding -> Linear.QQVector.t -> Linear.QQVector.t

(** Given a LIRA vector [t] under LIRA context [binding],
    and a valuation [m] that has been extended to assign integer and fractional
    variables,
    [floor binding m t = (phi, t')] where [m |= phi] and [phi |= floor(t) = t'].
 *)
val floor:
  dimension_binding -> (int -> QQ.t) -> Linear.QQVector.t ->
  linear_formula * Linear.QQVector.t

(** Given a LIRA vector [t] under LIRA context [binding],
    and a valuation [m] that has been extended to assign integer and fractional
    variables,
    [ceiling binding m t = (phi, t')] where [m |= phi] and [phi |= ceiling(t) = t'].
 *)
val ceiling:
  dimension_binding -> (int -> QQ.t) -> Linear.QQVector.t ->
  linear_formula * Linear.QQVector.t

(** Given an [implicant] in the language of LIRA computed by 
    [Interpretation.select_implicant],
    and [binding] that contains all variables in [implicant] in its support
    (for original variables),
    [lira_implicant srk binding interp implicant = (P, L)] where
    - All variables in [P] are among the integer and fractional variables 
      in [binding].
    - All variables in [L] are integer-valued.
    - ext(interp) |= P /\ L, where [ext(interp)] is the extension of [interp]
      to [x_int] and [x_frac] variables according to the expected semantics.
    - [P /\ L |= phi] modulo LIRA, equalities [x] = [x_int] + [x_frac], 
      integrality constraints for [x_int], and bound constraints for [x_frac],
      for each variable x that occur in [binding].
 *)
val lira_implicant_of_implicant:
  'a Syntax.context -> dimension_binding -> 'a Interpretation.interpretation ->
  'a Syntax.formula list -> linear_formula

val local_project:
  'a Syntax.context -> dimension_binding -> (int -> Q.t) ->
  eliminate_original:int list -> Polyhedron.t -> IntLattice.t -> Polyhedron.t
