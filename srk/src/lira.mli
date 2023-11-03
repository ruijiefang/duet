
(** LIRA vectors are LIRA terms that are linear in floor(x) and fractional(x),
    where x ranges over symbols/variables. LIRA vectors have to exist within
    a common LIRA context that contains all dimensions corresponding to symbols
    (by default, via [Syntax.int_of_symbol]).

    TODO: Say something about the relationship between dimensions of symbols
    and dimensions of LIRA vectors.
 *)

type lira_context

(** Add a dimension corrresponding to a symbol. *)
val add_dimension: int -> lira_context -> lira_context

(** Given a [ctx] that contains {int_of_symbol(x): x in symbols(term)},
    and an interpretation [interp],
    [linearize_term srk ctx int_of_symbol interp term = (phi, v)], where
    [interp |= phi |= term = v], where entailments are modulo LIRA and [v]
    is the representation of a LIRA term.
 *)
val linearize:
  'a Syntax.context -> lira_context ->
  ?int_of_symbol: (Syntax.symbol -> int) ->
  'a Interpretation.interpretation -> 'a Syntax.arith_term ->
  (Polyhedron.t * IntLattice.t) * Linear.QQVector.t

(** Given a conjunctive formula [implicant] in the language of LIRA,
    a [ctx] that contains {int_of_symbol(x): x in symbols(implicant)},
    and an interpretation [interp] that satisfies [implicant],
    [lira_implicant srk ctx interp implicant = (p, l)] where (p, l) represents
    a formula such that [interp |= (p, l) |= implicant].
 *)
val lira_implicant_of_implicant:
  'a Syntax.context -> lira_context ->
  ?int_of_symbol:(Syntax.symbol -> int) -> 'a Interpretation.interpretation ->
  'a Syntax.formula list -> Polyhedron.t * IntLattice.t

val local_project:
  'a Syntax.context -> lira_context -> 'a Interpretation.interpretation ->
  onto_original:int list -> Polyhedron.t * IntLattice.t ->
  DD.closed DD.t * IntLattice.t

val project:
  'a Syntax.context -> 'a Syntax.formula -> ('a Syntax.arith_term) array ->
  DD.closed DD.t * IntLattice.t
