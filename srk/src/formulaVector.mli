(** These should eventually go to [linear.ml] and [abstract.ml]. *)

(** A binding consists a map that interprets symbols as dimensions and a map
    that interprets dimensions as symbols and terms.
*)
type 'a binding

(**
    Preconditions:
    - [symbol_of_dim] and [term_of_adjoined_dim] need to be consistent on
      the intersection of their domains, in that
      [mk_const (symbol_of_dim dim) = term_of_adjoined_dim dim] for all [dim]
      in the intersection of domains.
    - [symbol_of_dim (dim_of_symbol s) = s] for all symbols [s]
    - [free_dims_start] is any dimension larger than the dimensions
      that occur in:
      - The domain of [symbol_of_dim]; strictly, any dimension larger than the
        dimension of a symbol that can occur in a formula for
        conversion or abstraction, and larger than the dimension of a symbol
        that occurs in a term in the image of [term_of_adjoined_dim].
      - The domain of [term_of_adjoined_dim].
 *)
val mk_binding:
  'a Syntax.context ->
  (int -> Syntax.symbol option) ->
  ?term_of_adjoined_dim: 'a Syntax.arith_term SrkUtil.Int.Map.t ->
  (Syntax.symbol -> int) ->
  free_dims_start: int -> 'a binding

(** Add dimensions to linearize mod terms, i.e., terms of the form [t mod r]
    for a term t and a constant rational r, in the formula.
 *)
val add_mod_term_dimensions:
  'a Syntax.context -> 'a binding -> 'a Syntax.formula -> 'a binding

(** Given [srk], [terms], and [phi],
    a standard binding places [terms] in the dimensions 0 through
    length(terms) (exclusive), followed by the image of symbols in [phi]
    under [Syntax.int_of_symbol], followed by quotient and remainder
    dimensions for mod terms in [phi] (terms of the form [t % r] for
    constant rational r and term t); there is one for each such term.
 *)
val mk_standard_binding:
  'a Syntax.context -> ?translate_mod_terms:bool ->
  ?project_onto:'a Syntax.arith_term array ->
  'a Syntax.formula -> 'a binding

val mod_term_dimensions: 'a binding -> int list

val pp_symbol_to_dimension:
  'a Syntax.context -> Syntax.Symbol.Set.t -> Format.formatter -> 'a binding -> unit

val formula_of_dd:
  'a Syntax.context -> 'a binding -> DD.closed DD.t -> 'a Syntax.formula

val formula_of_polyhedron:
  'a Syntax.context -> 'a binding -> Polyhedron.t -> 'a Syntax.formula

val formula_of_lattice:
  'a Syntax.context -> 'a binding -> IntLattice.t -> 'a Syntax.formula

val formula_of_point:
  'a Syntax.context -> 'a binding -> Linear.QQVector.t -> 'a Syntax.formula

val formula_of_model:
  'a Syntax.context -> 'a binding -> SrkUtil.Int.Set.t -> (int -> QQ.t) -> 'a Syntax.formula

val ambient_dim: (Polyhedron.t * IntLattice.t) list -> except:int list -> int

val collect_dimensions_from_constraints:
  ('a -> Linear.QQVector.t) -> 'a BatEnum.t -> SrkUtil.Int.Set.t

val collect_dimensions: (Polyhedron.t * IntLattice.t) -> SrkUtil.Int.Set.t

(** Lift a local abstraction procedure for a polyhedron-lattice pair into an
      local abstraction procedure for a formula.
      All symbols in the formula must be in the domain of [dim_of_symbol]
      in [binding], and the space of dimensions in [binding] has to contain
      dimensions corresponding to mod terms in the formula.
 *)
val abstract_implicant:
  'a Syntax.context -> 'a binding ->
  [ `ImplicantOnly of ((int -> QQ.t) -> Polyhedron.t * IntLattice.t -> 'b)
  | `WithTerms of
      term_defs: (Polyhedron.constraint_kind * Linear.QQVector.t) list ->
      dimensions_in_terms: SrkUtil.Int.Set.t ->
      (int -> QQ.t) -> (Polyhedron.t * IntLattice.t) -> 'b
  ] ->
  'a Syntax.formula ->
  [> `LIRA of 'a Interpretation.interpretation ] -> 'b
