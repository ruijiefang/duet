
val polyhedral_abs_by_mbp :
  'a Syntax.context -> 'a Syntax.formula -> Syntax.symbol list -> DD.closed DD.t


val polyhedral_lattice_abs_by_mbp :
  'a Syntax.context -> 'a Syntax.formula -> Syntax.symbol list ->
  DD.closed DD.t * IntLattice.t
