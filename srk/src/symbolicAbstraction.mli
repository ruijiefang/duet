
val convex_hull_by_recession_cone :
  'a Syntax.context -> 'a Syntax.formula -> Syntax.symbol list -> DD.closed DD.t

val convex_hull_by_cooper :
  'a Syntax.context -> 'a Syntax.formula -> Syntax.symbol list ->
  DD.closed DD.t * IntLattice.t
