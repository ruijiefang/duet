open Syntax

type t = PolynomialCone.t

val abstract : 'a Abstract.Solver.t -> ?bottom:t -> 'a arith_term array -> t
