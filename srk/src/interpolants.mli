module Interpolator : sig 
  val interpolant : 'a Syntax.context -> 'a Syntax.arith_term list -> int ->
'a CoordinateSystem.t -> Polyhedron.t list -> Polyhedron.t list -> 'a Syntax.formula option
  val to_lists: (Syntax.symbol -> bool) -> 'a Syntax.context -> 'a Syntax.formula -> 'a Syntax.formula -> ((Polyhedron.t list * Polyhedron.t list)* 'a CoordinateSystem.t)
end
