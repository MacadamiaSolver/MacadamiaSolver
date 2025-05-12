module Map = Base.Map.Poly

val dump : Ir.t -> string
val proof : Ir.t -> [ `Sat | `Unsat | `Unknown ]
val get_model : Ir.t -> (Ir.atom, int) Map.t option
