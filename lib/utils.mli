module Map = Base.Map.Poly

val option_map_to_map_option : ('a, 'b option) Map.t -> ('a, 'b) Map.t option
