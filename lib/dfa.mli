module Map = Base.Map.Poly

type bit = Bits.bit

type 'varname dfa

val create :
     transitions:('s * ('var, bit) Map.t * 's) list
  -> start:'s
  -> final:'s list
  -> 'var dfa

val run : 'v dfa -> ('v, bit) Map.t list -> bool

val intersect : 'v dfa -> 'v dfa -> 'v dfa

val union : 'v dfa -> 'v dfa -> 'v dfa

val project : ('v -> bool) -> 'v dfa -> 'v dfa

val invert : 'v dfa -> 'v dfa

val minimize : 'v dfa -> 'v dfa

val remove_unreachable : 'v dfa -> 'v dfa

val map_varname : ('a -> 'b) -> 'a dfa -> 'b dfa

val format :
  (Format.formatter -> 'v -> unit) -> Format.formatter -> 'v dfa -> unit

val is_graph : 'v dfa -> bool
