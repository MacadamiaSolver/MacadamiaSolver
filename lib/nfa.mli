module Map = Base.Map.Poly

type bit = Bits.bit
type deg = int

type t

val create_nfa :
     transitions:('s * int * 's) list
  -> start:'s list
  -> final:'s list
  -> vars:int list
  -> deg:int
  -> t

val run_nfa : t -> bool

val remove_unreachable : t -> t

val intersect : t -> t -> t

val unite : t -> t -> t

val project : int list -> t -> t

val truncate : int -> t -> t

val format_nfa : Format.formatter -> t -> unit

type dfa

val to_nfa : dfa -> t

val to_dfa : t -> dfa

val invert : dfa -> dfa

val minimize : dfa -> dfa

val is_graph : t -> bool
