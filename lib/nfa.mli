module Map = Base.Map.Poly
module Set = Base.Set.Poly

type state = int

type bit = Bits.bit

type deg = int

type t

val create_nfa :
     transitions:(state * int * state) list
  -> start:state list
  -> final:state list
  -> vars:int list
  -> deg:int
  -> t

val run_nfa : t -> bool

val intersect : t -> t -> t

val unite : t -> t -> t

val project : int list -> t -> t

val truncate : int -> t -> t

val is_graph : t -> bool

val invert : t -> t

val format_nfa : Format.formatter -> t -> unit
