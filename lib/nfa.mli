module Map = Base.Map.Poly
module Set = Base.Set.Poly
module Sequence = Base.Sequence

type state = int
type deg = int
type t

val create_nfa
  :  transitions:(state * int * state) list
  -> start:state list
  -> final:state list
  -> vars:int list
  -> deg:int
  -> t

val create_dfa
  :  transitions:(state * int * state) list
  -> start:state
  -> final:state list
  -> vars:int list
  -> deg:int
  -> t

val run : t -> bool
val intersect : t -> t -> t
val unite : t -> t -> t
val project : int list -> t -> t
val truncate : int -> t -> t
val is_graph : t -> bool
val reenumerate : (int, int) Map.t -> t -> t
val minimize : t -> t
val invert : t -> t
val format_nfa : Format.formatter -> t -> unit
val remove_unreachable : t -> t
