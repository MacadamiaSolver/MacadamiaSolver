module Map = Base.Map.Poly

type bit = Bits.bit

type 'varname nfa

val create_nfa :
     transitions:('s * ('var, bit) Map.t * 's) list
  -> start:'s list
  -> final:'s list
  -> 'var nfa

val run_nfa : 'v nfa -> ('v, bit) Map.t list -> bool

val map_varname : ('a -> 'b) -> 'a nfa -> 'b nfa

val remove_unreachable : 'v nfa -> 'v nfa

val intersect : 'v nfa -> 'v nfa -> 'v nfa

val unite : 'v nfa -> 'v nfa -> 'v nfa

val project : ('v -> bool) -> 'v nfa -> 'v nfa

val format_nfa :
  (Format.formatter -> 'v -> unit) -> Format.formatter -> 'v nfa -> unit

type 'varname dfa

type ('state, 'varname) dfaCollisions =
  ('state * ('varname, bit) Map.t * ('varname, bit) Map.t * 'state * 'state)
  list

val create_dfa :
     transitions:('s * ('var, bit) Map.t * 's) list
  -> start:'s
  -> final:'s list
  -> ('var dfa, ('s, 'var) dfaCollisions) result

val run_dfa : 'v dfa -> ('v, bit) Map.t list -> bool

val to_nfa : 'v dfa -> 'v nfa

val to_dfa: 'v nfa -> 'v dfa

val invert: 'v dfa -> 'v dfa

val is_graph: 'v nfa -> bool
