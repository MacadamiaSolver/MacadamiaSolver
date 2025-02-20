type varpos = int

val add : lhs:varpos -> rhs:varpos -> sum:varpos -> Nfa.t
val eq : varpos -> varpos -> Nfa.t
val eq_const : varpos -> int -> Nfa.t
val n : unit -> Nfa.t
val z : unit -> Nfa.t
val leq : varpos -> varpos -> Nfa.t
val geq : varpos -> varpos -> Nfa.t
val lt : varpos -> varpos -> Nfa.t
val gt : varpos -> varpos -> Nfa.t
val torename : varpos -> int -> int -> Nfa.t
