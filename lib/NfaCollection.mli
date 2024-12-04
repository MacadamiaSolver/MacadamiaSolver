type varpos = int

type deg = int

val add : lhs:varpos -> rhs:varpos -> sum:varpos -> deg -> Nfa.t

val eq : varpos -> varpos -> deg -> Nfa.t

val eq_const : varpos -> int -> deg -> Nfa.t

val n : deg -> Nfa.t

val z : deg -> Nfa.t

val leq : varpos -> varpos -> deg -> Nfa.t

val geq : varpos -> varpos -> deg -> Nfa.t

val torename : varpos -> int -> int -> Nfa.t
