type varpos = int

val add : lhs:varpos -> rhs:varpos -> sum:varpos -> Nfa.t
val eq : varpos -> varpos -> Nfa.t
val eq_const : varpos -> int -> Nfa.t
val n : unit -> Nfa.t
val z : unit -> Nfa.t
val leq : varpos -> varpos -> Nfa.t
val geq : varpos -> varpos -> Nfa.t
val geq_zero : varpos -> Nfa.t
val minus : varpos -> varpos -> Nfa.t
val lt : varpos -> varpos -> Nfa.t
val gt : varpos -> varpos -> Nfa.t
val torename : varpos -> int -> int -> Nfa.t
val torename2 : int -> int -> Nfa.t
val power_of_two : int -> Nfa.t
val mul : res:varpos -> lhs:int -> rhs:varpos -> Nfa.t
