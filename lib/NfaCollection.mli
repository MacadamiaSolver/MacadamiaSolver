module Add : sig
  val add : lhs:'var -> rhs:'var -> sum:'var -> 'var Nfa.dfa
end

module Eq : sig
  val eq : 'var -> 'var -> 'var Nfa.dfa

  val eq_const : 'var -> int -> 'var Nfa.dfa
end

module Neutral : sig
  val n : unit -> 'a Nfa.dfa

  val z : unit -> 'a Nfa.dfa
end

val leq : 'var -> 'var -> 'var Nfa.dfa

val geq : 'var -> 'var -> 'var Nfa.dfa
