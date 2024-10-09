val add : lhs:'var -> rhs:'var -> sum:'var -> 'var Dfa.dfa

val eq : 'var -> 'var -> 'var Dfa.dfa

val eq_const : 'var -> int -> 'var Dfa.dfa

val any : unit -> 'a Dfa.dfa

val none : unit -> 'a Dfa.dfa
