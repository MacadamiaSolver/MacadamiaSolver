; this is bad for our prover: the base is not 2
(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)

(assert (= 9 (exp 3 x)))

(check-sat)
(get-model)
