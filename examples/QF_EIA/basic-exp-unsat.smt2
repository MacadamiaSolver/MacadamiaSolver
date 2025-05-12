; unsat
(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)

(assert (> x (exp 2 x)))

(check-sat)
