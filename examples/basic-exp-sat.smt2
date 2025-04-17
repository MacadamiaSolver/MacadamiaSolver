; sat: x = 8, y = 3
(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (>= y 0))
(assert (= x (exp 2 y)))
(assert (> x 4))

(check-sat)
(get-model)
