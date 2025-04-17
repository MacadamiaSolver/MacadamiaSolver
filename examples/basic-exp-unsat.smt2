; sat with partial semantics: x = -1
(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun e2 () Int)
(declare-fun e3 () Int)

(assert (= e2 (exp 2 x)))
(assert (= e3 (exp 3 x)))
(assert (> e2 e3))

(check-sat)
(get-model)
