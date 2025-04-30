(set-logic ALL)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (= (exp 2 x) y))
(assert (= (exp 2 y) z))
(assert (>= z 16))
(assert (forall ((k Int)) (not (= (+ z (* 10 k)) 6))))

(check-sat)
