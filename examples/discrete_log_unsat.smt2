(set-logic ALL)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (+ (exp 2 x) (* 17 y)) 5))

(check-sat)
