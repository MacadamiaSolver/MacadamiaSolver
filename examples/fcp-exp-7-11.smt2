(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status sat)

(declare-fun P () Int)
(declare-fun x () Int)
; P = 59 (answer to Frobenius coin problem with 7 11), 2^x - 5 = 59, x = 8
(assert (= (+ 5 P) (exp 2 x)))
(assert (and (<= 0 P) (forall ((x0 Int) (x1 Int)) (=> (and (<= 0 x0) (<= 0 x1)) (not (= (+ (* x0 7) (* x1 11)) P)))) (forall ((R Int)) (=> (forall ((x0 Int) (x1 Int)) (=> (and (<= 0 x0) (<= 0 x1)) (not (= (+ (* x0 7) (* x1 11)) R)))) (<= R P)))))
(check-sat)
(exit)
