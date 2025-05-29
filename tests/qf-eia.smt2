(set-logic ALL)

(declare-const x Int)
(declare-const y Int)

(push 1)
  (assert (= (exp 2 x) 16))
  (check-sat)
(pop 1)

(push 1)
  (assert (= (+ (exp 2 x) 4) 16))
  (check-sat)
(pop 1)

(push 1)
  (assert (= (exp 2 x) (exp 2 y)))
  (check-sat)
(pop 1)

; (check-sat (= (exp 2 x) (exp 2 y))) ; sat
