(set-logic ALL)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)


(assert (>= (+ (* 2 x) (* 3 y) (* 4 z)) 40)
(check-sat) ; unsat
(get-model)
