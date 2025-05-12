(set-logic ALL)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(push 1)
  (assert (= (+ 2 6) 8))
  (check-sat) ; sat
(pop 1)

(push 1)
  (assert (<= (+ 3 5) (+ 16 (- 9))))
  (check-sat) ; unsat
(pop 1)

(push 1)
  (assert (>= (+ 3 5) (+ 16 (- 9))))
  (check-sat) ; sat
(pop 1)

(push 1)
  (assert (= x 4))
  (assert (= y 3))
  (assert (= z 2))
  (assert (= (+ (* 2 x) (* 3 y) (* 5 z)) 27))
  (check-sat) ; sat
(pop 1)

(push 1)
  (assert (forall ((x Int) (y Int)) (= (+ x y) (+ y x))))
  (check-sat) ; sat
(pop 1)

(push 1)
  (assert (forall ((x Int) (y Int) (z Int)) (= (+ x y z) (+ x (+ y z)))))
  (check-sat) ; sat
(pop 1)

(push 1)
  (assert (forall ((x Int) (y Int) (z Int)) (=> (and (>= (+ (* 2 x) (* 3 y) (* 4 z)) 43) (<= y 3) (<= z 5)) (>= x 7))))
  (check-sat) ; sat
(pop 1)

(push 1)
  (assert (forall ((x Int) (y Int) (z Int)) (=> (and (>= (+ (* 2 x) (* 3 y) (* 4 z)) 40) (<= y 3) (<= z 5)) (>= x 7))))
  (check-sat) ; unsat
(pop 1)

(push 1)
  (assert (forall ((x Int) (y Int)) (=> (= x y) (not (distinct x y)))))
  (assert (forall ((x Int) (y Int)) (=> (distinct x y) (not (= x y)))))
  (assert (forall ((x Int) (y Int)) (=> (<= x y) (not (> x y)))))
  (assert (forall ((x Int) (y Int)) (=> (< x y) (not (>= x y)))))
  (assert (forall ((x Int) (y Int)) (=> (>= x y) (not (< x y)))))
  (assert (forall ((x Int) (y Int)) (=> (> x y) (not (<= x y)))))
  (check-sat) ; sat
(pop 1)
