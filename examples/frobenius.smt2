(set-info :smt-lib-version 2.6)
(set-info :status sat)
(assert
  (forall ((x Int)) (or 
  (exists ((y Int) (z Int)) (= x (+ (* 5 y) (* 7 z)))) 
  (<= x 22)))
)
(check-sat)
(exit)
