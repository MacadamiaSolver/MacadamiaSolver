(set-info :smt-lib-version 2.6)
(set-logic LIA)

(assert
  (forall ((x Int))
    (exists ((y Int))
      (=> (>= x 0) (= y (+ x 1)))
    )
  )
)
(check-sat)
(exit)
