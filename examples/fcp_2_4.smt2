(set-info :smt-lib-version 2.6)
(set-logic LIA)
(set-info :source |

Based on the FCP benchmarks by Vojtěch Havlena, Michal Hečko, Lukáš Holík, Ondřej Lengál licensed under CC 4.0
See README for more information.

Instances of the Frobenius coin problem with two coins involving multiple
quantifier alternations that seem difficult for modern SMT solvers.
|)
(set-info :category "crafted")
(set-info :status sat)

(declare-fun P () Int)
(assert (and (<= 0 P) (forall ((x0 Int) (x1 Int)) (=> (and (<= 0 x0) (<= 0 x1)) (not (= (+ (* x0 2) (* x1 4)) P)))) (forall ((R Int)) (=> (forall ((x0 Int) (x1 Int)) (=> (and (<= 0 x0) (<= 0 x1)) (not (= (+ (* x0 2) (* x1 4)) R)))) (<= R P)))))
(check-sat)
(exit)
