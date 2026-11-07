; An Int-valued and a Bool-valued synth-fun in one problem: the solution has
; one define-fun of each sort.  g(a) = 2a + 3, p(a, c) = c /\ a > 1.
(set-logic LIA)
(synth-fun g ((a Int)) Int)
(synth-fun p ((a Int) (c Bool)) Bool)
(declare-var x Int)
(declare-var u Bool)
(constraint (= (g x) (+ (* 2 x) 3)))
(constraint (= (p x u) (and u (> x 1))))
(check-synth)
