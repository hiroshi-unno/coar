(set-option :interactive-mode true) ; enable (get-assertions) command
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (>= x 0))
(assert (distinct x 0))
(assert (= y (+ x 1)))
(assert (not (or (>= y 2) (> y 1))))
(check-sat)
(exit)
