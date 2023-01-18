(set-option :interactive-mode true) ; enable (get-assertions) command
(set-logic QF_LIA)
(declare-fun w () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (> x y))
(assert (> y z))
(assert (= x w))
(check-sat)
(exit)
