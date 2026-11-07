; Every check is answered, in order, on what is in scope at it: z3 5.1.0 and cvc5 1.4.2
; (--incremental) print sat, unsat, unsat, sat.  The second check sees the pushed x < 0, the third
; the assumptions, which are gone by the fourth.
(set-logic ALL)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
(push 1)
(assert (< x 0))
(check-sat)
(pop 1)
(declare-fun y () Int)
(check-sat-assuming ((= x y) (< y 0)))
(assert (= x 3))
(check-sat)
