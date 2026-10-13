; QECHC but not QCHC: the negated universal atom
; beside an existential head makes I anti-monotone in R -- the only solution is I := not R --
; whereas every satisfiable QCHC-proper problem has a monotone solution.  So
; this solution set is no QCHC-proper problem's, over any carrier, finite or infinite.
; expected: sat
(set-logic DQHORN)
(declare-forall-fun R (Int) Bool)
(declare-dep-exists-fun I (R) (Int) Bool)
(assert (forall ((x Int)) (=> (not (R x)) (I x))))
(assert (forall ((x Int)) (=> (and (I x) (R x)) false)))
(check-sat)
