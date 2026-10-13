; A recursive function definition.  Until 2026-09-06 every run never
; ended: Evaluator.eval_term folded both branches of the body's ite before its condition, so
; ev 4 unfolded through the branch not taken forever.  Expected: sat (ev 4 holds), on every
; path (printer_smt2, pcsat_tbq_ar -p pcsp, z3_smt -p smt).
(set-logic ALL)
(define-fun-rec ev ((n Int)) Bool (ite (<= n 0) (= n 0) (ev (- n 2))))
(assert (ev 4))
(check-sat)
