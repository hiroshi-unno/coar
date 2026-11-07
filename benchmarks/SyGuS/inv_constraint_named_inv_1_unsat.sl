; The invariant itself is named like a generated variable.  x counts up from
; 0, so no invariant implies x <= 0: infeasible.
(set-logic LIA)
(synth-inv INV_1 ((x Int)))
(define-fun pre ((x Int)) Bool (= x 0))
(define-fun trans ((x Int) (xp Int)) Bool (= xp (+ x 1)))
(define-fun post ((x Int)) Bool (<= x 0))
(inv-constraint INV_1 pre trans post)
(check-synth)
