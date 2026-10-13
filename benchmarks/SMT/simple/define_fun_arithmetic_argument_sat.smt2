; expected: sat
;
; The argument is an expression rather than a single literal, which is the case
; that refuted the first repair: in `(+ 2 1)` the addition and each literal carry
; a DIFFERENT sort variable, so substituting the argument's own top-level one
; settles nothing inside it. The argument is inferred against the formal instead,
; which is the type checker's job rather than the caller's.
(set-logic ALL)
(define-fun f ((n Int)) Int (+ n 1))
(assert (and (= (f (+ 2 1)) 4) (= (f (- 5 3)) 3)))
(check-sat)
