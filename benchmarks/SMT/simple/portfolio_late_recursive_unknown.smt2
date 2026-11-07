; The first check is decided. Later recursive context lacks a verified model
; certificate in the Z3 backend, so each portfolio stage must see that check.
(set-logic ALL)
(check-sat)
(define-fun-rec f ((x Int)) Int (+ (f (+ x 1)) 1))
(assert true)
(check-sat)
