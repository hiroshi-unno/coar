; The declared measure is not decreased (the call repeats its argument), and
; the defining equation f x = f x + 1 has no solution, so the context is
; inconsistent: a sat answer would be wrong.
(set-logic ALL)
(define-fun-rec f ((x Int)) Int (! (+ (f x) 1) :decreases x))
(assert (forall ((x Int)) (>= (f x) 0)))
(check-sat)
