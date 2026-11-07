(set-logic HORN)
(define-fun-rec g ((m (Array Int Int))) Int (+ (g m) 1))
(assert true)
(check-sat)
