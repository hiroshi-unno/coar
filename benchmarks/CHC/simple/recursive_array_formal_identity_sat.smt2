(set-logic HORN)
(define-fun-rec g ((m (Array Int Int))) Int (g m))
(assert true)
(check-sat)
