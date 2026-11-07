(set-logic ALL)
(define-fun-rec f ((s (Seq Int))) Int (+ (f s) 1))
(assert true)
(check-sat)
