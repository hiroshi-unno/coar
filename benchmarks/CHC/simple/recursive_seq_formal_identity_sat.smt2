(set-logic ALL)
(define-fun-rec f ((s (Seq Int))) Int (f s))
(assert true)
(check-sat)
