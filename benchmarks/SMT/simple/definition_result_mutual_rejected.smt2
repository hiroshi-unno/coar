; An ill-sorted definition must be refused before any verdict.
(set-logic ALL)
(define-funs-rec ((bad () Int)) (true))
(assert true)
(check-sat)
