; An ill-sorted definition must be refused before any verdict.
(set-logic ALL)
(define-fun bad () Int true)
(assert true)
(check-sat)
