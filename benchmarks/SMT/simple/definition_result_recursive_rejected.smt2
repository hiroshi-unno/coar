; An ill-sorted definition must be refused before any verdict.
(set-logic ALL)
(define-fun-rec bad () Int true)
(assert true)
(check-sat)
