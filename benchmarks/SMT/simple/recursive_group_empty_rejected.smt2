; The names of a define-funs-rec group must be nonempty, distinct and not already defined.
(set-logic ALL)
(define-funs-rec () ())
(assert true)
(check-sat)
