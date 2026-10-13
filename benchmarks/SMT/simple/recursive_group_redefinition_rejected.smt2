; The names of a define-funs-rec group must be nonempty, distinct and not already defined.
(set-logic ALL)
(define-fun f () Bool true)
(define-funs-rec ((f () Bool)) (false))
(assert f)
(check-sat)
