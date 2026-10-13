; The names of a define-funs-rec group must be nonempty, distinct and not already defined.
(set-logic ALL)
(define-funs-rec ((f () Bool) (|f| () Bool)) (true false))
(assert f)
(check-sat)
