; The names of a define-funs-rec group must be nonempty, distinct and not already defined.
(set-logic ALL)
(define-fun old () Bool true)
(define-funs-rec ((f ((x Bool)) Bool) (g ((x Bool)) Bool)) ((g x) (and old x)))
(assert (f false))
(check-sat)
