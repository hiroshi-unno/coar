; A non-recursive function stated by a quantified defining equation.  The question is satisfiable
; (f is the function the equation defines), and Z3 4.13.3, 4.15.2 and 5.1.0 do not return in 10 s.
; Z3interface.without_unreached_explicit drops such a definition when the question does not reach it.
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((a Int)) (= (f a) (ite (> a 0) a 0))))
(check-sat)
