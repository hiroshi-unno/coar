; An uninterpreted function constrained at two points and by a quantified
; frame, with a constant read through it.  Satisfiable; the model printed by
; -p smt gives the function's interpretation (its table and default) rather
; than a don't-care mark.
(set-logic ALL)
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Bool)
(declare-const c Int)
(assert (= (f 1) 10))
(assert (= (f 2) 20))
(assert (forall ((x Int)) (=> (> x 5) (= (f x) 0))))
(assert (= c (f 2)))
(assert (forall ((x Int) (y Int)) (= (g x y) (< x y))))
(check-sat)
