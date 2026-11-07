; The unsat sibling of let_of_generic_numerals_read_by_inner_let_sat.smt2: without the guard K the outer let may be
; 1, so x = 1 reaches inv and the query clause fails.  The occurrence of p inside the inner let's definition must
; read p's definition here too.  Expected: unsat (z3 unsat).
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (inv x) (= x 0))))
(assert (forall ((K Bool) (x Int))
  (let ((p (ite K 0 1)))
    (let ((q (- x p)))
      (=> (= q 0) (inv x))))))
(check-sat)
(exit)
