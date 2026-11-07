; A let whose definition is built from numerals alone, (ite K 0 1), read by the definition of a second let nested in
; it.  Before type inference the outer binder's sort is still a sort variable while its occurrence under the
; subtraction is already Int; a renaming of let binders that told the two apart by sort renamed the binder and left
; the occurrence as a free, universally quantified variable, which made this satisfiable system unsat.
; With K true, p = 0 and so x = 0, which the query clause asks for.  Expected: sat (z3 sat).
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (inv x) (= x 0))))
(assert (forall ((K Bool) (x Int))
  (let ((p (ite K 0 1)))
    (let ((q (- x p)))
      (=> (and (= q 0) K) (inv x))))))
(check-sat)
(exit)
