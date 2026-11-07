; F is functional, so total: every array a has some y with F(a, y).  G carries
; (a, y) through one step, after which y must equal both a[0] and a[1].  An
; array with a[0] /= a[1] admits no such y, so no functional F exists: unsat.
;
; Under the cell abstraction (clauses.cell_abstraction > 0) the array argument
; of F is replaced by (index, value) cells.  The abstracted system has the
; solution F#(j, v, y) := y = v, G#(j, v, y, n) := y = v, whose concretization
; F(a, y) := forall j. y = a[j] is empty at every non-constant array, so it is
; not total and is no solution of this problem.  A kinded unknown must not be
; abstracted, and the answer under that configuration must never be sat.
(declare-fnp F ((Array Int Int) Int) Bool)
(declare-fun G ((Array Int Int) Int Int) Bool)
(assert (forall ((a (Array Int Int)) (y Int)) (=> (F a y) (G a y 0))))
(assert (forall ((a (Array Int Int)) (y Int) (n Int))
  (=> (and (G a y n) (< n 1)) (G a y (+ n 1)))))
(assert (forall ((a (Array Int Int)) (y Int) (n Int))
  (=> (and (G a y n) (= n 1)) (and (= y (select a 0)) (= y (select a 1))))))
(check-sat)
