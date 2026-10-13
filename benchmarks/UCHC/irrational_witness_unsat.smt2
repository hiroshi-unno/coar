; Satisfiability over the rationals does not transfer to the reals, with unknowns only.
; Q and R are both models of the one
; complete theory of linear real arithmetic, and Q is its prime model.
;
;   NotInt(x)          <=  0 < x < 1
;   NotInt(x+1)        <=  NotInt(x)
;   NotInt(x-1)        <=  NotInt(x)
;   Neq(0, y, m)       <=  m != 0
;   Neq(n+1, y, m+y)   <=  Neq(n, y, m)
;   Z(n, m, y)         <=  NotInt(n)
;   Z(n, m, y)         <=  NotInt(m)
;   Z(n, m, y)         <=  Neq(n, y, m)
;   false              <=  forall n m. n >= 1 => Z(n, m, y)
;
; In an Archimedean model the least solution of NotInt is the non-integers, and Neq(n, y, m) holds for
; a natural number n exactly when m != n*y.  So the goal's premise at y says: for all integers n >= 1
; and m, m != n*y, i.e. y is irrational.
;
; Over Q the system is SATISFIABLE (no element is irrational; the least solution meets the goal).
; Over R it is UNSATISFIABLE (the goal fires at y = sqrt(2)).
;
; So the verdicts are: standard (Q) sat; standard (R) unsat; some model sat; every model (this
; repository's per-model definition for kind-free problems) unsat.  expected: unsat.
;
; No sound procedure can answer unsat: Q is a model with a solution, so no finite refutation exists.
; No solution exists in R, so a sat is wrong.  "No answer" is the correct behaviour.
(set-logic HORN)
(declare-fun NotInt (Real) Bool)
(declare-fun Neq (Real Real Real) Bool)
(declare-fun Z (Real Real Real) Bool)
(assert (forall ((x Real)) (=> (and (< 0.0 x) (< x 1.0)) (NotInt x))))
(assert (forall ((x Real)) (=> (NotInt x) (NotInt (+ x 1.0)))))
(assert (forall ((x Real)) (=> (NotInt x) (NotInt (- x 1.0)))))
(assert (forall ((y Real) (m Real)) (=> (not (= m 0.0)) (Neq 0.0 y m))))
(assert (forall ((n Real) (y Real) (m Real))
  (=> (Neq n y m) (Neq (+ n 1.0) y (+ m y)))))
(assert (forall ((n Real) (m Real) (y Real)) (=> (NotInt n) (Z n m y))))
(assert (forall ((n Real) (m Real) (y Real)) (=> (NotInt m) (Z n m y))))
(assert (forall ((n Real) (m Real) (y Real)) (=> (Neq n y m) (Z n m y))))
(assert (forall ((y Real))
  (=> (forall ((n Real) (m Real)) (=> (>= n 1.0) (Z n m y)))
      false)))
(check-sat)
