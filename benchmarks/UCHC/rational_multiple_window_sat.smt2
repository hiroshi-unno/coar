;; Expected sat (formerly named *_unsat). This repository's definition reads the
;; background theory as an SMT-LIB theory, whose models fix the standard structure (Int is the set of
;; all integers, Real the set of all reals), so this system is SATISFIABLE. Read over every model of
;; the FIRST-ORDER theory (non-standard models included), it is UNSATISFIABLE; that reading is what the
;; comments below were written for. expected: sat
; Standard satisfiability over the reals does not transfer to every model of linear real arithmetic,
; not even along an elementary extension of the reals, with unknowns only.
;
;   R(c, z, 0, 0)
;   R(c, z, n+1, d+z)  <=  R(c, z, n, d)
;   R(c, z, n, d-c)    <=  R(c, z, n, d)
;   L(c, z)            <=  R(c, z, n, 0) and n >= 1
;   false              <=  c > 0 and (forall z. 0 <= z <= c => L(c, z))
;
; In every model the least solution of R is {(c, z, n, n*z - m*c) : n, m standard natural numbers},
; because each derivation is finite, so L(c, z) holds exactly when z is a standard rational multiple
; of c.  The goal fires at c exactly when every element of [0, c] is such a multiple.
;
; Over R the system is SATISFIABLE: for c > 0 the element c/sqrt(2) of [0, c] is not a rational
; multiple of c, so the goal never fires.
;
; It is UNSATISFIABLE over Q (at c = 1 every element of [0, 1] is rational), and it is UNSATISFIABLE in
; M = R + Q*eps, the ordered Q-vector space with an infinitesimal eps ordered lexicographically, which
; is an elementary extension of R: at c = eps the interval [0, eps] of M is {q*eps : q rational in
; [0, 1]}, every element a rational multiple of c.
;
; So the verdicts are: standard (R) sat; standard (Q) unsat; some model sat; every model (this
; repository's per-model definition for kind-free problems) unsat.  expected (first-order reading): unsat
;
; Neither answer is reachable by a sound procedure.  A sat needs a solution in every model, which does
; not exist; an unsat needs a refutation, and none exists because R is a model with a solution.  So
; "no answer" is the correct behaviour, as for power_of_two_window_sat.smt2.
(set-logic HORN)
(declare-fun R (Real Real Real Real) Bool)
(declare-fun L (Real Real) Bool)
(assert (forall ((c Real) (z Real)) (R c z 0.0 0.0)))
(assert (forall ((c Real) (z Real) (n Real) (d Real))
  (=> (R c z n d) (R c z (+ n 1.0) (+ d z)))))
(assert (forall ((c Real) (z Real) (n Real) (d Real))
  (=> (R c z n d) (R c z n (- d c)))))
(assert (forall ((c Real) (z Real) (n Real))
  (=> (and (R c z n 0.0) (>= n 1.0)) (L c z))))
(assert (forall ((c Real))
  (=> (and (> c 0.0)
           (forall ((z Real)) (=> (and (<= 0.0 z) (<= z c)) (L c z))))
      false)))
(check-sat)
