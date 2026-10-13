;; Expected sat (formerly named *_unsat). This repository's definition reads the
;; background theory as an SMT-LIB theory, whose models fix the standard structure (Int is the set of
;; all integers, Real the set of all reals), so this system is SATISFIABLE. Read over every model of
;; the FIRST-ORDER theory (non-standard models included), it is UNSATISFIABLE; that reading is what the
;; comments below were written for. expected: sat
; Standard satisfiability does not transfer to every first-order model, with unknowns only.
;
;   NP(z)  <=  z >= 3 and z odd
;   NP(2z) <=  NP(z)
;   false  <=  x >= 1 and (forall z. x <= z <= 2x => NP(z))
;
; Over the integers the least solution of NP is the positive integers that are not powers of two.
; Every window [x, 2x] with x >= 1 contains a power of two, so the goal never fires, and the system
; is SATISFIABLE over Z.
;
; In a non-standard model of Th(Z, 0, 1, +, <) it is UNSATISFIABLE.  Take the Z-group
; M = {(y, k) in Q x Q : k + y*rho is a profinite integer}, ordered lexicographically, where the
; 2-adic component of rho is irrational.  In M only 0 is divisible by every power of two, so every
; element of the window [c, 2c] for c = (1, 0) is 2^j * (odd, non-standard) with j standard.  It
; therefore lies in the least solution of NP, and the goal fires at x = c.
;
; So the verdicts are: standard sat; some model (SMT "modulo T") sat; every model (this repository's
; per-model definition for kind-free problems) unsat.  expected (first-order reading): unsat
; Under the standard-structure reading of the header, the expected verdict is sat.
;
; Neither answer is reachable by a sound procedure.  No Presburger-definable solution exists: a
; semilinear superset of the non-powers of two contains a whole window.  No finite refutation exists
; either, because Z is a model.  So "no answer" is the correct behaviour.  A sat is wrong under the
; definition, and an unsat would rest on a refutation that cannot exist.
(set-logic HORN)
(declare-fun NP (Int) Bool)
(assert (forall ((z Int)) (=> (and (>= z 3) (= (mod z 2) 1)) (NP z))))
(assert (forall ((z Int)) (=> (NP z) (NP (* 2 z)))))
(assert (forall ((x Int))
  (=> (and (>= x 1)
           (forall ((z Int)) (=> (and (<= x z) (<= z (* 2 x))) (NP z))))
      false)))
(check-sat)
