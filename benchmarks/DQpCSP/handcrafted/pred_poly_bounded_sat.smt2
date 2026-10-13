; The same definition as pred_poly_naked_forall_unsat.smt2, made verifiable by **bounded**
; predicate polymorphism -- the mechanism the POPL 2024 ARM implementation also has
; (`Rtype.RForall (penv, constrs, c)`): the definition is verified for every X *that satisfies
; the bound*, and the client discharges the bound at its instantiation.
;
;     f : forall X with (a. X(a) => X(a+1)). (a:{X}) -> ...
;
; The bound enters as a premise of the definition's clauses, at the clause's own variable -- the
; same shape as a trait law (`fresh_function_law_sat.smt2`), so the clause
; stays universal and in QECHC (a universal-predicate literal in a body is unrestricted; note it
; is *not* in QCHC proper, which counts universal literals).  The client's obligation is the
; bound at its own instantiation, a pure theory check.
;
; This is the shape the paper should present as "the modular constraint": the definition is
; verified once, for every admissible X, and no client ever re-verifies it.  expected: sat
(set-logic DQHORN)
(declare-forall-fun X (Int) Bool)
(declare-dep-exists-fun P () ((Array Int Bool) Int) Bool)
; definition side, once for every X satisfying the bound
(assert (forall ((a Int)) (=> (X a) (P X a))))
(assert (forall ((a Int)) (=> (and (=> (X a) (X (+ a 1))) (P X a) (not (X (+ a 1)))) false)))
; client 1: X := (>= 0) -- use, and discharge of the bound
(assert (forall ((a Int)) (=> (and (P (lambda ((b Int)) (>= b 0)) a) (< a 0)) false)))
(assert (forall ((a Int)) (=> (and (>= a 0) (not (>= (+ a 1) 0))) false)))
; client 2: X := (> 5) -- the same solution for P must serve it too
(assert (forall ((a Int)) (=> (and (P (lambda ((b Int)) (> b 5)) a) (<= a 5)) false)))
(assert (forall ((a Int)) (=> (and (> a 5) (not (> (+ a 1) 5))) false)))
(check-sat)
