;; Renamed from *_unsat to *_sat on 2026-09-26 (maintainer). The repository's definition reads the
;; background theory as an SMT-LIB theory, whose models fix the standard structure (Int is the set of
;; all integers, Real the set of all reals), so this system is SATISFIABLE. Read over every model of
;; the FIRST-ORDER theory (non-standard models included), it is UNSATISFIABLE; that reading is what the
;; comments below were written for. expected: sat
; The induction axiom as a clause over a UNIVERSAL
; predicate symbol X (a declare-forall-fun, so the problem is "for every X"; no unknown at all).
;   X(0) /\ (forall n. n >= 0 /\ X(n) => X(n+1)) /\ n0 >= 0  =>  X(n0)
; True in the standard structure (induction on Z's non-negatives), false in a non-standard Z*,
; where X := the standard non-negatives is a proper cut.  With no unknown,
; "satisfiable" means valid; the repository's per-model definition asks for truth in every model,
; and no predicate kind is involved, so the verdict it defines is UNSATISFIABLE (standard: sat).
; Whether kind-free universal premises should also be read over the intended structure is an
; open question.  expected (first-order reading): unsat
(set-logic QHORN)
(declare-forall-fun X (Int) Bool)
(assert (forall ((n0 Int))
  (=> (and (X 0)
           (forall ((n Int)) (=> (and (>= n 0) (X n)) (X (+ n 1))))
           (>= n0 0))
      (X n0))))
(check-sat)
