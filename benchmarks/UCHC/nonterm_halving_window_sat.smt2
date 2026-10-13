;; Expected sat (formerly named *_unsat). This repository's definition reads the
;; background theory as an SMT-LIB theory, whose models fix the standard structure (Int is the set of
;; all integers, Real the set of all reals), so this system is SATISFIABLE. Read over every model of
;; the FIRST-ORDER theory (non-standard models included), it is UNSATISFIABLE; that reading is what the
;; comments below were written for. expected: sat
; The same separation as power_of_two_window_sat.smt2 inside the existential- and disjunction-free
; fragment (non-termination), read with an initial REGION.
;
; Program:  l0: z := * with x <= z <= 2x;
;           l1: while (z even and z > 0) z := z/2;  if (z = 1 or z <= 0) loop forever;  exit
; T_l(v) is the complement of the divergent set at l: the configurations from which every run
; terminates.  The goal says that every initial x >= 1 diverges.
;
; Over Z that holds: choosing the power of two in [x, 2x] halves down to 1 and loops.  So the
; system is SATISFIABLE over Z.  In the non-standard Z-group M of power_of_two_window_sat.smt2,
; every choice z in [c, 2c] for c = (1, 0) halves a standard number of times to an odd w >= 3 and
; exits.  So c terminates and the system is UNSATISFIABLE there.
; Verdicts: standard sat; some model sat; every model (per-model definition) unsat.  expected (first-order reading): unsat
; Under the standard-structure reading of the header the expected verdict is sat.
;
; With a single initial configuration (x = d) the transfer holds; it is the region that breaks it.  No definable solution and no finite refutation exist, so "no
; answer" is the correct behaviour.
(set-logic HORN)
(declare-fun T0 (Int) Bool)
(declare-fun T1 (Int) Bool)
; l1: one guarded universal premise over all successors (halve when even, self-loop at 1 or <= 0);
; an odd z >= 3 has no successor, so the premise is vacuous there
(assert (forall ((z Int))
  (=> (forall ((w Int))
        (=> (or (and (> z 0) (= z (* 2 w)))
                (and (or (= z 1) (<= z 0)) (= w z)))
            (T1 w)))
      (T1 z))))
; l0: z := * over the window [x, 2x]
(assert (forall ((x Int))
  (=> (forall ((z Int)) (=> (and (<= x z) (<= z (* 2 x))) (T1 z)))
      (T0 x))))
; every initial configuration with x >= 1 must diverge
(assert (forall ((x Int)) (=> (and (>= x 1) (T0 x)) false)))
(check-sat)
