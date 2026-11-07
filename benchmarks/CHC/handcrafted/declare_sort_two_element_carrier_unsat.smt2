; two_element_carrier_unsat with (declare-sort a 0) in place of (declare-forall-sort a).
; A system is satisfiable when one interpretation of the unknowns makes every clause hold in
; every model of the background theory, and an uninterpreted sort's carrier is part of the
; model, so a plain declare-sort is quantified universally exactly like a forall-sort: this file
; and its forall-sort twin have the same meaning and must get the same verdict.  What differs is
; the implementation -- a declare-sort is SUS, a forall-sort SVar, and the synthesizer's
; per-parameter dummies and existential witness are for SVar only -- so this file pins the
; semantics, not the completeness (measured 2026-09-12: unsat,0 under pcsat_tbq_ar; no answer
; in 30 s under pcsat_wopp_tbq_ar, like its twin).  expected: unsat
(set-logic QHORN)
(declare-sort a 0)
(declare-fun P (a) Bool)
(assert (forall ((x a) (y a)) (=> (distinct x y) (P x))))
(assert (forall ((x a) (y a)) (=> (and (distinct x y) (P y)) false)))
(check-sat)
