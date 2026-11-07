; POPL 2024's repair for `deferred`: the `Thunk` constructor gets a ghost field carrying the
; client's `n`, so the thunk's postcondition may be indexed by it -- `A(c, z)`, the `p4(z, c)` of
; the source's `[@@@rtype]` annotation.  Middle file of the triple; see
; arm_deferred_mono_chc_unsat.smt2 for the false negative and arm_deferred_pred_poly_sat.smt2 for
; the version that abstracts the predicate instead of storing a value.
;
; Plain CHC, satisfiable with `A(c, z) := (z = c)`.  expected: sat
(set-logic HORN)
(declare-fun A (Int Int) Bool)
(declare-fun Ans (Int Int) Bool)

(assert (forall ((c Int) (z Int)) (=> (A c z) (Ans c z))))
(assert (forall ((n Int)) (A n n)))
(assert (forall ((n Int) (z Int)) (=> (and (Ans n z) (not (= z n))) false)))
(check-sat)
