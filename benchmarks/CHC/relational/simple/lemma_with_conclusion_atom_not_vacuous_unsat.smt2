; Applying a lemma whose conclusion is an atom must add that atom, not make the
; sequent vacuous.  P is {0, 1, 2, ...}, so the query "1000 is not in P" is
; false: the problem is unsat.  The lemma P(x) => W(x) is true (W holds
; everywhere) and is proved; applying it to the query adds W(x) and nothing
; else, which does not close the query.  The relational proof search of MuCyc
; (config/solver/mucyc_relational.json) once added the negation of the
; lemma's own premise constraint as well, which made every sequent the lemma
; applied to valid and answered sat here.  The refutation needs a derivation
; of height 1001, so the search answers unknown or runs out of time, never
; sat.
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun W (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (= y (+ x 1))) (P y))))
(assert (forall ((x Int)) (W x)))
(assert (forall ((x Int)) (=> (and (P x) (= x 1000)) false)))
(set-info :coar-lemma (forall ((x Int)) (=> (P x) (W x))))
(check-sat)
