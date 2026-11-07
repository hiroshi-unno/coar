; A false lemma must not be used.  P is the set {0, 1, 2, ...} (P(0), and
; P(x + 1) from P(x)), so the query "1000 is not in P" is false: the problem
; is unsat.  The lemma below claims every x in P is at most 1, which is false
; (P(2) holds); were it assumed, it would close the query at once and the
; answer would be a wrong sat.  The relational proof search of MuCyc
; (config/solver/mucyc_relational.json) tries to prove the lemma, refutes it
; (P(2) is a derivation of height 3), reports it unused, and then cannot
; decide the query, whose refutation needs a derivation of height 1001: it
; answers unknown or runs out of time, never sat.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (= y (+ x 1))) (P y))))
(assert (forall ((x Int)) (=> (and (P x) (= x 1000)) false)))
(set-info :coar-lemma (forall ((x Int)) (=> (P x) (<= x 1))))
(check-sat)
