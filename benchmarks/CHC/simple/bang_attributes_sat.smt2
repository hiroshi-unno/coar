; An SMT-LIB command the reader once refused: (! t attrs) with attributes other than :named/:pattern; all attributes are dropped.  Expected: sat.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (! (forall ((x Int)) (=> (> x 0) (P x))) :named a1 :weight 2 :qid q1))
(assert (forall ((x Int)) (! (=> (and (P x) (<= x 0)) false) :pattern ((P x)) :named a2)))
(check-sat)
