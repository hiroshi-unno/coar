; P is functional with no argument, so it holds of exactly one byte v, which
; would have to satisfy v <s 0 and v >s -1: no byte does, unsat.
(set-logic HORN)
(declare-fnp P ((_ BitVec 8)) Bool)
(assert (forall ((v (_ BitVec 8))) (=> (P v) (and (bvslt v #x00) (bvsgt v #xff)))))
(check-sat)
