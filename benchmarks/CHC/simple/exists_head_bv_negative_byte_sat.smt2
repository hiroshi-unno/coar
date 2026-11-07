; An existential head over a byte: for x >= 0 some v satisfies v <s 0 and
; v >s -2, namely v = -1 (#xff): sat.
(set-logic HORN)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (>= x 0) (Q x))))
(assert (forall ((x Int)) (=> (Q x) (exists ((v (_ BitVec 8))) (and (bvslt v #x00) (bvsgt v #xfe))))))
(check-sat)
