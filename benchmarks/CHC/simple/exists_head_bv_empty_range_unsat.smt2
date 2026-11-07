; An existential head over a byte: for x >= 0 some v must satisfy v <s 0 and
; v >s -1, which no byte does, and Q holds at x = 0: unsat.
(set-logic HORN)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (>= x 0) (Q x))))
(assert (forall ((x Int)) (=> (Q x) (exists ((v (_ BitVec 8))) (and (bvslt v #x00) (bvsgt v #xff))))))
(check-sat)
