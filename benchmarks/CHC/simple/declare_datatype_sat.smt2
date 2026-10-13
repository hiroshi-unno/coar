; An SMT-LIB command the reader once refused: the singular declare-datatype (SMT-LIB 2.6), desugared to declare-datatypes.  Expected: sat.
(set-logic HORN)
(declare-datatype Lst ((nil) (cons (hd Int) (tl Lst))))
(declare-fun P (Lst) Bool)
(assert (forall ((l Lst)) (=> (= l nil) (P l))))
(assert (forall ((l Lst)) (=> (and (P l) (not (= l nil))) false)))
(check-sat)
