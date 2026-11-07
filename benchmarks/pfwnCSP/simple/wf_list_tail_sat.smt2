; Well-founded: l -> l1 where l = cons(h, l1) (ranking: the size of the list).  Expected: sat.
(set-logic HORN)
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(declare-wfp WF (L L) Bool)
(assert (forall ((l L) (l1 L) (h Int)) (=> (= l (cons h l1)) (WF l l1))))
(check-sat)
