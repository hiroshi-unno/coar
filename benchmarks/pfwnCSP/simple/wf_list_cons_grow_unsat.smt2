; NOT well-founded: l -> cons(h, l) grows forever (no cycle, so not finitely refutable).
; Expected: unsat; PCSat answers unknown/timeout, never sat.
(set-logic HORN)
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(declare-wfp WF (L L) Bool)
(assert (forall ((l L) (l1 L) (h Int)) (=> (= l1 (cons h l)) (WF l l1))))
(check-sat)
