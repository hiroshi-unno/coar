; NOT well-founded in every model: tl applied to nil is unspecified, and in a model where
; tl(nil) = nil the relation has the self-loop nil -> nil, so it is not well-founded for all
; models of the datatype theory.  Expected: unsat (or unknown), never sat.  The guarded
; twin is wf_list_tail_sat.smt2.
(set-logic HORN)
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(declare-wfp WF (L L) Bool)
(assert (forall ((l L) (l1 L)) (=> (= l1 (tl l)) (WF l l1))))
(check-sat)
