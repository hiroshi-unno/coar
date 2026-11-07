; Well-founded only because of the wrap: x := x + 1 while x >s 0 over 8 bits overflows from 127
; to -128 and stops (over unbounded integers it would diverge).  Expected: sat.
(set-logic HORN)
(declare-wfp WF ((_ BitVec 8) (_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8)) (x1 (_ BitVec 8))) (=> (and (bvsgt x #x00) (= x1 (bvadd x #x01))) (WF x x1))))
(check-sat)
