; Well-founded: x := x + 1 while x != 0 over 8 bits reaches 0 by wrapping at 255 (ranking: the
; unsigned distance to 256).  Expected: sat.
(set-logic HORN)
(declare-wfp WF ((_ BitVec 8) (_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8)) (x1 (_ BitVec 8))) (=> (and (not (= x #x00)) (= x1 (bvadd x #x01))) (WF x x1))))
(check-sat)
