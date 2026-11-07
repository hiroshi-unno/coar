; NOT well-founded: (bvsle x #x7f) holds for every 8-bit x, so x, x+1, ... wraps from 127 to -128
; and cycles through all 256 values.  Read as an unbounded integer the guard x <= 127 would make
; 127 - x a ranking function; a bit-vector ranking must not cross the wrap.  Expected: unsat (no
; WF relation contains a cycle); PCSat answers unknown/timeout, never sat.
(set-logic HORN)
(declare-wfp WF ((_ BitVec 8) (_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8)) (x1 (_ BitVec 8))) (=> (and (bvsle x #x7f) (= x1 (bvadd x #x01))) (WF x x1))))
(check-sat)
