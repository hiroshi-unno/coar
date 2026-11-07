; NOT well-founded: from an odd x, x := x + 2 (mod 256) never reaches 0 and cycles (length 128).
; An unsigned ranking 256 - x decreases on every step but the one that wraps; the strict step
; r(x) >= r(y) + 1 must be checked with r(y) != max so the wrap is not hidden.  Expected: unsat;
; PCSat answers unknown/timeout (the cycle is too long to sample), never sat.
(set-logic HORN)
(declare-wfp WF ((_ BitVec 8) (_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8)) (x1 (_ BitVec 8))) (=> (and (not (= x #x00)) (= x1 (bvadd x #x02))) (WF x x1))))
(check-sat)
