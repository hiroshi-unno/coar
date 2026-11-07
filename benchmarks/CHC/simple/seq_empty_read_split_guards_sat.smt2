; expected: sat
;
; `s` is the empty sequence in both clauses, so `(seq.nth s 0)` is the one value
; a model gives to a read out of range.  In each model `P 1` is forced only when
; that value is 0, and the query needs it to be 1, so every model admits an
; interpretation of `P`: the problem is satisfiable.  Z3's Spacer finds a
; solution, but writes it with `seq.nth_i` (the read at an in-range index),
; which is not `seq.nth` at every index and has no term in this tree; the
; Spacer backend then answers `unknown` instead of raising an exception.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((s (Seq Int))) (=> (and (= (seq.len s) 0) (= (seq.nth s 0) 0)) (P 1))))
(assert (forall ((s (Seq Int))) (=> (and (P 1) (= (seq.len s) 0) (= (seq.nth s 0) 1)) false)))
(check-sat)
