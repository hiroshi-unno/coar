; expected: unsat
;
; A solution has to satisfy every clause in every model of the theory, and a
; read outside a sequence is a term the theory leaves open.  The first clause's
; read is forced out of range (`seq.len s <= i`), and it is guarded on the
; lower side only (`0 <= i`).  Some model gives `(seq.nth s i)` the value 7 at
; `s = seq.empty, i = 0`; there the premise holds, so `P 0` is forced, and the
; second clause refutes it.  Hence no solution exists: `unsat`.  A reading that
; picks one convenient model (the out-of-range reads never equal 7) would say
; `sat`, which is the wrong question.
;
; What the file pins is the other direction of the range test that decides
; whether a sequence read is interpretation-dependent: a one-sided guard does
; not put the read in range, so the read must still be reported, with the
; refinement on as with it off.  The answer must never be `sat`.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((s (Seq Int)) (i Int))
  (=> (and (<= 0 i) (<= (seq.len s) i) (= (seq.nth s i) 7)) (P 0))))
(assert (=> (P 0) false))
(check-sat)
