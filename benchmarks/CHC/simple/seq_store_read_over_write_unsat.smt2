; expected: unsat
;
; `seq.store` is not an SMT-LIB symbol -- SMT-LIB sequences have no write, and a
; front end that models one has to spell out the three-piece concatenation
; `(seq.++ (seq.++ (seq.extract s 0 i) (seq.unit v)) (seq.extract s (+ i 1) ...))`
; at every write. This tool reads the single symbol and expands it at the solver
; boundary, which keeps a write one node where a qualifier and a read-over-write
; rewrite can see it.
;
; The clause is invalid, and refuting it is exactly read over write: the premise
; writes 7 at a position of s and reads the same position back, so the
; conclusion asking for 8 fails. Written against the guarded meaning -- the
; premise states that i is a position of s, because past the end the three-piece
; concatenation appends rather than replaces and the written value would not be
; where the read looks.
(set-logic HORN)
(assert (forall ((s (Seq Int)) (i Int))
  (=> (and (<= 0 i) (< i (seq.len s)))
      (= (seq.nth (seq.store s i 7) i) 8))))
(check-sat)
