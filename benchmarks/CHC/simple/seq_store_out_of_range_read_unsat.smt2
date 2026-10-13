; expected: unsat
;
; A read OUTSIDE a sequence is underspecified, and the sequence is part of what
; it is underspecified in: `(seq.nth s (- 1))` and `(seq.nth t (- 1))` are two
; different applications, and a solver may give them different values even when
; `s` and `t` agree everywhere inside.  So this assertion is not a consequence
; of the theory and the problem is refuted -- z3 confirms it directly, answering
; `sat` to the negation of the same equation written with the concatenation that
; `seq.store` abbreviates.
;
; It answered `sat` while the read-over-write rewrite guarded only the WRITTEN
; index: the else branch of `if j = i and i is in range then e else nth(s, j)`
; claims the two reads agree, which for an out-of-range `j` is exactly the
; agreement above.  The rewrite now also asks that the READ index be inside the
; sequence, which it can establish only where the length is available from the
; sequence's own structure.
(set-logic HORN)
(assert (forall ((s (Seq Int)) (v Int))
  (= (seq.nth (seq.store s 0 v) (- 1)) (seq.nth s (- 1)))))
(check-sat)
