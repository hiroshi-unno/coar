; expected: unsat
;
; `(seq.extract s 0 k)` is the prefix of `s` of length max 0 (min k (len s)).
; The prefix of [1, 2] and the prefix of [1] agree for k <= 1 and differ at
; k = 2, so the universal claim is false.  It exercises the prefix-over-
; concatenation identity, which must keep the second element when k exceeds
; the length of the first part.
(set-logic HORN)
(assert (forall ((k Int))
  (= (seq.extract (seq.++ (seq.unit 1) (seq.unit 2)) 0 k)
     (seq.extract (seq.unit 1) 0 k))))
(check-sat)
