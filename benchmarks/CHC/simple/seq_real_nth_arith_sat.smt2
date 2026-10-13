; expected: sat
;
; `P(s, i) := seq.nth s i > 0.0` satisfies all three clauses in every model of
; the theory: the first clause's conclusion is its own premise, the second's
; follows from `s[i+1] > s[i] > 0`, and the third's `s[i] + 1 > 0` follows from
; `s[i] > 0`.  The solution mentions the same read as the clauses, so it holds
; whatever value a model gives a read outside the sequence's range.
;
; What the file pins is that a read of a sequence of REALS inside real
; arithmetic is readable at all: the real normaliser had no case for it (the
; integer one treats such a read as an atom) and the file failed at parse time
; with "[real_monomials_of] not supported: (seq.nth ...)".
(set-logic HORN)
(declare-fun P ((Seq Real) Int) Bool)
(assert (forall ((s (Seq Real)) (i Int))
  (=> (and (<= 0 i) (< i (seq.len s)) (> (seq.nth s i) 0.0)) (P s i))))
(assert (forall ((s (Seq Real)) (i Int))
  (=> (and (P s i) (< (+ i 1) (seq.len s)) (> (seq.nth s (+ i 1)) (seq.nth s i))) (P s (+ i 1)))))
(assert (forall ((s (Seq Real)) (i Int))
  (=> (P s i) (> (+ (seq.nth s i) 1.0) 0.0))))
(check-sat)
