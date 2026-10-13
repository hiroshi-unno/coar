; expected: sat
;
; `Q(s, i) := seq.nth s i` and `B(b) := b` satisfy all four clauses in every
; model of the theory: the first two clauses conclude `Q` from its own
; definition, the third needs `B(s[i])` where `s[i]` holds, and the fourth
; refutes only a pair of `B`-true values whose conjunction is false, which
; `B(b) := b` never has.  The solution mentions the same read as the clauses,
; so it holds whatever value a model gives a read outside the range.
;
; What the file pins is a read of a sequence of BOOLEANS standing as a formula
; and passed as a Boolean argument.  The SMT-LIB reader looked the head of a
; formula-position application up as a name, and failed with "seq.nth is not
; bound" (it already accepted `select` there, the same case); once read, the
; simplifier rewrote `s[i] = true` into the formula of `s[i]`, which is
; `s[i] = true` again, and looped until the budget ran out.
(set-logic HORN)
(declare-fun Q ((Seq Bool) Int) Bool)
(declare-fun B (Bool) Bool)
(assert (forall ((s (Seq Bool)) (i Int))
  (=> (and (<= 0 i) (< i (seq.len s)) (seq.nth s i)) (Q s i))))
(assert (forall ((s (Seq Bool)) (i Int))
  (=> (and (Q s i) (< (+ i 1) (seq.len s)) (seq.nth s (+ i 1))) (Q s (+ i 1)))))
(assert (forall ((s (Seq Bool)) (i Int))
  (=> (Q s i) (B (seq.nth s i)))))
(assert (forall ((b Bool) (c Bool))
  (=> (and (B b) (B c) (not (and b c))) false)))
(check-sat)
