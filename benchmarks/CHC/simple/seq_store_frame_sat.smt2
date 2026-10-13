; expected: sat
;
; The twin of the `unsat` file beside this one, pinning the other direction and
; the other half of what a write symbol buys: its FRAME property. A `seq.store`
; leaves the length alone and leaves every position but the written one alone,
; and both are meant to be syntactic facts here rather than consequences a
; solver derives from the sequence axioms -- the point of not expanding the
; write until the solver boundary.
;
; Both conjuncts of the conclusion are valid, so the problem is satisfiable. A
; rewrite that dropped the written index's guard would still prove these two;
; the `unsat` twin is what pins that guard.
;
; ANSWERED `sat,0` SINCE 2026-09-18, and this file is why the rewrite moved.
; The read-over-write law has to know that the read index is inside the sequence
; -- rewriting an out-of-range read into a read of another sequence claims an
; agreement the theory does not give -- and that hypothesis is stated in this
; clause's PREMISE, where a rewrite on terms cannot see it. A rewrite on terms
; therefore declined here and the second conjunct was left to the solver, which
; does not settle it: the sequence write is this tool's own symbol and no SMT
; solver has a law for it. The rule is now applied once per clause instead,
; where the premise is in hand: a clause is a disjunction, so while rewriting
; one disjunct every other disjunct may be assumed false, and those assumptions
; are exactly `0 <= j < seq.len s`.
(set-logic HORN)
(assert (forall ((s (Seq Int)) (i Int) (j Int) (v Int))
  (=> (and (<= 0 i) (< i (seq.len s)) (<= 0 j) (< j (seq.len s)) (not (= i j)))
      (and (= (seq.len (seq.store s i v)) (seq.len s))
           (= (seq.nth (seq.store s i v) j) (seq.nth s j))))))
(check-sat)
