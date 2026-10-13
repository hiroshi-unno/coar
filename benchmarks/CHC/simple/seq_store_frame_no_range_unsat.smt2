; expected: unsat
;
; The discriminating control for the file beside this one. It is
; `seq_store_frame_sat.smt2` with the read index's range hypothesis
; `(<= 0 j) (< j (seq.len s))` DELETED from the premise, and nothing else
; changed.
;
; Without that hypothesis the obligation is not valid: outside the sequence a
; read is unspecified, so `seq.nth (seq.store s i v) j` and `seq.nth s j` denote
; values the theory does not tie together and need not agree. A pfwCSP/CHC
; system with no unknown is satisfiable exactly when its constraints are valid,
; so the answer is `unsat`.
;
; What it pins is the rewrite that makes the twin answer. The read-over-write
; law is applied once per clause, using the clause's own other disjuncts as
; hypotheses, and it may fire ONLY where those hypotheses put the read index
; inside the sequence. If it fired here anyway, the obligation would become
; `ite(i = j and 0 <= i < len s, v, nth(s, j)) = nth(s, j)`, which under the
; surviving premise `i != j` IS valid -- so a rewrite that stopped consulting
; its hypothesis would turn this file's `unsat` into `sat`. The twin alone
; cannot catch that; this file is why the pair is a pair.
(set-logic HORN)
(assert (forall ((s (Seq Int)) (i Int) (j Int) (v Int))
  (=> (and (<= 0 i) (< i (seq.len s)) (not (= i j)))
      (and (= (seq.len (seq.store s i v)) (seq.len s))
           (= (seq.nth (seq.store s i v) j) (seq.nth s j))))))
(check-sat)
