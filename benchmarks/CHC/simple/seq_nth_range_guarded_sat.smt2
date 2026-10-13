; expected: sat
;
; `P(x) := x >= 0` satisfies all three clauses in every model of the theory:
; the second clause's conclusion `x + 1 >= 0` follows from `x >= 0` whatever
; the sequence part says, so the problem is satisfiable.
;
; What the file pins is the classification of its sequence read.  The read
; `(seq.nth t j)` is guarded by `0 <= j < seq.len t` in the same clause, so
; wherever it is out of range the clause holds anyway, and wherever it is in
; range the theory fixes its value: the clause's pure part has the same truth
; value in every model and is NOT interpretation-dependent.  Its guard group
; `j < 0 \/ j >= seq.len t \/ seq.nth t j <= 0` shares no variable with the
; predicate atoms and is false for some `t, j` in every model, so the
; eliminator may drop it and strengthen the clause to `P x => P (x + 1)`.
; With the classification by symbol it is reported instead, and the step asks a
; universal-closure query over a sequence binder, which is refused, so the
; group is kept.  Either way the answer must be `sat`.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (P 0))
(assert (forall ((x Int) (t (Seq Int)) (j Int))
  (=> (and (P x) (<= 0 j) (< j (seq.len t)) (> (seq.nth t j) 0)) (P (+ x 1)))))
(assert (forall ((x Int)) (=> (P x) (>= x 0))))
(check-sat)
