; expected: sat
;
; One write into a sequence, stated as a relation W(s, i, t) between the old
; sequence, the written position and the new sequence -- the relation a slice
; write `s[i] = 0` contributes to a loop or a callee summary.  The fact clause
; builds t by the write; the two queries ask for the frame property (the length
; is kept, and every other in-range position is kept) and for the written value.
;
; Satisfiable: W(s, i, t) := 0 <= i < seq.len s /\ t = seq.store s i 0 makes
; every clause valid.  The fact clause is its own definition.  In the
; queries, the premise fixes t to the write with i in range, so seq.len t =
; seq.len s, seq.nth t i = 0, and seq.nth t j = seq.nth s j for every in-range
; j <> i -- the read-over-write laws of the sequence theory, with every read in
; range.  Without the range conjunct the candidate is too weak: seq.nth t i for
; an out-of-range i is a value the theory leaves open.
;
; The composition clause (a write repeated at the same position is the write)
; keeps W recursive, so the preprocessor cannot eliminate it and the answer has
; to come from synthesis.  Composition holds for the solution above because
; seq.store (seq.store s i 0) i 0 = seq.store s i 0 whenever i is in range.
;
; What the candidate needs is an equality between two WHOLE sequences, which a
; cell qualifier (one position of one sequence) cannot state.  Recorded
; 2026-09-25, one run each at 120 s: pcsat_tbq_ar answers sat,4, and the cell
; chains pcsat_tbq_cell_seq2 and pcsat_tbq_cell_seq3 answer nothing.  The
; equality t = seq.store s i 0 is offered to W by the ordinary extraction (the
; fact clause states it over W's own arguments), and under the seq3 chain it
; also survives the cell-only cut, but the celled example rows replace the
; sequences by their cells, so a whole-sequence equality separates no two of
; them.
(set-logic HORN)
(declare-fun W ((Seq Int) Int (Seq Int)) Bool)
(assert (forall ((s (Seq Int)) (i Int) (t (Seq Int)))
  (=> (and (<= 0 i) (< i (seq.len s)) (= t (seq.store s i 0))) (W s i t))))
(assert (forall ((s (Seq Int)) (i Int) (t (Seq Int)) (u (Seq Int)))
  (=> (and (W s i t) (W t i u)) (W s i u))))
(assert (forall ((s (Seq Int)) (i Int) (t (Seq Int)) (j Int))
  (=> (and (W s i t) (<= 0 j) (< j (seq.len s)) (not (= j i)))
      (= (seq.nth t j) (seq.nth s j)))))
(assert (forall ((s (Seq Int)) (i Int) (t (Seq Int)))
  (=> (W s i t) (and (= (seq.len t) (seq.len s)) (= (seq.nth t i) 0)))))
(check-sat)
