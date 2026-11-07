; expected: unsat
;
; `(seq.nth (seq.unit x) 1)` reads past the end of a one-element sequence.
; SMT-LIB leaves such a read open: in each model it is some integer, a
; function of the sequence and the index, and different models choose
; differently.  So "it is 0 for every x" holds in some models and not in
; others, and the constraint is not satisfied by this tool's reading
; (it must hold whatever the theory leaves open).  A simplifier that folded
; the read to 0, or to the neighbouring element, would answer `sat`.
; The companion seq_nth_out_of_range_is_nonzero_unsat.smt2 pins the other
; direction, so a fold to any constant fails one of the two.
(set-logic HORN)
(assert (forall ((x Int)) (= (seq.nth (seq.unit x) 1) 0)))
(check-sat)
