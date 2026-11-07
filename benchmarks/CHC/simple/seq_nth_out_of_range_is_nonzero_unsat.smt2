; expected: unsat
;
; The negation of seq_nth_out_of_range_is_zero_unsat.smt2's claim: a read
; past the end of a sequence is open, so "it is never 0" is not a
; consequence of the theory either.  Together the two files refute any fold
; of the open read to a constant.
(set-logic HORN)
(assert (forall ((x Int)) (not (= (seq.nth (seq.unit x) 1) 0))))
(check-sat)
