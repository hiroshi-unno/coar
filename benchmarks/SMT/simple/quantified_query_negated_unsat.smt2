; expected: unsat
;
; The negation of the first file, refuted under either strategy. The direction a
; repair must not overshoot into: whatever the scope discipline, this one has to
; stay unsat.
(set-logic ALL)
(assert (not (forall ((x Int)) (exists ((y Int)) (> y x)))))
(check-sat)
