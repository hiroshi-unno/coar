; A sort name introduced twice at top level is malformed (z3 rejects it): refuse it before
; solving rather than let the later introduction silently replace the earlier one.
(set-logic ALL) (declare-datatype S ((a))) (declare-datatype S ((b))) (declare-const x S) (assert (= x b)) (check-sat)
