; A sort name introduced twice at top level is malformed (z3 rejects it): refuse it before
; solving rather than let the later introduction silently replace the earlier one.
(set-logic ALL) (define-sort S () Bool) (declare-datatype S ((a))) (declare-const x S) (assert x) (check-sat)
