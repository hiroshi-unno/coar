; A sort name introduced twice at top level is malformed (z3 rejects it): refuse it before
; solving rather than let the later introduction silently replace the earlier one.
(set-logic ALL) (declare-sort S 0) (define-sort S () Bool) (declare-const x S) (assert x) (check-sat)
