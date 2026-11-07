; A functional relation cannot return both 0 and 1 for the same input.
(set-logic HORN)
(declare-fnp |3| (Int Int) Bool)
(assert (|3| 0 0))
(assert (|3| 0 1))
(check-sat)
