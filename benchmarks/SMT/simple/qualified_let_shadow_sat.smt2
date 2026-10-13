; A scoped term binding takes precedence over the same-named constructor.
(set-logic ALL)
(declare-datatype E ((a) (b)))
(assert (let ((a b)) (= (as a E) b)))
(check-sat)
