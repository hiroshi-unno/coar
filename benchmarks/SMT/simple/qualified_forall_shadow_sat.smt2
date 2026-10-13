; A scoped term binding takes precedence over the same-named constructor.
(set-logic ALL)
(declare-datatype E ((a) (b)))
(assert (forall ((a E)) (= (as a E) a)))
(check-sat)
