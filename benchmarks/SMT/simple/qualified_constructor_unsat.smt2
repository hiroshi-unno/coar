; A sort-qualified nullary constructor denotes the same value as its plain name.
(set-logic ALL)
(declare-datatype E ((a) (b)))
(declare-const x E)
(assert (= x (as a E))) (assert (not (= x a)))
(check-sat)
