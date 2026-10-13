; expected: error before a solver verdict; S requires one sort argument.
(set-logic ALL)
(declare-sort S 1)
(declare-const x S)
(assert (= x x))
(check-sat)
