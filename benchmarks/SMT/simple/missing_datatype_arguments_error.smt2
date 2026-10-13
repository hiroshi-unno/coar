; expected: error before a solver verdict; Box requires one sort argument.
(set-logic ALL)
(declare-datatypes ((Box 1)) ((par (T) ((mkBox (value T))))))
(declare-const x Box)
(assert (= x x))
(check-sat)
