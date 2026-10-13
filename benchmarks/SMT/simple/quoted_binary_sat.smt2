(set-logic ALL)
(declare-const |#b01| (_ BitVec 2))
(assert (= |#b01| #b10))
(check-sat)
