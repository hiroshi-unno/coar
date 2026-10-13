(set-logic ALL)
(declare-const |#x01| (_ BitVec 8))
(assert (= |#x01| #x02))
(check-sat)
