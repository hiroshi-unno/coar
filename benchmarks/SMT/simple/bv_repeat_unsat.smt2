; (_ repeat i) of the QF_BV logic: i copies concatenated
(set-logic QF_BV)
(declare-const x (_ BitVec 2))
(assert (= x #b10))
(assert (not (and (= ((_ repeat 2) x) #b1010)
                  (= ((_ repeat 1) x) x)
                  (= ((_ repeat 3) #b01) #b010101))))
(check-sat)
