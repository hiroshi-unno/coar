; rotating right by 6 on four bits is rotating right by 2; the x it asks for exists
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= ((_ rotate_right 6) x) #b0110))
(assert (= ((_ rotate_left 3) x) #b1100))
(check-sat)
