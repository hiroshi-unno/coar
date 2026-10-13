; A validation query of a cell-route candidate on quantified-inv/two_arrays_offset_sat
; that Z3 refutes both with arrays and with a and b as functions Int -> Int.
(set-logic ALL)
(declare-const a (Array Int Int))(declare-const b (Array Int Int))(declare-const i Int)(declare-const n Int)(declare-const k Int)
(assert true)(assert (<= 0 n))(assert (= (select a n) (select b (+ i n))))(assert (not true))
(check-sat)
