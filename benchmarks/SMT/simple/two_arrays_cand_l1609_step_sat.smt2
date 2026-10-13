; A validation query of a cell-route candidate on quantified-inv/two_arrays_offset_sat:
; the negated step clause with the candidate substituted (trace line 1609).  Z3 4.15.2
; leaves it undecided at 11 s with a and b arrays; with a and b uninterpreted
; functions Int -> Int it answers sat in a tenth of a second, and the two are
; equisatisfiable because a and b are read only through select.
(set-logic ALL)
(declare-const a (Array Int Int))(declare-const b (Array Int Int))(declare-const i Int)(declare-const n Int)(declare-const k Int)
(assert (forall ((v89651 Int) (v89649 Int)) (or (and (> 0 (- v89649 i)) (< 0 (select b v89651)) (>= 0 (select a v89649)) (>= n (select a v89649)) (< i (select b v89651)) (>= i (select a v89649)) (<= v89649 i)) (and (= (select a v89649) (select b v89651)) (< 0 (select a v89649)) (< i (select a v89649))) (and (<= 0 (- v89649 n)) (>= v89649 n)) (and (= (select a v89649) (select b v89651)) (<= 0 (select a v89649))))))(assert (<= 0 n))(assert (= (select a n) (select b (+ i n))))(assert (not (forall ((v89651 Int) (v89649 Int)) (or (and (> 0 (- v89649 i)) (< 0 (select b v89651)) (>= 0 (select a v89649)) (>= (+ n 1) (select a v89649)) (< i (select b v89651)) (>= i (select a v89649)) (<= v89649 i)) (and (= (select a v89649) (select b v89651)) (< 0 (select a v89649)) (< i (select a v89649))) (and (<= 0 (- v89649 (+ n 1))) (>= v89649 (+ n 1))) (and (= (select a v89649) (select b v89651)) (<= 0 (select a v89649)))))))
(check-sat)
