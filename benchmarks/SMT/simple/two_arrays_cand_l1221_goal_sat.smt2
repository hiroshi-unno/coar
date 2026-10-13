; A validation query of a cell-route candidate on quantified-inv/two_arrays_offset_sat:
; the negated goal clause with the candidate substituted (trace line 1221).  Z3 4.15.2
; leaves it undecided at 11 s with a and b arrays; with a and b uninterpreted
; functions Int -> Int it answers sat in a tenth of a second, and the two are
; equisatisfiable because a and b are read only through select.
(set-logic ALL)
(declare-const a (Array Int Int))(declare-const b (Array Int Int))(declare-const i Int)(declare-const n Int)(declare-const k Int)
(assert (forall ((v78274 Int) (v78272 Int)) (or (<= 0 (- v78272 n)) (and (> 0 (- v78272 i)) (<= 0 (select b v78274)) (>= 0 (select a v78272)) (>= n (select a v78272)) (>= i (select a v78272)) (<= v78272 i)) (and (<= 0 (- v78272 n)) (> v78272 0) (>= v78272 n)) (and (= (select a v78272) (select b v78274)) (< 0 (select a v78272)) (< i (select a v78272))))))(assert (<= 0 k))(assert (< k n))(assert (not (= (select a k) (select b (+ i k)))))
(check-sat)
