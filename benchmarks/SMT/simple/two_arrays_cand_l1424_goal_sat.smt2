; A validation query of a cell-route candidate on quantified-inv/two_arrays_offset_sat:
; the negated goal clause with the candidate substituted (trace line 1424).  Z3 4.15.2
; leaves it undecided at 11 s with a and b arrays; with a and b uninterpreted
; functions Int -> Int it answers sat in a tenth of a second, and the two are
; equisatisfiable because a and b are read only through select.
(set-logic ALL)
(declare-const a (Array Int Int))(declare-const b (Array Int Int))(declare-const i Int)(declare-const n Int)(declare-const k Int)
(assert (forall ((v84232 Int) (v84230 Int)) (or (and (> 0 (- v84230 i)) (< 0 (select b v84232)) (>= 0 (select a v84230)) (>= n (select a v84230)) (>= i (select a v84230)) (<= v84230 i)) (and (= (select a v84230) (select b v84232)) (< 0 (select a v84230)) (< i (select a v84230))) (and (<= 0 (- v84230 n)) (>= v84230 n)) (and (= (select a v84230) (select b v84232)) (<= 0 (select a v84230))))))(assert (<= 0 k))(assert (< k n))(assert (not (= (select a k) (select b (+ i k)))))
(check-sat)
