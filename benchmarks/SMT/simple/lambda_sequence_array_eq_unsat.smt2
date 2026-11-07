; C495: equal singleton sequences have equal elements, but these arrays
; differ at index 0 (0 versus 3). Native Z3 5.1.0 incorrectly answered sat.
(set-logic ALL)
(declare-const s (Seq (Array Int Int)))
(assert (= s (seq.unit (store (lambda ((x Int)) x) 7 0))))
(assert (= s (seq.unit (store ((as const (Array Int Int)) 3) 7 0))))
(check-sat)
