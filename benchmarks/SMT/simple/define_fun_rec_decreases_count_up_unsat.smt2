; The same definition as define_fun_rec_decreases_count_up_sat.smt2; the
; count of a two-element sequence from index 0 is 2, not 3.
(set-logic ALL)
(define-fun-rec cnt_up ((s (Seq Int)) (i Int)) Int
  (! (ite (or (< i 0) (>= i (seq.len s))) 0 (+ 1 (cnt_up s (+ i 1))))
     :decreases (- (seq.len s) i)))
(assert (= (cnt_up (seq.++ (seq.unit 5) (seq.unit 7)) 0) 3))
(check-sat)
