; A recursive definition that counts upwards: no formal decreases, so its
; totality is proved only by the declared measure (len s - i), which every
; recursive call takes from a non-negative value to a smaller one.
(set-logic ALL)
(define-fun-rec cnt_up ((s (Seq Int)) (i Int)) Int
  (! (ite (or (< i 0) (>= i (seq.len s))) 0 (+ 1 (cnt_up s (+ i 1))))
     :decreases (- (seq.len s) i)))
(assert (= (cnt_up (seq.++ (seq.unit 5) (seq.unit 7)) 0) 2))
(check-sat)
