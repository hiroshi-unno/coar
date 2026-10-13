; expected: sat
;
; The same for a real-valued definition and for a Bool-valued one, which inlines
; through the formula path rather than the term path -- two call sites, and only
; repairing one would leave the other.
(set-logic ALL)
(define-fun h ((r Real)) Real (+ r 1.0))
(define-fun g ((n Int)) Bool (> n 1))
(assert (and (= (h 2.0) 3.0) (= (h (/ 4.0 2.0)) 3.0) (g 2) (not (g 0))))
(check-sat)
