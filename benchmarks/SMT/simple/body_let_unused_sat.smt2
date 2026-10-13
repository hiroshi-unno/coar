(set-logic ALL)
(define-fun-rec f ((n Int)) Int (let ((m (- n 1))) (ite (<= n 0) 0 (+ 1 (f m)))))
(assert true)
(check-sat)
