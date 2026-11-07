(set-logic HORN)
(define-fun-rec f ((x Int)) Int (ite (= (div 1 0) (div (- 2 1) 0)) (- (f x)) (+ (f x) 1)))
(assert true)
(check-sat)
