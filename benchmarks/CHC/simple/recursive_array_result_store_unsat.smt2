(set-logic HORN)
(define-fun-rec a ((x Int)) (Array Int Int) (store (a x) 0 (+ (select (a x) 0) 1)))
(assert true)
(check-sat)
