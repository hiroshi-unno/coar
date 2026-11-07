; A finite store patch has exactly two zero cells at indices 0, 1 and 2.
; The unsupported native recursive route must not refute this model.
(set-logic ALL)
(define-fun-rec cnt ((x Int) (t Int) (a (Array Int Int))) Int
 (ite (<= t 0) 0 (+ (cnt x (- t 1) a) (ite (= (select a (- t 1)) x) 1 0))))
(define-fun-rec arr ((dummy Int)) (Array Int Int) (lambda ((i Int)) (ite (= i 2) 15922 0)))
(assert (>= (cnt 0 3 (arr 0)) 2))
(check-sat)
