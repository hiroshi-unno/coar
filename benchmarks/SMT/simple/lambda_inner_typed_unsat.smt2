(set-logic ALL)
(define-const k Int 3)
(assert (distinct (select (lambda ((x Int)) (let ((a x)) a)) k) k))
(check-sat)
