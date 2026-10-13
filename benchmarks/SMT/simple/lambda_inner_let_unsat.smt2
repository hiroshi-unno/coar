(set-logic ALL)
(assert (distinct (select (lambda ((x Int)) (let ((a x)) a)) 3) 3))
(check-sat)
