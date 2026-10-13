(set-logic ALL)
(assert (distinct (let ((x 1)) (select (lambda ((x Int)) x) 3)) 3))
(check-sat)
