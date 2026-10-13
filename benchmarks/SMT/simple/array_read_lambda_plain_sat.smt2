(set-logic ALL)
(assert (= (select (lambda ((x Int)) x) 3) 3))
(check-sat)
