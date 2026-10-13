(set-logic ALL)
(assert (distinct (select (lambda ((x Int)) x) 3) 3))
(check-sat)
