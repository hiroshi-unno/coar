(set-logic ALL)
(assert (distinct (select (lambda ((x Real)) x) 1.5) 1.5))
(check-sat)
