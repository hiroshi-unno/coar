(set-logic ALL)
(assert (= (select (lambda ((x Real)) x) 1.5) 1.5))
(check-sat)
