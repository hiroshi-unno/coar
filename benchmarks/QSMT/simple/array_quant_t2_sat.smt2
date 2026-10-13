(set-logic ALL)
(assert (exists ((a (Array Int Int))) (forall ((i Int)) (= (select a i) 0))))
(check-sat)
