(set-logic ALL)
(assert (forall ((a (Array Int Int))) (exists ((i Int)) (= (select a i) (select a i)))))
(check-sat)
