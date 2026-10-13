(set-logic ALL)
(assert (forall ((a (Array Int Int)) (i Int)) (=> (= a (store a i 3)) (= (select a i) 3))))
(check-sat)
