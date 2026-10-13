(set-logic HORN)

(declare-fun I ((Array Int Int)) Bool)

;; a[0] = 2, a[1] = 4 -> I(a)
(assert (forall ((a (Array Int Int)))
		(=>
		 (and (= (select a 0) 2)
		      (= (select a 1) 4))
		 (I a))))

(check-sat)
(get-model)
