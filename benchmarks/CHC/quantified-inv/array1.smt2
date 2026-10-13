(set-logic HORN)

(declare-fun I ((Array Int Int)) Bool)
(declare-fun J ((Array Int Int)) Bool)

;; a[0] = 2, a[1] = 4 -> I(a)
(assert (forall ((a (Array Int Int)))
		(=>
		 (and (= (select a 0) 2)
		      (= (select a 1) 4))
		 (I a))))

;; I(a), a[0] + a[1] + a[2] = 10 -> J(a)
(assert (forall ((a (Array Int Int)))
		(=>
		 (and
		  (I a)
		  (=
		   (+ (select a 0)
		      (select a 1)
		      (select a 2))
		   10))
		 (J a))))

(assert (forall ((a (Array Int Int)))
		(=> (I a) (= (select a 0) 1))))

(check-sat)
(get-model)
