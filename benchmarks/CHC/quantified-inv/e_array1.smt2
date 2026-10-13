;; a quantifier-free solution is enough for this one

(set-logic HORN)

(declare-fun I ((Array Int Int) Int) Bool)

;; I(a, i) = exists j. 0 <= i <= j & a[i] = 0

;; a[i] = 0 => I(a, i, 0)
(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (and (>= i 0)
		      (= (select a i) 0))
		 (I a i))))

;; I(a, i) => I(a, i+1)
(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (I a i)
		 (I a (+ i 1)))))

(assert (forall ((a (Array Int Int)))
		(=>
		 (and
		  (I a 2)
		  (> (select a 0) 0)
		  (> (select a 1) 0)
		  (> (select a 2) 0))
		  false)))

(check-sat)
(get-model)
