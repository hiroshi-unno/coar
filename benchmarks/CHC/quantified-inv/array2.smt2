(set-logic HORN)

(declare-fun I ((Array Int Int) Int) Bool)

;; a[0] = 0 => I(a, 0)

(assert (forall ((a (Array Int Int)))
		(=> (= (select a 0) 0) (I a 0))))

;; i <= 0, I(a, i), a[i]+2 <= a[i+1] => I(a, i+1)

(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (and (<= 0 i) (I a i) (<= (+ (select a i) 2) (select a (+ i 1))))
		 (I a (+ i 1)))))


;; i = k, I(a, k) => a[k] = 2*k
(assert (forall ( (a (Array Int Int)) (k Int) )
		(=>
		 (I a k)
		 (>= (select a k) k))))

(check-sat)
(get-model)
