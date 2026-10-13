(set-logic HORN)

;;(define-fun I ((a (Array Int Int)) (i Int)) Bool
;;	    (= (select a i) i))

(declare-fun I ((Array Int Int) Int) Bool)

;; a[0] = 0 => I(a, 0)
(assert (forall ((a (Array Int Int)) (i Int))
		(=> (= (select a 0) 0)
		    (I a 0))))

;; I(a, i), a[i+1] = i+1 => I(a, i+1)
(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (and (I a i)
		      (= (select a (+ i 1)) (+ i 1)))
		 (I a (+ i 1)))))

;; I(a, i), a[i] > i => false
(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (and (I a i)
		      (> (select a i) i))
		 false)))

(check-sat)
(get-model)

