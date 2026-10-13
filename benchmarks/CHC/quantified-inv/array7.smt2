(set-logic HORN)

;;(define-fun I ((a (Array Int Int)) (i Int)) Bool
;;	    (= (select a i) i))

(declare-fun I ((Array Int Int) Int) Bool)

;; a[1] = 1 => I(a, 1)
(assert (forall ((a (Array Int Int)) (i Int))
		(=> (= (select a 1) 1)
		    (I a 1))))

;; I(a, i), a[i] = i, a[i+1] = -(i+1) => I(a, i+1)
(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (and (I a i)
		      (= (select a i) i)
		      (= (select a (+ i 1)) (- (+ i 1))))
		 (I a (+ i 1)))))

;; I(a, i), a[i] = -i, a[i+1] = i+1 => I(a, i+1)
(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (and (I a i)
		      (= (select a i) (- i))
		      (= (select a (+ i 1)) (+ i 1)))
		 (I a (+ i 1)))))

;; I(a, i), I(a, i+1), a[i] > 0, a[i] + a[i+1] > 0 => false
(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (and (I a i)
		      (I a (+ i 1))
		      (> (select a i) 0)
		      (> (+ (select a i) (select a (+ i 1))) 0))
		 false)))

(check-sat)
(get-model)
