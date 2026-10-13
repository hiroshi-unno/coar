(set-logic HORN)

;; I(A, i, m) means min(A[0..i]) = m
(declare-fun I ((Array Int Int) Int Int) Bool)

;;(define-fun I ((a (Array Int Int)) (i Int) (m Int)) Bool
;;	    (and (= (select a 0) m)
;;		 (=> (>= i 1) (= (select a i) 5))
;;		 (=> (< i 0) (= (select a i) 5))))

;;(define-fun I ((a (Array Int Int)) (i Int) (min Int)) Bool
;;	    (and (=> (not (= i 0)) (<= min (select a i)))
;;		 (=> (= i 0) (= min (select a i)))))

;; a[0] = min => I(a, 0, min)

(assert (forall ((a (Array Int Int)) (m Int))
		(=> (= (select a 0) m) (I a 0 m))))

;; I(a, i, min), a[i+1] < min => I(a, i+1, a[i+1])

(assert (forall ((a (Array Int Int)) (i Int) (m Int))
		(=>
		 (and (<= 0 i) (I a i m) (< (select a (+ i 1)) m))
		 (I a (+ i 1) (select a (+ i 1)))
		 )))

;; I(a, i, min), min <= a[i+1] => I(a, i+1, min)

(assert (forall ((a (Array Int Int)) (i Int) (m Int))
		(=>
		 (and (<= 0 i) (I a i m) (<= m (select a (+ i 1))))
		 (I a (+ i 1) m)
		 )))

;; min(A[0..0]) = 4, min(A[0..1]) = 0 => A[1] = 0

(assert (forall ((a (Array Int Int)) (i Int))
		(=> (I a 0 4) 
		    (= (select a 0) 4))))

(check-sat)
(get-model)

