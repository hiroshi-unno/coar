(set-logic HORN)

;; I(A) := A = [0, 1, 0, 1, 0, 1, ...]
(declare-fun I ((Array Int Int) Int) Bool)

;; A[0] = 0 => I(A, 0)
(assert (forall ((a (Array Int Int)))
		(=> (= (select a 0) 0)
		    (I a 0))))

;; A[1] = 1 => I(A, 1)
(assert (forall ((a (Array Int Int)))
		(=> (= (select a 1) 0)
		    (I a 1))))

;; I(A, i), A[i] = 0 => A[i+2] = 0
(assert (forall ((a (Array Int Int)) (i Int))
		(=> (and (I a i) (= (select a i) 0))
		    (= (select a (+ i 2)) 0))))
	
;; I(A, i), A[i] = 1 => A[i+2] = 1
(assert (forall ((a (Array Int Int)) (i Int))
		(=> (and (I a i) (= (select a i) 1))
		    (= (select a (+ i 2)) 1))))

(check-sat)
(get-model)


	
