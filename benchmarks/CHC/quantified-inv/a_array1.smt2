;; pcsat answers unsat on this

(set-logic HORN)

;; I(a, N) <=> forall i in [0..N]. a[i] = 0
(declare-fun I ((Array Int Int) Int) Bool)

;;(define-fun I ((a (Array Int Int)) (N Int)) Bool
;;	    (forall ((i Int))
;;		    (=>
;;		     (and (<= 0 i) (<= i N))
;;		     (= (select a i) 0))))

;; a[0] = 0 => I(a, 0)
(assert (forall ((a (Array Int Int)))
		(=>
		 (= (select a 0) 0)
		 (I a 0))))

;; i >= 0, I(a, i), a[i+1] = 0 => I(a, i+1)
(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (and
		  (>= i 0)
		  (I a i)
		  (= (select a (+ i 1)) 0))
		 (I a (+ i 1)))))

;; 0 <= j <= i, I(a, i), a[j] != 0 => false
(assert (forall ((a (Array Int Int)) (i Int) (j Int))
		(=>
		 (and
		  (<= 0 j)
		  (<= j i)
		  (I a i)
		  (< (select a j) 0)) ;; with != or > this is unsat; with < it makes progress
		 false)))

(check-sat)
(get-model)

