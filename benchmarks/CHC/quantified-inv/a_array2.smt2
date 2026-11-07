;; sat: I(a, N) = forall i. 0 <= i <= N -> a[i] = 0 and
;; J(a, b, N, k) = forall i. 0 <= i <= N -> a[i] = 42 satisfy every clause.
;; They still do if either query's comparison is replaced by <, != or >.

(set-logic HORN)

;; I(a, N) <=> forall i in [0..N]. a[i] = 0
(declare-fun I ((Array Int Int) Int) Bool)

(declare-fun J ((Array Int Int) (Array Int Int) Int Int) Bool)

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

(assert (forall ((a (Array Int Int)))
		(=>
		 (= (select a 0) 42)
		 (J a a 0 0))))

;; i >= 0, I(a, i), a[i+1] = 0 => I(a, i+1)
(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (and
		  (>= i 0)
		  (I a i)
		  (= (select a (+ i 1)) 0))
		 (I a (+ i 1)))))

(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (and
		  (>= i 0)
		  (J a a i i)
		  (= (select a (+ i 1)) 42))
		 (J a a (+ i 1) i))))

;; 0 <= j <= i, I(a, i), a[j] != 0 => false
(assert (forall ((a (Array Int Int)) (i Int) (j Int))
		(=>
		 (and
		  (<= 0 j)
		  (<= j i)
		  (I a i)
		  (< (select a j) 0))
		 false)))

(assert (forall ((a (Array Int Int)) (i Int) (j Int) (k Int))
		(=>
		 (and
		  (<= 0 j)
		  (<= j i)
		  (J a a i k)
		  (> (select a j) 42))
		 false)))

(check-sat)
(get-model)

