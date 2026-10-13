(set-logic HORN)

;; J(a, i, v) = forall j. 0 <= j <= i -> a[j] != v
;; (declare-fun J ((Array Int Int) Int Int) Bool)

(define-fun J ((a (Array Int Int)) (i Int) (v Int)) Bool
	    (forall ((j Int))
		    (=>
		     (and (<= 0 j) (<= j i))
		     (not (= (select a j) v)))))

;; a[0] != v -> J(a, 0, v)
(assert (forall ((a (Array Int Int)) (v Int))
		(=> (not (= (select a 0) v))
		    (J a 0 v))))

;; J(a, i, v), a[i+1] != v -> J(a, i+1, v)
(assert (forall ((a (Array Int Int)) (i Int) (v Int))
		(=>
		 (and (J a i v) (not (= (select a (+ i 1)) v)))
		 (J a (+ i 1) v))))

;; J(a, i, v), 0 <= j <= i, a[j] = v -> false
(assert (forall ((a (Array Int Int)) (i Int) (j Int) (v Int))
		(=>
		 (and (J a i v) (<= 0 j) (<= j i) (= (select a j) v))
		 false)))


;; I(A, N) := forall i, j. (0 <= j < i <= N) -> A[i] != A[j]
;;
;; I.e., an array A has no duplicate items in the range [0, N]
;; (declare-fun I ((Array Int Int) Int) Bool)

(define-fun I ((a (Array Int Int)) (N Int)) Bool
	    (forall ((i Int) (j Int))
		    (=>
		     (and
		      (<= 0 j) (< j i) (<= i N))
		     (not (= (select a i) (select a j))))))

;; I(a, 0)
(assert (forall ((a (Array Int Int))) (I a 0)))

;; I(a, i), (forall j. 0 <= j < i -> A[i] != A[j]) -> I(a, i+1)
;; I(a, i), J(a, i, a[i+1]) -> I(a, i+1)

(assert (forall ((a (Array Int Int)) (i Int))
		(=> (and
		     (I a i)
		     (J a i (select a (+ i 1))))
		    (I a (+ i 1)))))

;; I(a, i), 0 <= j < i, a[i] = a[j] -> false
(assert (forall ((a (Array Int Int)) (i Int) (j Int))
		(=>
		 (and (I a i) (<= 0 j) (< j i) (= (select a i) (select a j)))
		 false)))

(check-sat)
