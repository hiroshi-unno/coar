(set-logic HORN)

;; I(A, N) := forall i, j. (0 <= j < i <= N) -> A[i] != A[j]
;;
;; I.e., an array A has no duplicate items in the range [0, N]

(declare-fun I ((Array Int Int) Int) Bool)

;; solution
;; (define-fun I ((a (Array Int Int)) (N Int)) Bool
;;	    (forall ((i Int) (j Int))
;;		    (=>
;;		     (and (<= 0 j) (< j i) (<= i N))
;;		     (not (= (select a i) (select a j))))))

;; I(a, 0)
(assert (forall ((a (Array Int Int))) (I a 0)))

;; I(a, i), 0 <= j < i, a[i] = a[j] -> false
(assert (forall ((a (Array Int Int)) (i Int) (j Int))
		(=>
		 (and (I a i) (<= 0 j) (< j i) (= (select a i) (select a j)))
		 false)))

;; I(a, i), (forall j. 0 <= j < i -> A[i] != A[j]) -> I(a, i+1)

(assert (forall ((a (Array Int Int)) (i Int))
		(=> (and
		     (I a i)
		     (forall ((j Int)) (=> (and (<= 0 j) (< j i))
					   (not (= (select a i) (select a j))))))
		    (I a (+ i 1)))))

(check-sat)
