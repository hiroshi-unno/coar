(set-logic HORN)

;; I(a, i, bound) = forall j. 0 <= j <= i -> a[j] <= bound
(declare-fun I ((Array Int Int) Int Int) Bool)

;; solution
;; (define-fun I ((a (Array Int Int))
;;	       (N Int)
;;	       (bound Int)) Bool
;;	       (forall ((i Int))
;;		       (=>
;;			(and (<= 0 i) (<= i N))
;;			(<= (select a i) bound))))
			

;; a[0] <= bound => I(a, 0, bound)
(assert (forall ((a (Array Int Int)) (bound Int))
                (=> (<= (select a 0) bound) (I a 0 bound))))

;; I(a, i, bound), a[i+1] <= bound => I(a, i+1, bound)

(assert (forall ((a (Array Int Int)) (i Int) (bound Int))
                (=>
                 (and (I a i bound) (<= (select a (+ i 1)) bound))
                 (I a (+ i 1) bound))))

;; 0 <= j <= i, I(a, i, bound), a[j] > bound -> false

(assert (forall ((a (Array Int Int)) (i Int) (j Int) (bound Int))
		(=>
		 (and (<= 0 j) (<= j i)
		      (I a i bound)
		      (> (select a j) bound))
		 false)))

(check-sat)
(get-model)
