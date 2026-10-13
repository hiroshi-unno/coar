(set-logic HORN)

;; I(a, b, N) = forall i. 0 <= i <= N -> a[i] = b[i]
(declare-fun I ((Array Int Int) (Array Int Int) Int) Bool)

;; solution
;; (define-fun I ((a (Array Int Int)) (b (Array Int Int)) (N Int)) Bool
;;	    (forall ((i Int))
;;		    (=> (and (<= 0 i) (<= i N))
;;			(= (select a i) (select b i)))))

;; a[0] = b[0] => I(a, b, 0)
(assert (forall ((a (Array Int Int)) (b (Array Int Int)))
                (=> (= (select a 0) (select b 0))
		    (I a b 0))))

;; I(a, b, i), a[i+1] = b[i+1] => I(a, b, i+1)
(assert (forall ((a (Array Int Int)) (b (Array Int Int)) (i Int))
		(=> (and (I a b i)
			 (= (select a (+ i 1)) (select b (+ i 1))))
		    (I a b (+ i 1)))))

;; I(a, b, N), i <= N, a[i] != b[i] => false
(assert (forall ((a (Array Int Int)) (b (Array Int Int)) (N Int) (i Int))
		(=>
		 (and (I a b N) (<= 0 i) (<= i N)
		      (not (= (select a i) (select b i))))
		 false)))

(check-sat)

		    
