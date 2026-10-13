(set-logic HORN)

(declare-fun I ((Array Int Int) (Array Int Int) Int) Bool)

;;(define-fun I ((a (Array Int Int))
;;	       (b (Array Int Int))
;;	       (i Int)) Bool
;;	       (= (select a (+ (select b i) i)) i))

;; I(a, b, i) = a[b[i]+i] == i

(assert (forall
	 ((a (Array Int Int)) (b (Array Int Int)) (i Int))
	 (=>
	  (= (select a (select b 0)) 0)
	  (I a b 0))))

;; I(a, b, i), a[b[i+1]+i+1] == i+1 => I(a, b, i+1)

(assert (forall
	 ((a (Array Int Int)) (b (Array Int Int)) (i Int))
	 (=>
	  (and
	   (I a b i)
	   (=
	    (select a (+ (select b (+ i 1)) (+ i 1)))
	    (+ i 1)))
	  (I a b (+ i 1)))))

;; I(a, b, i), b[i] < 0 => false

(assert (forall
	 ((a (Array Int Int)) (b (Array Int Int)) (i Int))
	 (=>
	  (and 
	   (I a b 5)
	   (= (select b 5) i)
	   (not (= (select a (+ i 5)) 5))
	   )
	  false)))

(check-sat)
(get-model)

		

