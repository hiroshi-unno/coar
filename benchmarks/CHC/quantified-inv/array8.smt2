(set-logic HORN)

;;(define-fun I ((a (Array Int Int)) (i Int) (m Int)) Bool
;;	    (and
;;	     (>= i 0)
;;	     (=> (= i 0) (= (select a 0) m))
;;	     (=> (> i 0)
;;		 (and
;;		  (=> (= (select a (- i 1)) m) (= (select a i) (- m)))
;;		  (=> (= (select a (- i 1)) (- m)) (= (select a i) m)))
;;		 )))

(declare-fun I ((Array Int Int) Int Int) Bool)

;; a[0] = m => I(a, 0, m)
(assert (forall ((a (Array Int Int)) (i Int) (m Int))
		(=> (= (select a 0) m)
		    (I a 0 m))))

;; I(a, i, m), a[i]+a[i+1]= 0 => I(a, i+1, m)
(assert (forall ((a (Array Int Int)) (i Int) (m Int))
		(=>
		 (and (I a i m)
		      (=
		       (+ (select a i) (select a (+ i 1)))
		       0))
		 (I a (+ i 1) m))))

;; I(a, i+1, m), a[i] = m, a[i+1] <> -m => false
(assert (forall ((a (Array Int Int)) (i Int) (m Int))
		(=>
		 (and (>= i 0)
		      (I a (+ i 1) m)
		      (= (select a i) m)
		      (not (= (select a (+ i 1)) (- m))))
		 false)))

(check-sat)
(get-model)
