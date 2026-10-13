;; (set-logic HORN)

;; (declare-fun S ((Array Int Int) Int) Bool)

(define-fun S ((a (Array Int Int)) (N Int)) Bool
	    (exists ((i Int))
		    (and
		     (<= 0 i)
		     (< i N)
		     (> (select a i) (select a (+ i 1))))))

;; 0 <= i, i+1 <= N, a[i] > a[i+1] => S(A, N)

(assert (forall ((a (Array Int Int)) (N Int) (i Int))
		(=>
		 (and
		  (<= 0 i)
		  (< i N)
		  (> (select a i) (select a (+ i 1))))
		 (S a N))))

(declare-fun T ((Array Int Int) Int) Bool)

;; T(a, i), a[i] <= a[i+1] -> T(a, i+1)

(assert (forall ((a (Array Int Int)))
		(=>
		 (<= (select a 0) (select a 1))
		 (T a 1))))

(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (and
		  (<= 0 i)
		  (T a i)
		  (<= (select a i) (select a (+ i 1))))
		 (T a (+ i 1)))))

(assert (forall ((a (Array Int Int)) (N Int))
		(=>
		 (and
		  (S a N)
		  (T a N))
		 false)))

(check-sat)
(get-info :reason-unknown)
(get-model)

		
