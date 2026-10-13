;; (set-logic HORN)

;; (set-logic ALIA)

(declare-fun E ((Array Int Int) Int) Bool)

;;(define-fun E ((a (Array Int Int)) (N Int)) Bool
;;	    (exists ((i Int))
;;		    (and (<= 0 i) (<= i N) (= (select a i) 0))))

;; (declare-fun A ((Array Int Int) Int) Bool)
(define-fun A ((a (Array Int Int)) (i Int)) Bool
	    (forall ((j Int))
		    (=>
		     (and (<= 0 j) (<= j i))
		     (not (= (select a j) 0)))))

;; 0 <= i <= N, a[i] = 0 -> E(a, N)

(assert (forall ((a (Array Int Int)) (i Int) (N Int))
		(=>
		 (and
		  (<= 0 i)
		  (<= i N)
		  (= (select a i) 0))
		 (E a N))))

;; a[0] != 0 -> A(a, 0)

(assert (forall ((a (Array Int Int)) (N Int))
		(=>
		 (not (= (select a 0) 0))
		 (A a 0))))

;; A(a, i), a[i+1] != 0 -> A(a, i+1)
(assert (forall ((a (Array Int Int)) (i Int))
		(=>
		 (and
		  (A a i)
		  (not (= (select a (+ i 1)) 0)))
		 (A a (+ i 1)))))

(assert (forall ((a (Array Int Int)) (N Int))
		(=>
		 (and
		  (>= N 0)
		  (A a N)
		  (E a N))
		 false)))

(check-sat)
(get-info :reason-unknown)
(get-model)
