;; (set-logic HORN)
(set-logic AUFNIRA)

;; I(A) := A = [0, 1, 0, 1, 0, 1, ...]
(declare-fun I ((Array Int Int)) Bool)

;; (define-fun I ((a (Array Int Int))) Bool
;;	    (forall ((idx Int))
;;		    (ite (= (mod idx 2) 0) (= (select a idx) 0) (= (select a idx) 1))))

;;(define-fun I ((a (Array Int Int))) Bool
;;	    (= a
;;	       (lambda ((idx Int)) (ite (= (mod idx 2) 0) 0 1))))

;; exists A. I(A)
(assert (I (lambda ((idx Int)) (ite (= (mod idx 2) 0) 0 1))))

;; I(A), A[i] = 0 => A[i+2] = 0
(assert (forall ((a (Array Int Int)) (i Int))
		 (=> (and (I a) (= (select a i) 0))
		     (= (select a (+ i 2)) 0))))

;; I(A), A[i] = 0 => A[i-2] = 0
(assert (forall ((a (Array Int Int)) (i Int))
		 (=> (and (I a) (= (select a i) 0))
		     (= (select a (- i 2)) 0))))
	
;; I(A), A[i] = 1 => A[i+2] = 1
(assert (forall ((a (Array Int Int)) (i Int))
		 (=> (and (I a) (= (select a i) 1))
		     (= (select a (+ i 2)) 1))))

;; I(A), A[i] = 1 => A[i-2] = 1
(assert	(forall ((a (Array Int Int)) (i Int))
		 (=> (and (I a) (= (select a i) 1))
		     (= (select a (- i 2)) 1))))

(check-sat)
;; (get-model)
(get-info :reason-unknown)

