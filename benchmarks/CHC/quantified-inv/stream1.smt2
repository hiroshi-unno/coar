(set-logic HORN)

;; (set-logic AUFLIA)

;; (set-logic ALL)

;; I(A) <=> [..., -1, -1, 1, 1, ...]
(declare-fun I ((Array Int Int)) Bool)

;;(define-fun I ((A (Array Int Int))) Bool
;;	    (exists ((idx Int))
;;		    (forall ((i Int))
;;			    (ite (>= i idx)
;;				 (= (select A i) 1)
;;				 (= (select A i) (- 1))))))

;;(define-fun I ((A (Array Int Int))) Bool
;;	    (forall ((idx Int))
;;		    (and (=> (>= idx 0) (= (select A idx) 1))
;;			 (=> (<  idx 0) (= (select A idx) (- 1))))))

(assert (I (lambda ((idx Int)) (ite (>= idx 0) 1 (- 1)))))

;; (assert (I ((as const (Array Int Int)) 1)))

;; (assert (I ((as const (Array Int Int)) (- 1))))

;; (assert (exists ((A (Array Int Int))) (I A)))

;; (assert (forall ((A (Array Int Int)))
;;		(=> (I A) (= (select A 0) 1))))

;;(assert (forall ((A (Array Int Int)))
;;		(=> (I A) (= (select A (- 1)) (- 1)))))

;; I(A), A[i] = 1 => A[i+1] = 1
(assert (forall ((A (Array Int Int)) (i Int))
		(=> (and (I A) (= (select A i) 1))
		    (= (select A (+ i 1)) 1))))

;; I(A), A[i] = -1 => A[i-1] = -1
(assert (forall ((A (Array Int Int)) (i Int))
		(=> (and (I A) (= (select A i) (- 1)))
		    (= (select A (- i 1)) (- 1)))))

;;(assert (forall ((A (Array Int Int)))
;;		(=> (I A) (= (select A 0) 1))))

;;(assert (forall ((A (Array Int Int)))
;;		(=> (I A) (= (select A (- 1)) (- 1)))))

;; (declare-const A (Array Int Int))
;; (assert (I A))

(check-sat)
;; (get-model)
;; (get-info :reason-unknown)
