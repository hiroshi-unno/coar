;; not solved -- but see below
;; it is solved after all; it just takes a while

(set-logic HORN)

;; I(A, i, m) means min(A[0..i]) = m
(declare-fun I ((Array Int Int) Int Int) Bool)

;; (define-fun I ((a (Array Int Int)) (i Int) (min Int)) Bool
;;	    (and
;;	     (>= i 0)
;;	     (forall ((j Int))
;;		     (=> (<= j i) (>= (select a j) min)))
;;	     (exists ((j Int))
;;		     (and
;;		      (<= j i)
;;		      (= (select a j) min)))))

;; a[0] = min => I(a, 0, min)

(assert (forall ((a (Array Int Int)) (min Int))
		(=> (= (select a 0) min) (I a 0 min))))

;; I(a, i, min), a[i+1] < min => I(a, i+1, a[i+1])

(assert (forall ((a (Array Int Int)) (i Int) (min Int))
		(=>
		 (and (I a i min) (< (select a (+ i 1)) min))
		 (I a (+ i 1) (select a (+ i 1)))
		 )))

;; I(a, i, min), min <= a[i+1] => I(a, i+1, min)

(assert (forall ((a (Array Int Int)) (i Int) (min Int))
		(=>
		 (and (I a i min) (<= min (select a (+ i 1))))
		 (I a (+ i 1) min)
		 )))

;; a predicate that is true of everything would satisfy the clauses above,
;; which is not wanted, so a clause that plainly rules it out is added
;; min(A[0..0]) = m+1, min(A[0..1]) = m => A[1] = m
(assert (forall ((a (Array Int Int)) (i Int) (m Int))
 		(=> (and (I a 0 (+ m 1)) (I a 1 m))
		    (= (select a 1) m)))) 

(check-sat)
(get-model)


