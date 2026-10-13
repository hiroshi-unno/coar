(set-logic HORN)

(declare-fun I ((Array Int Int) Int Int Int) Bool)

;;(define-fun I ((a (Array Int Int)) (i Int) (val Int) (N Int)) Bool
;;	    (forall ((j Int))
;;		    (=>
;;		     (and (<= 0 j) (< j i) (<= j N))
;;		     (and
;;		      (=> (= j val) (= (select a j) 0))
;;		      (=> (not (= j val)) (= (select a j) j))))))

(assert (forall ((a (Array Int Int)) (N Int))
		(=> true (I a 0 7 N))))

;;idx     0 1 2 3      val-1 val val+1              N N<
;;array [ 0 1 2 3 ... (val-1) 0 (val+1) (val+2) ... | do not touch ]
;; I(a, i, val, N) = forall j. j < i <= N => ((j = val => a[j] = 0) /\ (j != val => a[j] = j)) (*)

(assert (forall ((a (Array Int Int))
		 (i Int)
		 (val Int)
		 (N Int)
		 (a1 (Array Int Int))
		 (i1 Int))
		(let ((a!1 (and (I a i val N)
				(<= i N)
				(= a1 (ite (= val i) (store a i 0) (store a i i)))
				(= i1 (+ i 1)))))
		  (=> a!1 (I a1 i1 val N)))))


;; I(a, i, val, N), i > N, a[val] != 0 => false
(assert (forall ((a (Array Int Int))
		 (i Int)
		 (val Int)
		 (N Int)
		 (j Int))
		(=>
		 (and (I a i val N) (<= 0 j) (<= j N) (< N i) (not (= j val)) (not (= (select a j) j)))
		 false)))

(check-sat)
(get-model)


