(set-logic HORN)
(declare-fun I ((Array Int Int) Int Int Int) Bool)

(assert (forall ((a (Array Int Int)) (N Int))
		(=> true (I a 0 7 N))))

;; idx     0 1 2 3      val-1 val val+1              N N<
;; array [ 0 1 2 3 ... (val-1) 0 (val+1) (val+2) ... | do not touch ]
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

;; Enlarging positive examples, we eventually find the following:
;; I(a = [0, 1, 2, 3, 4, 5, 6, 0, 8], i = 9, val = 7, N = 8) (#)
;; Then, take i1 = 8, a[i1 = 8] = 8 > val = 7 in the following clause.

(assert (forall ((a (Array Int Int)) (i Int) (val Int) (N Int) (i1 Int))
		(=> (and (I a i val N) (> i N) (<= 0 i1) (<= i1 N) (> (select a i1) val))
		    false)))

(check-sat)
