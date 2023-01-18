(set-logic HORN)
(declare-fun triple (Int Int) Bool)

(assert (forall ((n Int) (r Int) (s Int))
   (=> (and (triple n r) (triple n s))
       (= r s))))

(assert (forall ((m Int))
   (=> (= m 0)
       (triple m m))))
       
(assert (forall ((n Int) (r Int))
   (=> (and (> n 0) (triple (- n 1) r))
       (triple n (+ r 3)))))

(check-sat)
(get-model)
