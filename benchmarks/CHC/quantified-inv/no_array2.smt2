(declare-fun I (Int) Bool)

(assert (I 0))

(assert (forall ((i Int))
		(=> (I (+ i 2)) (I (+ i 4)))))

(assert (forall ((i Int))
		(=>
		 (and (I (+ i 1)) (I (+ i 2)))
		 false)))

(check-sat)
(get-model)
