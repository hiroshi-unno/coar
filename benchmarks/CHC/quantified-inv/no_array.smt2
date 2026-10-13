(declare-fun I (Int) Bool)

(assert (I 0))

(assert (forall ((i Int))
		(=> (I i) (I (+ i 2)))))

(assert (forall ((i Int))
		(=>
		 (and (I i) (I (+ i 1)))
		 false)))

(check-sat)
(get-model)

