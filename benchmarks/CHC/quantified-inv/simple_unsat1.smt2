(declare-fun I ((Array Int Int)) Bool)

(assert (forall ((i Int))
		(I (store (store ((as const (Array Int Int)) 0) 1 1) i i))))

(assert
 (=>
  (I (store (store ((as const (Array Int Int)) 0) 2 2) 1 1))
  false))

(check-sat)
