(assert
	(forall ((x Int) (y Int))
		(exists ((z Int))
			(and
				(<= x z)
				(<= y z)
				(forall ((w Int))
					(=> (and (<= x w) (<= y w)) (<= z w))
				)
			)
		)
	)
)
