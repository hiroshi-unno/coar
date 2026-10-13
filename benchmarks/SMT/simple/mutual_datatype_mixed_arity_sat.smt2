; Parametric mutually recursive datatypes: coherent member instances throughout the recursive group.
(declare-datatypes ((A 0) (B 1)) (((anil) (acons (ab (B Bool)))) (par (T) ((bnil) (bcons (value T) (ba A))))))
(declare-const a0 A)
(declare-const a1 A)
(assert (distinct a0 a1))
(check-sat)
