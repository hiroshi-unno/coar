; Parametric mutually recursive datatypes: coherent member instances throughout the recursive group.
(declare-datatypes ((A 2) (B 2)) ((par (T U) ((anil) (acons (av T) (ab (B U T))))) (par (X Y) ((bnil) (bcons (bv X) (ba (A Y X)))))))
(declare-const a0 (A Int Bool))
(declare-const a1 (A Int Bool))
(assert (distinct a0 a1))
(check-sat)
