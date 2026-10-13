; Parametric mutually recursive datatypes: coherent member instances throughout the recursive group.
(declare-datatypes ((A 1) (B 1) (C 1)) ((par (T) ((anil) (acons (ab (B T))))) (par (U) ((bnil) (bcons (bc (C U))))) (par (V) ((cnil) (ccons (ca (A V)))))))
(declare-const a0 (A Int))
(declare-const a1 (A Int))
(assert (distinct a0 a1))
(check-sat)
