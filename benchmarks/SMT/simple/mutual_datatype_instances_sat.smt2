; Parametric mutually recursive datatypes: sat with both bindings; formerly failed on inconsistent sibling definitions.
(declare-datatypes ((A 1) (B 1)) ((par (T) ((anil) (acons (ab (B T))))) (par (U) ((bnil) (bcons (ba (A U)))))))
(declare-const a0 (A Int))
(declare-const a1 (A Int))
(assert (distinct a0 a1))
(check-sat)
