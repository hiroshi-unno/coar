; Parametric mutually recursive datatypes: the complete mutual group must retain Bool-valued selectors.
(declare-datatypes ((A 1) (B 1)) ((par (T) ((anil) (acons (av T) (ab (B T))))) (par (U) ((bnil) (bcons (bv U) (ba (A U)))))))
(declare-const a0 (A Bool))
(declare-const a1 (A Bool))
(declare-const a2 (A Bool))
(assert (distinct (av a0) (av a1) (av a2)))
(check-sat)
