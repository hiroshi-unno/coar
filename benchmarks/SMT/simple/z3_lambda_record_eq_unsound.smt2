; Z3 5.1.0 answers sat; mk is the only constructor and injective, and the two
; arrays differ at index 0 (0 against 3), so no w equals both records and the
; answer is unsat.  Taken apart into (arr w) = ... and asked extensionally, it
; is answered unsat.
; expect unsat
(declare-datatypes ((W 0)) (((mk (arr (Array Int Int))))))
(declare-const w W)
(assert (= w (mk (store (lambda ((x Int)) x) 7 0))))
(assert (= w (mk (store ((as const (Array Int Int)) 3) 7 0))))
(check-sat)
