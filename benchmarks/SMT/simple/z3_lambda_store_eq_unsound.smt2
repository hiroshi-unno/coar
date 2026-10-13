; Z3 5.1.0 answers sat; the two arrays differ at index 0 (0 against 3), so the
; answer is unsat.  The same equality asked extensionally,
; (forall ((x Int)) (= (ite (= x 7) 0 x) (ite (= x 7) 0 3))), is answered unsat.
; expect unsat
(assert (= (store (lambda ((x Int)) x) 7 0) (store ((as const (Array Int Int)) 3) 7 0)))
(check-sat)
