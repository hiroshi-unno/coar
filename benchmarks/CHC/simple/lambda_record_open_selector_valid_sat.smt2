(set-logic HORN)
(declare-datatypes ((W 0)) (((mk (arr (Array Int Int))))))
(declare-datatypes ((L 0)) (((nil) (cons (hd W) (tl L)))))
(declare-fun p (Int) Bool)
(assert (forall ((n Int)) (p n)))
; hd nil is open, but it cannot equal both records: mk is injective and the
; two arrays differ at index 0 (0 against 3).  Valid in every model: sat.
(assert (forall ((n Int)) (=> (and (p n) (= (hd nil) (mk (store (lambda ((x Int)) x) 7 0)))) (not (= (hd nil) (mk (store ((as const (Array Int Int)) 3) 7 0)))))))
(check-sat)
