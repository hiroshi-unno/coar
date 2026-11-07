(set-logic HORN)
(declare-datatypes ((W 0)) (((mk (arr (Array Int Int))))))
(declare-datatypes ((L 0)) (((nil) (cons (hd W) (tl L)))))
(define-fun-rec cnt ((n Int)) Int (ite (<= n 0) 0 (+ 1 (cnt (- n 1)))))
(declare-fun p (Int) Bool)
(assert (forall ((n Int)) (p n)))
; as lambda_record_open_selector_valid_sat, with a known function in the clause
(assert (forall ((n Int)) (=> (and (p n) (>= n 0) (= (cnt n) n) (= (hd nil) (mk (store (lambda ((x Int)) x) 7 0)))) (not (= (hd nil) (mk (store ((as const (Array Int Int)) 3) 7 0)))))))
(check-sat)
