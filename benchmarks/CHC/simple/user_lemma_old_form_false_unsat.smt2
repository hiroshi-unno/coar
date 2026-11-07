; The same problem with the false lemma written in the older, non-standard form
; (set-info f <formula>), which z3 and cvc5 refuse: it must not be assumed
; either; P holds of length nil, which is 0, so the problem is unsatisfiable.
(set-logic HORN)
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(define-fun-rec length ((x List)) Int
  (ite ((_ is nil) x) 0 (+ 1 (length (tail x)))))
(set-info length (forall ((y List)) (< (length y) 0)))
(declare-fun P (Int) Bool)
(assert (forall ((x List)) (P (length x))))
(assert (forall ((n Int)) (=> (P n) (< n 0))))
(check-sat)
