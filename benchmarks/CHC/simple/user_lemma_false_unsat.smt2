; The lemma below is false (length nil is 0), so it must not be assumed: assumed,
; it would make P := false a solution.  P holds of length nil, which is 0, so the
; problem is unsatisfiable.
(set-logic HORN)
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(define-fun-rec length ((x List)) Int
  (ite ((_ is nil) x) 0 (+ 1 (length (tail x)))))
(define-fun length_negative ((y List)) Bool (< (length y) 0))
(set-info :lemma length_negative)
(declare-fun P (Int) Bool)
(assert (forall ((x List)) (P (length x))))
(assert (forall ((n Int)) (=> (P n) (< n 0))))
(check-sat)
