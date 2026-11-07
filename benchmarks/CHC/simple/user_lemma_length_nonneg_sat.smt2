; P must hold of the length of every list and only of non-negative integers, so
; the problem is satisfiable exactly when every list has a non-negative length,
; which needs induction.  The lemma states it in standard SMT-LIB: a Boolean
; define-fun named by (set-info :lemma ...), which other solvers skip.
(set-logic HORN)
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(define-fun-rec length ((x List)) Int
  (ite ((_ is nil) x) 0 (+ 1 (length (tail x)))))
(define-fun length_nonneg ((y List)) Bool (>= (length y) 0))
(set-info :lemma length_nonneg)
(declare-fun P (Int) Bool)
(assert (forall ((x List)) (P (length x))))
(assert (forall ((n Int)) (=> (P n) (>= n 0))))
(check-sat)
