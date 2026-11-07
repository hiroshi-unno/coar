; P is functional with no argument and a list result: P holds of exactly one
; list, which must be a cons with head 1.  The tail is unconstrained, so
; cons(1, l) for any l is a witness: sat.
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-fnp P (Lst) Bool)
(assert (forall ((l Lst)) (=> (P l) (and ((_ is cons) l) (= (hd l) 1)))))
(check-sat)
