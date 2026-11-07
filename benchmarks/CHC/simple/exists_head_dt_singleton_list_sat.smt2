; An existential head over a list: for every x >= 0 some l is the singleton
; list cons(x, nil), a witness over the argument: sat.
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (>= x 0) (Q x))))
(assert (forall ((x Int)) (=> (Q x) (exists ((l Lst)) (and ((_ is cons) l) (= (hd l) x) ((_ is nil) (tl l)))))))
(check-sat)
