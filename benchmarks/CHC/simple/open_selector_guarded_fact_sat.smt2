(set-logic HORN)
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(define-fun-rec len ((l L)) Int (ite ((_ is nil) l) 0 (+ 1 (len (tl l)))))
(declare-fun p (L) Bool)
; the fact forces p only on the one-element list holding hd nil, whose value
; the background chooses; p := len l = 1 meets both clauses in every background
(assert (forall ((l L)) (=> (and (= (len l) 1) (= (hd l) (hd (tl l)))) (p l))))
(assert (forall ((l L)) (=> (p l) (= (len l) 1))))
(check-sat)
