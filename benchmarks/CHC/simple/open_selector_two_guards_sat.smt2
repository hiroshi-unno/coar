(set-logic HORN)
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(define-fun-rec len ((l L)) Int (ite ((_ is nil) l) 0 (+ 1 (len (tl l)))))
(declare-fun p (L) Bool)
; positives on the one-element list holding hd nil, negatives on one holding
; hd nil + 1: never the same list in one background, so p := (hd l = hd (tl l))
; restricted to length 1 is a solution in every background
(assert (forall ((l L)) (=> (and (= (len l) 1) (= (hd l) (hd (tl l)))) (p l))))
(assert (forall ((l L)) (=> (and (p l) (= (len l) 1) (= (hd l) (+ (hd (tl l)) 1))) false)))
(check-sat)
