(set-logic HORN)
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(define-fun-rec len ((l L)) Int (ite ((_ is nil) l) 0 (+ 1 (len (tl l)))))
(declare-fun p (L) Bool)
(assert (forall ((l L)) (p l)))
; valid: if every k exceeds hd (tl l) then so does hd (tl l) + 1 ... read at
; k := hd (tl l) the premise is false
(assert (forall ((l L)) (=> (and (p l) (= (len l) 1) (forall ((k Int)) (> k (hd (tl l))))) false)))
(check-sat)
