(set-logic HORN)
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(define-fun-rec len ((l L)) Int (ite ((_ is nil) l) 0 (+ 1 (len (tl l)))))
(declare-fun p (L) Bool)
; in a background with hd nil = 3 the fact forces p (cons 3 nil), which the
; goal forbids: unsat under the per-background reading
(assert (forall ((l L)) (=> (and (= (len l) 1) (= (hd l) (hd (tl l)))) (p l))))
(assert (forall ((l L)) (=> (p l) (not (= (hd l) 3)))))
(check-sat)
