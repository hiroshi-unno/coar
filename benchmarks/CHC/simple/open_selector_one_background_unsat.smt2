(set-logic HORN)
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(define-fun-rec len ((l L)) Int (ite ((_ is nil) l) 0 (+ 1 (len (tl l)))))
(declare-fun p (L) Bool)
(assert (forall ((l L)) (=> (= (len l) 1) (p l))))
; in a background with hd nil = 5 the one-element lists are forced into p and
; the goal fails: unsat under the per-background reading
(assert (forall ((l L)) (=> (and (p l) (= (len l) 1)) (not (= (hd (tl l)) 5)))))
(check-sat)
