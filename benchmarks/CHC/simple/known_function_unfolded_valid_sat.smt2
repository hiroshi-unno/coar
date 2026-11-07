(set-logic HORN)
(declare-sort X 0)
(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (hd T) (tl (List T)))))))
(define-fun-rec length ((x (List X))) Int (ite ((_ is nil) x) 0 (+ 1 (length (tl x)))))
(declare-fun p ((List X)) Bool)
(assert (forall ((l (List X))) (p l)))
; A one-element list has length 1, by unfolding the definition twice.
(assert (forall ((l (List X))) (=> (and (p l) ((_ is cons) l) ((_ is nil) (tl l))) (= (length l) 1))))
(check-sat)
