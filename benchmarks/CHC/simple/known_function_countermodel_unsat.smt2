(set-logic HORN)
(declare-sort X 0)
(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (hd T) (tl (List T)))))))
(define-fun-rec length ((x (List X))) Int (ite ((_ is nil) x) 0 (+ 1 (length (tl x)))))
(declare-fun p ((List X)) Bool)
(assert (forall ((l (List X))) (p l)))
; A cons is not always of length at least 2: the one-element list l = cons(a, nil) is a
; countermodel, and length evaluates to 1 there by its definition.
(assert (forall ((l (List X))) (=> (and (p l) ((_ is cons) l)) (>= (length l) 2))))
(check-sat)
