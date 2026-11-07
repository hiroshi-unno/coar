(set-logic HORN)
(declare-sort X 0)
(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (hd T) (tl (List T)))))))
(define-fun-rec len ((x (List X))) Int (ite ((_ is nil) x) 0 (+ 1 (len (tl x)))))
(declare-fun p ((List X)) Bool)
(assert (forall ((l (List X))) (p l)))
; false in any background where hd nil is the list's only element
(assert (forall ((l (List X))) (=> (and (p l) (= (len l) 1)) (not (= (hd l) (hd (as nil (List X))))))))
(check-sat)
