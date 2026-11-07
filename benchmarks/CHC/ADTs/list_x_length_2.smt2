(set-logic HORN)

(declare-sort X 0)
(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (hd T) (tl (List T)))))))

(declare-fun length ((List X) Int) Bool)
(define-fun-rec defined_length ((x (List X))) Int (
     ite ((_ is nil) x) 0 (+ (defined_length (tl x)) 1)
))
; A law of defined_length: on a cons it is at least 1 (by induction on x, since defined_length is never
; negative).  Written as a lemma CoAR proves before it uses it; other solvers skip
; (set-info :lemma ...), so the problem is the same for them.
(define-fun defined_length_pos_on_cons ((x (List X))) Bool (or ((_ is nil) x) (> (defined_length x) 0)))
(set-info :lemma defined_length_pos_on_cons)
(assert (forall ((l (List X)) (var68 Int) )
(=>
    (and
        (= var68 0)
        ((_ is nil) l)
    )
    (length l var68)
)))

(assert (forall ((l (List X)) (_v27 Int) (_v24 Int) (var71 X) (var72 (List X)))
(=>
    (and
        (length var72 _v24)
        (= _v27 (+ 1 _v24))
        (= l (cons var71 var72))
    )
    (length l _v27)
)))

(assert (forall ((l (List X)) (ret Int) (x X))
(=>
    (length l ret)
    (> ret 0)
)))

(check-sat)
(exit)