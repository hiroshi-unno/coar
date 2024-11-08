(set-logic HORN)

(declare-sort X 0)
(declare-datatypes (T) ((List nil (cons (hd T) (tl (List))))))
(define-fun-rec defined_length ((x (List X))) Int (
     ite ((_ is nil) x) 0 (+ (defined_length (tl x)) 1)
))
(set-info defined_length (forall ((x (List X)))
  (or ((_ is nil) x) (> (defined_length x) 0))
))

(declare-fun length ((List X) Int) Bool)

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
    (and
        (length l ret)
    )
    (>= ret 0)
)))

(check-sat)
(exit)