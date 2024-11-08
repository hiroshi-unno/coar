(set-logic HORN)

(declare-sort Int 0)
(declare-datatypes (T) ((List (nil) (cons (hd T) (tl List)))))

(declare-fun exists$ ((List Int) Bool) Bool)
(define-fun p ((x Int)) Bool (
    > x 0
))

(assert (forall ((l (List Int)) (var73 Bool))
    (=>
        (and
            (= l nil)
            (not var73)
        )
        (exists$ l var73)
    )
))

(assert (forall ((l (List Int)) (var79 (List Int)) (var78 Int) (_v53 Bool))
    (=>
        (and 
            _v53
            (= l (cons var78 var79))
            (exists$ var79 true)
        )
        (exists$ l _v53)
    )
))


(assert (forall ((l (List Int)) (var79 (List Int)) (var78 Int) (_v53 Bool))
    (=>
        (and 
            _v53
            (= l (cons var78 var79))
            (exists$ var79 false)
            (p var78)
        )
        (exists$ l _v53)
    )
))

(assert (forall ((l (List Int)) (var79 (List Int)) (var78 Int) (_v53 Bool))
    (=>
        (and 
            (not _v53)
            (= l (cons var78 var79))
            (exists$ var79 false)
            (not (p var78))
        )
        (exists$ l _v53)
    )
))

(assert (forall ((l1 (List Int)) (l2 (List Int)) )
    (=>
        (and
            (exists$ l1 true)
            (exists$ l2 false)
            
        )   
        (not (= l1 l2))
    )

))

(check-sat)
(exit)