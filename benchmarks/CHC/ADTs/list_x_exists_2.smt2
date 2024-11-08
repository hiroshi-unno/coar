(set-logic HORN)

(declare-sort X 0)
(declare-datatypes (T) ((List nil (cons (hd T) (tl (List))))))

(declare-fun p (X) Bool)
(declare-fun exists ((List X) Bool) Bool)

(assert (forall ((l (List X)) (var73 Bool) )
    (=>
        (and 
            (not var73) 
            ((_ is nil) l)
        )
        (exists l var73)
    )
))

(assert (forall ( (l (List X)) (var79 (List X)) (var78 X) (_v53 Bool) )
    (=>
        (and
            (exists var79 true)
            (and 
                _v53
                (= l (cons var78 var79))
            )
        )
        (exists l _v53)
    )
))

(assert (forall ( (l (List X)) (var79 (List X)) (var78 X) (_v53 Bool) )
    (=>
        (and
            (exists var79 false)
            (and
                _v53
                (= l (cons var78 var79))
                (p var78)
            )
        )
        (exists l _v53)
    )
))

(assert (forall ( (l (List X)) (var79 (List X)) (var78 X) (_v53 Bool) )
    (=>
        (and
            (exists var79 false)
            (and
                (not _v53)
                (= l (cons var78 var79))
                (not (p var78))
            )
        )
        (exists l _v53)
    )
))

(assert (forall ( (l1 (List X)) (l2 (List X)) )
    (=>
        (and
            (not (= l1 nil))
            (exists l1 true)
        )
        (p (hd l1))
    )

))

(check-sat)
(exit)