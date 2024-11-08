(set-logic HORN)

(declare-sort X 0)
(declare-datatypes (T) ((List nil (cons (hd T) (tl (List))))))

(declare-fun p (X) Bool)
(declare-fun exists ((List X) Bool) Bool)
(declare-fun append ((List X) (List X) (List X)) Bool)

(assert (forall ((l1 (List X)) (l2 (List X)) (_v12 (List X)))
  (=>
    (and
        ((_ is nil) l1)
        (= _v12 l2)
    )
    (append l1 l2 _v12)
  )
))

(assert (forall ((l1 (List X)) (l2 (List X)) (_v44 (List X)) (_v41 (List X)) (var12 (List X)) (_v38 X) )
  (=>
    (and
      (append var12 l2 _v41)
      (not ((_ is nil) l1))
      ((_ is cons) l1)
      (= var12 (tl l1))
      (= _v38 (hd l1))
      (= _v44 (cons _v38 _v41))
    )
    (append l1 l2 _v44)
  )
))

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
                (_v53)
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
                (_v53)
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

(assert (forall ( (l1 (List X)) (l2 (List X)) (l3 (List X)) (r Bool) )
    (=>
        (and
            (append l1 l2 l3)
            (exists l1 true)
            (exists l3 false)
        )
        false
    )

))

(check-sat)
(exit)