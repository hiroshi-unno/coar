(set-logic HORN)

(declare-sort X 0)
(declare-datatypes (T) ((List nil (cons (hd T) (tl (List))))))

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

(assert
 (forall ((l1 (List X)) (l2 (List X)) (l3 (List X)) (l4 (List X)) (l5 (List X)) (l6 (List X)) (l7 (List X)) )
 (=> 
     (and
          (append l1 l2 l3) 
          (append l4 l5 l6) 
          (append l2 l5 l7)
          (append l1 l7 l6)  
     )
     (not (= l3 l4))
 )
))

(check-sat)
(exit)