(set-logic HORN)

(declare-sort X 0)
(declare-datatypes () ((X_List nil (cons (hd X) (tl (X_List))))))

(declare-fun append ((X_List) (X_List) (X_List)) Bool)


(assert (forall ((l1 (X_List)) (l2 (X_List)) (_v12 (X_List)))
  (=>
    (and
        ((_ is nil) l1)
        (= _v12 l2)
    )
    (append l1 l2 _v12)
  )
))

(assert (forall ((l1 (X_List)) (l2 (X_List)) (_v44 (X_List)) (_v41 (X_List)) (var12 (X_List)) (_v38 X) )
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
(assert (forall ((l1 (X_List)) (l2 (X_List)) (r (X_List)) (x X) ) 
  (=>
    (and 
        (append l1 l2 r)
    )
    (= (hd l1) (hd r))
  )
))



(check-sat)
(exit)