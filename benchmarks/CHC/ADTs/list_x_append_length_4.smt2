(set-logic HORN)

(declare-sort X 0)
(declare-datatypes (T) ((List nil (cons (hd T) (tl (List))))))

(declare-fun append ((List X) (List X) (List X)) Bool)
(declare-fun length ((List X) Int) Bool)
(define-fun-rec defined_length ((x (List X))) Int (
     ite ((_ is nil) x) 0 (+ (defined_length (tl x)) 1)
))
(set-info defined_length (forall ((x (List X)))
  (or ((_ is nil) x) (> (defined_length x) 0))
))
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

(assert (forall ((l1 (List X)) (l2 (List X)) (r (List X)) (len1 Int) (len2 Int) (len3 Int) ) 
  (=>
    (and 
        (append l1 l2 r)
        (length l1 len1)
        (length l2 len2)
        (length r len3)
    )
    (= (+ len1 len2) len3)
  )
))

(check-sat)
(exit)