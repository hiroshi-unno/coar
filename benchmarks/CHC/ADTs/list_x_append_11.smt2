(set-logic HORN)

(declare-sort X 0)
(declare-datatypes (T) ((List nil (cons (hd T) (tl (List))))))

(declare-fun append ((List X) (List X) (List X)) Bool)
(define-fun-rec length ((x (List X))) Int (
     ite ((_ is nil) x) 0 (+ 1 (length (tl x)))
))

(set-info length (forall ((x (List X)))
 (or ((_ is nil) x) (> (length x) 0))
))
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

(assert (forall ((l1 (List X)) (l2 (List X)) (r (List X)) (x X) ) 
  (=>
    (and 
        (append l1 l2 r)
        (= l1 (cons x nil))
    )
    (= r (cons x l2))
  )
))



(check-sat)
(exit)