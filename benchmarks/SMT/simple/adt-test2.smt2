(set-logic ALL_SUPPORTED)
(declare-sort A 0 )
(declare-datatypes ()((A_list (nil) (cons (hd A )(tl A_list)))))
(define-fun-rec length ((x (A_list))) Int (
     ite ((_ is nil) x) 0 (+ 1 (length (tl x))) 
))

(set-info length (forall ((x (List X))
  (>= (length x) 0)
)))

(declare-fun l () A_list)

(assert 
     (not (or (not (>= (length l) 0)) (>= (length l) 0)))
)


(check-sat)
(exit)