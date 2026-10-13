(set-logic HORN)
(define-fun-rec |a b| ((|x y| Bool)) Bool (not |x y|))
(assert (forall ((x Bool)) (= (|a b| x) (not x))))
(check-sat)
