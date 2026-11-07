(set-logic HORN)
(define-fun-rec f ((x (_ BitVec 8))) (_ BitVec 8) (bvadd (f x) #x01))
(assert true)
(check-sat)
