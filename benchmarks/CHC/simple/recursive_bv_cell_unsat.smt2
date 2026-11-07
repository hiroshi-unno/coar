(set-logic HORN)
(define-fun-rec f ((x (_ BitVec 8))) (_ BitVec 8) (ite (= x #x05) (bvadd (f #x05) #x01) #x00))
(assert true)
(check-sat)
