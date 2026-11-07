(set-logic HORN)
(define-fun-rec f ((x (_ BitVec 8))) (_ BitVec 8) (ite (= x #x05) (f #x05) #x00))
(assert true)
(check-sat)
