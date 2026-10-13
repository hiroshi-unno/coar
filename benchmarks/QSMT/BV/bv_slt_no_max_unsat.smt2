; The signed counterpart of the unsigned-order file: signed order is bounded
; too (x = 127 is maximal), so forall x. exists y. x <s y is false.  Signed
; comparisons are rewritten before projection, so this covers a different arm
; than the unsigned one.
(set-logic BV)
(assert (forall ((x (_ BitVec 8))) (exists ((y (_ BitVec 8))) (bvslt x y))))
(check-sat)
