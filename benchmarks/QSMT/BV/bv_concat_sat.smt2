; The eliminated variable is equated to a concatenation of two universals.
; Worth keeping as a *negative* landmark for the projection: concat with an
; affine argument is folded into arithmetic before the rules are tried
; (concat(x, w) is x * 16 + w over 8 bits), so this does NOT reach the
; concatenation rule -- it is solved as an ordinary equation with an odd
; coefficient.  See the files whose concatenation has a non-affine argument
; for inputs that do reach it.
(set-logic BV)
(assert (forall ((x (_ BitVec 4)) (w (_ BitVec 4))) (exists ((y (_ BitVec 8))) (= y (concat x w)))))
(check-sat)
