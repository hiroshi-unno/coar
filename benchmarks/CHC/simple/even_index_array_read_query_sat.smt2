; The query's local z is even and indexes an array that stays (inv's argument), so projecting z
; away meets a divisibility beside a read a[z]: z = 2q with q fresh, and q is then removed by its
; model value, which the model must therefore bind.  The divisibility reaches the integer rule only
; when the quotient that `mod` introduces is eliminated before z; the projection eliminates in the
; order of variable names, and the unused w0..w34 shift the fresh-name counter so that z is
; #tvar99 and the quotient #tvar101, which sorts first.  The padding is tuned to the
; preprocessing that runs before the projection: when the refutation by unfolding moved into a
; forked copy, the parent minted 60 fewer names, z became #tvar39, the quotient sorted after it,
; and the projection solved z from the equality instead (still sat, but the residue rule went
; unexercised); w5..w34 restored the order.  If the row counting the residue rule's fresh
; variable fails while the verdict holds, re-tune the padding (each w shifts the counter by 2).
; a[0] >= 0 is invariant (a step needs x < a[0] and x >= 0), so the query is unreachable: sat.
(set-logic HORN)
(declare-fun inv (Int (Array Int Int)) Bool)
(assert (forall ((x Int) (a (Array Int Int)) (w0 Int) (w1 Int) (w2 Int) (w3 Int) (w4 Int) (w5 Int) (w6 Int) (w7 Int) (w8 Int) (w9 Int) (w10 Int) (w11 Int) (w12 Int) (w13 Int) (w14 Int) (w15 Int) (w16 Int) (w17 Int) (w18 Int) (w19 Int) (w20 Int) (w21 Int) (w22 Int) (w23 Int) (w24 Int) (w25 Int) (w26 Int) (w27 Int) (w28 Int) (w29 Int) (w30 Int) (w31 Int) (w32 Int) (w33 Int) (w34 Int)) (=> (and (= x 0) (>= (select a 0) 0) (>= w0 0) (>= w1 0) (>= w2 0) (>= w3 0) (>= w4 0) (>= w5 0) (>= w6 0) (>= w7 0) (>= w8 0) (>= w9 0) (>= w10 0) (>= w11 0) (>= w12 0) (>= w13 0) (>= w14 0) (>= w15 0) (>= w16 0) (>= w17 0) (>= w18 0) (>= w19 0) (>= w20 0) (>= w21 0) (>= w22 0) (>= w23 0) (>= w24 0) (>= w25 0) (>= w26 0) (>= w27 0) (>= w28 0) (>= w29 0) (>= w30 0) (>= w31 0) (>= w32 0) (>= w33 0) (>= w34 0)) (inv x a))))
(assert (forall ((x Int) (a (Array Int Int))) (=> (and (inv x a) (< x (select a 0))) (inv (+ x 1) (store a 0 (- (select a 0) 1))))))
(assert (forall ((z Int) (x Int) (a (Array Int Int)))
  (=> (and (inv x a) (= (mod z 2) 0) (< x z) (< z (+ x 3)) (= (select a z) 1) (< (select a 0) 0)) false)))
(check-sat)
