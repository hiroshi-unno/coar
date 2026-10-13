; The same doubling chain as the file beside this one -- twenty-five nested let-bindings,
; t25 = 33554432*x -- but over a forall-bound variable instead of a declared constant.
; The assertion is that a positive x has a positive 2^25 multiple, which is true.
;
; Written out in full the term would have 33,554,432 leaves.  This file stays small end to
; end and is read in well under a second, which is the point of keeping it: it shows that
; the machinery for preserving a `let` works, and that what defeats it in the companion
; file is the classification of `declare-fun` constants as unknowns, not the parser and not
; any inability to represent sharing.
;
; If a change ever makes this file slow or large, sharing has been lost somewhere new.
(assert (forall ((x Int)) (=> (> x 0) (> (let ((t1 (+ x x))) (let ((t2 (+ t1 t1))) (let ((t3 (+ t2 t2))) (let ((t4 (+ t3 t3))) (let ((t5 (+ t4 t4))) (let ((t6 (+ t5 t5))) (let ((t7 (+ t6 t6))) (let ((t8 (+ t7 t7))) (let ((t9 (+ t8 t8))) (let ((t10 (+ t9 t9))) (let ((t11 (+ t10 t10))) (let ((t12 (+ t11 t11))) (let ((t13 (+ t12 t12))) (let ((t14 (+ t13 t13))) (let ((t15 (+ t14 t14))) (let ((t16 (+ t15 t15))) (let ((t17 (+ t16 t16))) (let ((t18 (+ t17 t17))) (let ((t19 (+ t18 t18))) (let ((t20 (+ t19 t19))) (let ((t21 (+ t20 t20))) (let ((t22 (+ t21 t21))) (let ((t23 (+ t22 t22))) (let ((t24 (+ t23 t23))) (let ((t25 (+ t24 t24))) t25))))))))))))))))))))))))) 0))))
(check-sat)
