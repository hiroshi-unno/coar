; a well-founded relation over the reals: every step decreases x by at least 1.5
; while x stays above 1, so a ranking decreasing by >= 1 per step exists; a bare
; strict decrease (x > y) would not be a well-foundedness witness over the reals
(set-logic HORN)
(declare-wfp WF_R (Real Real) Bool)
(assert (forall ((x Real) (y Real)) (=> (and (>= x 1.0) (= y (- x 1.5))) (WF_R x y))))
(assert (forall ((x Real) (y Real)) (=> (and (>= x 3.0) (= y (- x 2.0))) (WF_R x y))))
(check-sat)
