; P is functional with no argument, so it holds of exactly one option, which
; would have to be both some and none: no total P exists, unsat.
(set-logic HORN)
(declare-datatypes ((Opt 0)) (((none) (some (val Int)))))
(declare-fnp P (Opt) Bool)
(assert (forall ((o Opt)) (=> (P o) (and ((_ is some) o) ((_ is none) o)))))
(check-sat)
