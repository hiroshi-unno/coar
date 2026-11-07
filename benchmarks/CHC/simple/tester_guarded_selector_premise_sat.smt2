; A payload read through a selector beside its own tester in a premise:
; ((_ is some) o) /\ (val o) ... is the constructor equation o = (some y) over a
; fresh clause variable y in every model, whatever (val none) denotes.  Solution:
; q o := ((_ is some) o) /\ (val o) > 0, p x := x > 0.
(set-logic HORN)
(declare-datatypes ((Opt 0)) (((none) (some (val Int)))))
(declare-fun p (Int) Bool)
(declare-fun q (Opt) Bool)
(assert (forall ((o Opt)) (=> (and ((_ is some) o) (> (val o) 0)) (q o))))
(assert (forall ((o Opt)) (=> (and (q o) ((_ is some) o)) (p (val o)))))
(assert (forall ((x Int)) (=> (p x) (> x 0))))
(check-sat)
