; A payload read through a selector beside its own tester in a premise forces
; q (some 3) in every model, and the goal forbids it.  The read is guarded, so
; the refutation does not depend on what (val none) denotes.
(set-logic HORN)
(declare-datatypes ((Opt 0)) (((none) (some (val Int)))))
(declare-fun q (Opt) Bool)
(assert (forall ((o Opt)) (=> (and ((_ is some) o) (= (val o) 3)) (q o))))
(assert (forall ((o Opt)) (=> (q o) (not (= o (some 3))))))
(check-sat)
