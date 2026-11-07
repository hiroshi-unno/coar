; The read (val o) has no tester beside it, so its value at none is open: in a
; model where (val none) = 3 the first clause forces q none, which the second
; forbids.  Unsatisfiable under the per-model reading (every model must admit
; an interpretation of q).  Treating the read as if it were guarded by
; ((_ is some) o) would drop the none case and make the system satisfiable.
(set-logic HORN)
(declare-datatypes ((Opt 0)) (((none) (some (val Int)))))
(declare-fun q (Opt) Bool)
(assert (forall ((o Opt)) (=> (= (val o) 3) (q o))))
(assert (forall ((o Opt)) (=> (and (q o) ((_ is none) o)) false)))
(check-sat)
