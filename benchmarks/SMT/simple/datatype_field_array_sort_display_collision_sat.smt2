; Expected: sat. A nested field must not resolve to another datatype instance whose sort
; arguments print alike.
; The bounded guard refuses the collision; full structural identity remains unfinished.
(set-logic ALL)
(declare-sort bool 0)
(declare-datatypes ((Box 1)) ((par (T) ((mkBox (value T))))))
(declare-datatype zzWrap ((wrap (payload (Array Bool (Box bool))))))
(declare-const a (Box Bool))
(assert (= a (mkBox true)))
(declare-const c0 zzWrap)
(declare-const c1 zzWrap)
(declare-const c2 zzWrap)
(declare-const c3 zzWrap)
(declare-const c4 zzWrap)
(assert (distinct c0 c1 c2 c3 c4))
(check-sat)
