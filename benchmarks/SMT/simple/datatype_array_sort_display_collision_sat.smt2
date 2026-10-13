; expected: sat; distinct identities for datatype instances whose arguments print alike are
; only partly implemented.
; Box Bool has two elements, hence Bool-indexed arrays into it have four.
; The independent user sort bool may have three elements, admitting five arrays.
(set-logic ALL)
(declare-sort bool 0)
(declare-datatypes ((Box 1)) ((par (T) ((mkBox (value T))))))
(declare-const a (Box Bool))
(assert (= a (mkBox true)))
(declare-const c0 (Array Bool (Box bool)))
(declare-const c1 (Array Bool (Box bool)))
(declare-const c2 (Array Bool (Box bool)))
(declare-const c3 (Array Bool (Box bool)))
(declare-const c4 (Array Bool (Box bool)))
(assert (distinct c0 c1 c2 c3 c4))
(check-sat)
