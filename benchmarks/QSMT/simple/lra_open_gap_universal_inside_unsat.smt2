(set-logic LRA)
(set-info :status unsat)
; x < 2 and no h strictly between x and 2: h = (x + 2) / 2 is always one.
; An existential's strategy x = 2 - e (e a positive infinitesimal) must be
; checked with e fixed before the universal h is chosen; read with e chosen
; after h, it wins every move and the formula looks satisfiable.
(declare-fun x () Real)
(assert (forall ((h Real)) (and (< x 2.0) (or (<= h x) (>= h 2.0)))))
(check-sat)
(exit)
