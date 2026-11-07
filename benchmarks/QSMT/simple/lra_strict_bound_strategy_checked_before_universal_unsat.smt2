(set-logic LRA)
(set-info :status unsat)
; Reduced from SMT-LIB keymaera/water_tank-node11756: ts = t forces
; t + x <= 2, against t + x > 2.  A strategy t = 2 - x + e (e a positive
; infinitesimal) must be checked with e fixed before the universal ts is
; chosen; read with e chosen after ts, it wins every move and the formula
; looks satisfiable.
(declare-fun t () Real)
(declare-fun x () Real)
(assert (forall ((ts Real))
  (and (=> (and (<= 0.0 ts) (<= ts t)) (<= (+ ts x) 2.0))
       (< x 2.0)
       (> (+ t x) 2.0))))
(check-sat)
(exit)
