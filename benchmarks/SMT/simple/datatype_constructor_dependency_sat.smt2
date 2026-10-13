; Semantic verdict: sat. A constructor or selector named like another datatype must not count
; as a sort dependency (a false mutual group gave duplicate definitions and no answer).
(set-logic ALL)
(declare-datatypes ((A 1) (B 1))
 ((par (T) ((B (value T))))
  (par (U) ((bnil) (bw (ba (A Bool)) (extra U))))))
(declare-const x0 (A Int))
(declare-const x1 (A Int))
(assert (distinct x0 x1))
(check-sat)
