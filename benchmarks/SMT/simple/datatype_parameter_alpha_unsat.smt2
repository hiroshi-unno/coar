; Semantic verdict: unsat. A local datatype parameter named like a member of the declaration
; group is the parameter, not a recursive reference to that member.
(set-logic ALL)
(declare-datatypes ((B 0) (A 1))
 (((bnil) (bw (ba (A Bool)))) (par (T) ((aw (value T))))))
(declare-const x0 (A Bool))
(declare-const x1 (A Bool))
(declare-const x2 (A Bool))
(assert (distinct x0 x1 x2))
(check-sat)
