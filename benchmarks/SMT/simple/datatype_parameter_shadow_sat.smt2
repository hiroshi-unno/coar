; Semantic verdict: sat. A local datatype parameter named like a member of the declaration
; group is the parameter, not a recursive reference to that member.
(set-logic ALL)
(declare-datatypes ((B 0) (A 1))
 (((bnil) (bw (ba (A Bool)))) (par (B) ((aw (value B))))))
(declare-const x0 (A Int))
(declare-const x1 (A Int))

(assert (distinct x0 x1))
(check-sat)
