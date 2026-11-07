; Unsatisfiable: P(0), P => Q and Q(x) => x >= 1 force 0 >= 1.
; With the template synthesizer's candidate generalisation on, the candidate
; P := p1 <= p2, Q := p3 <= p4 has three clause groups chained by shared
; parameters ({p1,p2}, {p1..p4}, {p3,p4}); each group alone has parameter
; values that make it valid, all three together have none.
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (P x) (Q x))))
(assert (forall ((x Int)) (=> (Q x) (>= x 1))))
(check-sat)
