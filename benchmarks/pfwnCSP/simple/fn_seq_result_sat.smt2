; Satisfiable.  A functional predicate whose result is a sequence.  P is declared functional
; (total and single-valued) and gives, for each x, a sequence y with P(x, y); Q is an ordinary
; predicate with a self-loop, so that preprocessing keeps both unknowns:
;   P(x, y) => Q(x, y)
;   Q(x, y) /\ x >= 0 => Q(x + 1, y ++ [0])
;   Q(x, y) => x < 0 \/ seq.len y = x
; A solution: P(x, y) holds exactly when y is the sequence of max(x, 0) zeros (total and
; single-valued), and Q(x, y) := x < 0 \/ seq.len y = x, which is inductive.  So the verdict is sat.
;
; What the file is for: the function templates have no form whose result is a sequence, so the
; expected answer of this tool is unknown, an ordinary verdict, and never an exception or unsat.
(set-logic HORN)
(declare-fnp P (Int (Seq Int)) Bool)
(declare-fun Q (Int (Seq Int)) Bool)
(assert (forall ((x Int) (y (Seq Int))) (=> (P x y) (Q x y))))
(assert (forall ((x Int) (y (Seq Int)))
  (=> (and (Q x y) (>= x 0)) (Q (+ x 1) (seq.++ y (seq.unit 0))))))
(assert (forall ((x Int) (y (Seq Int))) (=> (Q x y) (or (< x 0) (= (seq.len y) x)))))
(check-sat)
