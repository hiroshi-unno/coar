; Satisfiable.  A functional predicate whose result is a sequence one element longer than an
; argument sequence.  F is declared functional (total and single-valued); Q is an ordinary
; predicate with a self-loop, so that preprocessing keeps both unknowns:
;   F(s, x, y) => Q(s, x, y)
;   Q(s, x, y) => Q(s ++ [0], x, y ++ [0])
;   Q(s, x, y) => seq.len y = seq.len s + 1
; A solution: F(s, x, y) :<=> y = s ++ [x] (total and single-valued) and
; Q(s, x, y) := seq.len y = seq.len s + 1, which is inductive.  So the verdict is sat.
;
; What the file is for: the function template for a sequence result (the FN template's
; seq_result_function_template, off by default) offers s ++ seq.unit x among its candidate
; results, so with the switch the expected answer is sat; without it the result sort has no
; template and the expected answer is unknown, an ordinary verdict.
(set-logic HORN)
(declare-fnp F ((Seq Int) Int (Seq Int)) Bool)
(declare-fun Q ((Seq Int) Int (Seq Int)) Bool)
(assert (forall ((s (Seq Int)) (x Int) (y (Seq Int))) (=> (F s x y) (Q s x y))))
(assert (forall ((s (Seq Int)) (x Int) (y (Seq Int)))
  (=> (Q s x y) (Q (seq.++ s (seq.unit 0)) x (seq.++ y (seq.unit 0))))))
(assert (forall ((s (Seq Int)) (x Int) (y (Seq Int)))
  (=> (Q s x y) (= (seq.len y) (+ (seq.len s) 1)))))
(check-sat)
