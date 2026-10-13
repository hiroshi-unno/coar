; Unsatisfiable.  The twin of fn_seq_result_concat_sat.smt2 with one more clause, a fact
; x > 0 => Q(s, x, s ++ s): at s = [] and x = 1 the goal then demands 0 = 1, whatever F is.
;   F(s, x, y) => Q(s, x, y)
;   Q(s, x, y) => Q(s ++ [0], x, y ++ [0])
;   x > 0 => Q(s, x, s ++ s)
;   Q(s, x, y) => seq.len y = seq.len s + 1
;
; What the file is for: with the FN template's seq_result_function_template on, the
; sequence-result template must not turn an unsatisfiable problem into sat; the expected answer
; is unsat with the switch and without it.  (Preprocessing refutes it, so it pins the verdict,
; not the template.)
(set-logic HORN)
(declare-fnp F ((Seq Int) Int (Seq Int)) Bool)
(declare-fun Q ((Seq Int) Int (Seq Int)) Bool)
(assert (forall ((s (Seq Int)) (x Int) (y (Seq Int))) (=> (F s x y) (Q s x y))))
(assert (forall ((s (Seq Int)) (x Int) (y (Seq Int)))
  (=> (Q s x y) (Q (seq.++ s (seq.unit 0)) x (seq.++ y (seq.unit 0))))))
(assert (forall ((s (Seq Int)) (x Int)) (=> (> x 0) (Q s x (seq.++ s s)))))
(assert (forall ((s (Seq Int)) (x Int) (y (Seq Int)))
  (=> (Q s x y) (= (seq.len y) (+ (seq.len s) 1)))))
(check-sat)
