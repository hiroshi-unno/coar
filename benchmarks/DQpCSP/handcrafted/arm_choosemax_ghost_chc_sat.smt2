; POPL 2024's repair for `choose-max`: the ghost parameters `u v x y` are passed to the handler,
; so the one refinement may be indexed by the call's context -- here by the call site `c` (inner
; = 1, outer = 2) and the values it needs.  Middle file of the triple; see
; arm_choosemax_mono_chc_unsat.smt2 and arm_choosemax_pred_poly_sat.smt2.
; Plain CHC, satisfiable.  expected: sat
(set-logic HORN)
(declare-fun A (Int Int Int Bool Int) Bool)  ; A(site, ghost1, ghost2, branch, answer)
(declare-fun Ans (Int Int Int Int) Bool)
; the handler's clause, at a fixed site and its ghost values
(assert (forall ((c Int) (p Int) (q Int) (r1 Int) (r2 Int))
  (=> (and (A c p q true r1) (A c p q false r2) (>= r1 r2)) (Ans c p q r1))))
(assert (forall ((c Int) (p Int) (q Int) (r1 Int) (r2 Int))
  (=> (and (A c p q true r1) (A c p q false r2) (< r1 r2)) (Ans c p q r2))))
; site 1, the inner call in the context of `a`: branches answer a - x and a - y, y >= x
(assert (forall ((a Int) (x Int) (y Int)) (=> (>= y x) (A 1 a x true (- a x)))))
(assert (forall ((a Int) (x Int) (y Int)) (=> (>= y x) (A 1 a x false (- a y)))))
; site 2, the outer call: branches answer u - x and v - x, v >= u
(assert (forall ((u Int) (v Int) (x Int)) (=> (>= v u) (A 2 v x true (- u x)))))
(assert (forall ((u Int) (v Int) (x Int)) (=> (>= v u) (A 2 v x false (- v x)))))
; the specification of main, at the outer site
(assert (forall ((v Int) (x Int) (z Int))
  (=> (and (Ans 2 v x z) (not (= z (- v x)))) false)))
(check-sat)
