; The false negative for POPL 2024's `choose-max`, whose source carries **four** ghost parameters
; (`choose_max u v x y(*dummy*)`).  Triple:
;   arm_choosemax_mono_chc_unsat.smt2  no context information -> unsat  (this file)
;   arm_choosemax_ghost_chc_sat.smt2   the four ghosts        -> sat    (POPL 2024's fix)
;   arm_choosemax_pred_poly_sat.smt2   predicate polymorphism -> sat    (ours, QCHC)
;
;   main u v x y = choose_max u v x y (fun () -> let a = if Decide then u else v in
;                                                let b = if Decide then x else y in a - b)
;   assert  main : (u:int) -> (v:{z >= u}) -> (x:int) -> (y:{z >= x}) -> {z | z = v - x}
;
; `Decide` is called twice, in different contexts: the inner call's branch answers are `a - x`
; and `a - y`, and they mention the local `a` bound by the outer call.  With one refinement `A`
; for every call, `A` has to hold of the inner answers for **every** value the outer call may
; produce, so it degenerates to "any integer", the maximum the handler computes is unconstrained,
; and the specification is refuted.  expected: unsat
(set-logic HORN)
(declare-fun A (Bool Int) Bool)     ; A(b, r): resuming with b answers r -- one refinement for
                                    ; every call of Decide, which is the point
(declare-fun Ans (Int) Bool)
; the handler's clause: the maximum of the two branch answers is the answer
(assert (forall ((r1 Int) (r2 Int))
  (=> (and (A true r1) (A false r2) (>= r1 r2)) (Ans r1))))
(assert (forall ((r1 Int) (r2 Int))
  (=> (and (A true r1) (A false r2) (< r1 r2)) (Ans r2))))
; the inner call, at every `a` the outer call may bind -- this is where the context is lost
(assert (forall ((a Int) (x Int) (y Int)) (=> (>= y x) (A true (- a x)))))
(assert (forall ((a Int) (x Int) (y Int)) (=> (>= y x) (A false (- a y)))))
; the specification of main
(assert (forall ((u Int) (v Int) (x Int) (z Int))
  (=> (and (>= v u) (Ans z) (not (= z (- v x)))) false)))
(check-sat)
