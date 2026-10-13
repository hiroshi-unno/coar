; The POPL 2024 ARM benchmark `shift-SAT.ml` with its ghost parameter replaced by predicate
; polymorphism, encoded by universally quantified predicates.
;
;   let rec reset_ (_ctx: int) body = try_with body () {
;     Shift f -> fun k -> reset_ _ctx (fun () -> f (continue k)) }
;   let main n = reset_ n (fun () -> let s = perform (Shift (fun k -> k (k (k n)))) in s * 2 + 1)
;   assert  main : (n:int) -> {z:int | z = 8 * n + 7}
;
; Delimited control: `Shift` hands the *continuation itself* to the client's function `f`, which
; may apply it any number of times.  The abstracted predicate is the continuation's contract,
; `X(z, s)` = "resuming with s answers z"; the handler is verified once for every X and the
; client instantiates it at its own delimited context — here `z = 2s + 1`, applied three times,
; giving 8n + 7.  The ghost parameter `_ctx` was the first-order stand-in.
;
; K(X, s, z) is the continuation the handler supplies.  expected: unsat
(set-logic DQHORN)

(declare-forall-fun X (Int Int) Bool)      ; X(z, s): resuming with s answers z
(declare-dep-exists-fun K () ((Array Int (Array Int Bool)) Int Int) Bool)

; --- the handler, verified once for every X: the continuation it passes to `f` is the ambient one
(assert (forall ((s Int) (z Int)) (=> (X z s) (K X s z))))
(assert (forall ((s Int) (z Int)) (=> (and (K X s z) (not (X z s))) false)))

; --- client 1: f = (fun k -> k (k (k n))) in the context `s * 2 + 1`, i.e. X := (z,s) |-> z = 2s+1;
;     three applications give 8n + 7, but the specification wrongly demands 8n + 6 ---
(assert (forall ((n Int) (z1 Int) (z2 Int) (z3 Int))
  (=> (and (K (lambda ((z Int)) (lambda ((s Int)) (= z (+ (* 2 s) 1)))) n z1)
           (K (lambda ((z Int)) (lambda ((s Int)) (= z (+ (* 2 s) 1)))) z1 z2)
           (K (lambda ((z Int)) (lambda ((s Int)) (= z (+ (* 2 s) 1)))) z2 z3)
           (not (= z3 (+ (* 8 n) 6))))
      false)))
; --- client 2: the same handler in a different delimited context, `s + 5`, applied once ---
(assert (forall ((n Int) (z Int))
  (=> (and (K (lambda ((z2 Int)) (lambda ((s Int)) (= z2 (+ s 5)))) n z) (not (= z (+ n 5))))
      false)))
(check-sat)
