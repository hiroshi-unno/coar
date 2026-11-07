; The POPL 2024 ARM benchmark `expectation-SAT.ml` with its ghost parameter `(p, x, y)` replaced
; by predicate polymorphism, encoded by universally quantified predicates.
;
;   expectation _ctx body = try_with body () {
;     Pick p -> fun k -> p * (continue k true) + (100 - p) * (continue k false) }
;   let main p x y = expectation (p, x, y)(*dummy*) (fun () -> if perform (Pick p) then x else y)
;   assert  main : (p:int) -> (x:int) -> (y:int) -> {z: int | z = p * x + (100 - p) * y}
;
; The probabilistic member of the "combining" family: the handler takes a **weighted average**
; of the two branch answers, the weight `p` being the operation's argument.  As in `choose-max`,
; the abstracted predicate is indexed by the resumed value — `X(r, b)` = "resuming with `b`
; answers `r`" — because the two branches must be told apart.  The weight is an ordinary
; argument of the handler's clause, not part of the abstraction, so it stays first-order.
;
; The ghost parameter carried `(p, x, y)` into the handler; here the handler knows nothing about
; the client and the client instantiates.
; expected: unsat
(set-logic DQHORN)

(declare-forall-fun X (Int Bool) Bool)     ; X(r, b): resuming with b answers r
(declare-dep-exists-fun Pick () ((Array Int (Array Bool Bool)) Int Int) Bool)

; --- the handler, verified once for every X: Pick p averages the branches with weights p, 100-p
(assert (forall ((p Int) (r1 Int) (r2 Int))
  (=> (and (X r1 true) (X r2 false)) (Pick X p (+ (* p r1) (* (- 100 p) r2))))))

; --- client 1: the body answers x on true and y on false, so the value is p*x + (100-p)*y ---
(assert (forall ((p Int) (x Int) (y Int) (z Int))
  (=> (and (Pick (lambda ((r Int)) (lambda ((b Bool)) (or (and b (= r x)) (and (not b) (= r y)))))
                 p z)
           (not (= z (+ (* p x) (* (- 100 p) y)))))
      false)))
; --- client 2: a different context — both branches answer the same constant c, so the average
;     is 100 * c whatever the weight, but the specification wrongly demands 99 * c ---
(assert (forall ((p Int) (c Int) (z Int))
  (=> (and (Pick (lambda ((r Int)) (lambda ((b Bool)) (= r c))) p z)
           (not (= z (* 99 c))))
      false)))
(check-sat)
