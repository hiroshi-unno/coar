; The POPL 2024 ARM benchmark `choose-max-SAT.ml` with its four ghost parameters replaced by
; predicate polymorphism, encoded by universally quantified predicates.
;
;   choose_max _ctx1 _ctx2 _ctx3 _ctx4 body = try_with body () {
;     Decide _ -> fun k -> let r1 = continue k true in let r2 = continue k false in
;                          if r1 >= r2 then r1 else r2 }
;   let main u v x y = choose_max u v x y(*dummy*) (fun () ->
;     let a = if perform (Decide (false,0)) then u else v in
;     let b = if perform (Decide (true,a))  then x else y in a - b)
;   assert  main : (u:int) -> (v:{z | z >= u}) -> (x:int) -> (y:{z | z >= x}) -> {z | z = v - x}
;
; This is the shape the earlier ARM encodings did not have: the handler **combines** the two
; branch answers (here with `max`) instead of transporting one, so the abstracted predicate must
; say what each branch answers, and the answer refinement the clause produces is *derived* from
; it.  The continuation's type in the paper is `(y:T2) -> C1` — parameterised by the resumed
; value — so the abstracted predicate is indexed by the branch: `X(r, b)` = "resuming with `b`
; answers `r`".  With a set-valued abstraction `X(r)` the encoding would be wrong (it would allow
; both branches to take the same element and `max` to return the smaller answer), which is worth
; recording as the modelling pitfall of this shape.
;
; The two clients are the program's **two calls of the same operation in different contexts**,
; which is precisely what POPL 2024 § 3.2 introduces predicate polymorphism for ("this allows
; calls to the same operation in different contexts to have different control effects").  The
; inner call's instantiation mentions the client's local `a` — the very thing the ghost parameter
; was there to carry.  expected: sat
(set-logic DQHORN)

(declare-forall-fun X (Int Bool) Bool)     ; X(r, b): resuming with b answers r
(declare-dep-exists-fun Dec () ((Array Int (Array Bool Bool)) Int) Bool)

; --- the handler, verified once for every X ---
(assert (forall ((r1 Int) (r2 Int))
  (=> (and (X r1 true) (X r2 false) (>= r1 r2)) (Dec X r1))))
(assert (forall ((r1 Int) (r2 Int))
  (=> (and (X r1 true) (X r2 false) (< r1 r2)) (Dec X r2))))

; --- client 1, the inner call, in the context of the local `a`: resuming with true answers
;     a - x, with false answers a - y; since y >= x the maximum is a - x ---
(assert (forall ((a Int) (x Int) (y Int) (z Int))
  (=> (and (>= y x)
           (Dec (lambda ((r Int)) (lambda ((b Bool)) (or (and b (= r (- a x)))
                                                         (and (not b) (= r (- a y)))))) z)
           (not (= z (- a x))))
      false)))
; --- client 2, the outer call, in a different context: resuming with true answers u - x, with
;     false answers v - x; since v >= u the maximum is v - x, the specification of `main` ---
(assert (forall ((u Int) (v Int) (x Int) (z Int))
  (=> (and (>= v u)
           (Dec (lambda ((r Int)) (lambda ((b Bool)) (or (and b (= r (- u x)))
                                                         (and (not b) (= r (- v x)))))) z)
           (not (= z (- v x))))
      false)))
(check-sat)
