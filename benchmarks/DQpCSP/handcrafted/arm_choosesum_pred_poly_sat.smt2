; The POPL 2024 ARM benchmark `choose-sum-SAT.ml` with its ghost parameters replaced by
; predicate polymorphism, encoded by universally quantified predicates.
;
;   choose_all _ctx1 _ctx2 body = match_with body () { retc = fun x -> x;
;     Decide _ -> fun k -> continue k true + continue k false }
;   let main x y = choose_all x y(*dummy*) (fun () ->
;     let a = if perform (Decide (false,0)) then x else y in
;     let b = if perform (Decide (true,a))  then x else y in a - b)
;   assert  main : int -> int -> {z: int | z = 0}
;
; This is the shape the earlier ARM encodings did not have: the handler **combines** the two
; branch answers (here with `+`: the sum over all branches, so the four combinations of `a - b` cancel) instead of transporting one, so the abstracted predicate must
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
  (=> (and (X r1 true) (X r2 false)) (Dec X (+ r1 r2)))))

; --- client 1, the inner call, in the context of the local `a`: the two branches answer
;     a - x and a - y, so the sum is 2a - x - y ---
(assert (forall ((a Int) (x Int) (y Int) (z Int))
  (=> (and (Dec (lambda ((r Int)) (lambda ((b Bool)) (or (and b (= r (- a x)))
                                                         (and (not b) (= r (- a y)))))) z)
           (not (= z (- (- (* 2 a) x) y))))
      false)))
; --- client 2, the outer call in a different context: the branches answer 2x - x - y and
;     2y - x - y, so the sum is 0 -- the specification of `main` ---
(assert (forall ((x Int) (y Int) (z Int))
  (=> (and (Dec (lambda ((r Int)) (lambda ((b Bool))
                  (or (and b (= r (- (- (* 2 x) x) y))) (and (not b) (= r (- (- (* 2 y) x) y)))))) z)
           (not (= z 0)))
      false)))
(check-sat)
