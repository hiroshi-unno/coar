; The POPL 2024 ARM benchmark `deferred-easy-SAT.ml` with its ghost parameter removed, as QCHC
; (predicate polymorphism encoded by universally quantified predicates).
;
;   type deferred = Value of int | Thunk of (unit -> int)
;   lazy_ t body = match_with body () { retc = fun y -> fun s -> y;
;       Force -> fun k -> function Value v      -> continue k v (Value v)
;                                | Thunk t      -> let v = t () in continue k v (Value v) }
;     (Thunk t)
;   test n = lazy_ (fun () -> n) (fun () -> let res = perform Force in res)
;   assert  test : (n:int) -> {z | z = n + 1}   (deliberately wrong, so this must be refuted)
;
; What the ghost parameter was carrying.  The evaluated version
; (benchmarks/OCaml/popl24/arm/deferred-1-SAT.ml) declares
;   type deferred = Value of int | Thunk of int(*ctxinfo*) * (unit -> int)
;   [@@@rtype "Thunk :: (c: {z:int | p3(z)}) -> (f: unit -> {z: int | p4(z, c)}) -> ..."]
; i.e. the thunk's postcondition is a *constructor-level* abstracted predicate `p4` applied to a
; ghost field `c` that carries the client's `n`.  Drop the field and RCaml answers `unsat,0`
; (measured 2026-09-06, `rcaml_pp_pcsat_tb_ar`): with no way to name the thunk's postcondition,
; the program is rejected.  Here the postcondition is a universal predicate symbol `X`, the
; handler is verified once for every `X`, and the client instantiates it at `(= z n)`.
;
; The `deferred` state is encoded as a pair (isValue, v): `Value v` is (true, v), a thunk is
; (false, _) with its postcondition being `X` -- a closure cannot be a first-order value, and its
; contract is exactly what the abstraction names.  expected: unsat
(set-logic DQHORN)

(declare-forall-fun X (Int) Bool)
; Inv(X, isValue, v): the state is well-formed -- a Value stores a value satisfying X
(declare-dep-exists-fun Inv () ((Array Int Bool) Bool Int) Bool)
; Frc(X, isValue, v, z): performing Force at that state resumes the continuation with z
(declare-dep-exists-fun Frc () ((Array Int Bool) Bool Int Int) Bool)

; --- the handler, verified once for every X ---
; the initial state is the thunk itself
(assert (forall ((v Int)) (Inv X false v)))
; Force at a Value: continue k v (Value v)
(assert (forall ((v Int)) (=> (Inv X true v) (Frc X true v v))))
; Force at a Thunk: v = t () satisfies the thunk's postcondition X, then continue k v (Value v)
(assert (forall ((v Int) (w Int)) (=> (and (Inv X false v) (X w)) (Frc X false v w))))
; ... and the new state Value v must itself be well-formed
(assert (forall ((v Int) (w Int)) (=> (and (Inv X false v) (X w)) (Inv X true w))))
; the well-formedness the Value branch relies on
(assert (forall ((v Int)) (=> (and (Inv X true v) (not (X v))) false)))

; --- the client: t = (fun () -> n), so X := (z |-> z = n); the wrong spec asks for n+1 ---
(assert (forall ((n Int) (z Int))
  (=> (and (Frc (lambda ((a Int)) (= a n)) false 0 z) (not (= z (+ n 1)))) false)))
(check-sat)
