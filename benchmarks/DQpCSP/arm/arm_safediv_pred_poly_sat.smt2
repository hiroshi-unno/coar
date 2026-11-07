; The POPL 2024 ARM benchmark `safe-div-1-SAT.ml` with its ghost parameter replaced by predicate
; polymorphism, encoded by universally quantified predicates.
;
;   optionize _ctx body = match_with body () { retc = fun x -> Some x; exnc = fun MyExn -> None }
;   let safe_div n m = optionize (n, m)(*dummy*) (fun () -> if m = 0 then raise MyExn else n / m)
;   assert  safe_div : int -> {z | z = 0} -> {z: int option | z = None}
;
; Exceptions are operations here (POPL 2024 § 6: "our implementation deals with operations and
; exceptions uniformly").  The abstracted predicate is the **body's postcondition on normal
; return**:
;   optionize : forall X:int. (unit -> {z:int | X(z)})
;                          -> {z: int option | (z = Some v /\ X(v)) \/ z = None}
; and the ghost parameter of the evaluated file is the pair `(n, m)` passed to `optionize` so
; that the handler can name the client's values.  With the abstraction it needs none of that:
; the handler is verified once for every X and each client picks its own.
;
; `int option` is encoded as (isSome, v).  expected: sat
(set-logic DQHORN)

(declare-forall-fun X (Int) Bool)
(declare-dep-exists-fun Opt () ((Array Int Bool) Bool Int) Bool)

; --- the handler, verified once for every X ---
; retc: the body returned v normally, and its postcondition holds of v
(assert (forall ((v Int)) (=> (X v) (Opt X true v))))
; exnc: MyExn was raised -- the answer is None, whatever X says
(assert (Opt X false 0))

; --- client 1: m = 0, so the body always raises; X := (z |-> false) says "no normal return",
;     which the client discharges from m = 0.  The answer must be None ---
(assert (forall ((isSome Bool) (v Int))
  (=> (and (Opt (lambda ((a Int)) false) isSome v) isSome) false)))
; --- client 2: n >= 0 and m > 0, so the body returns n / m >= 0; X := (z |-> z >= 0), a
;     different instantiation of the same once-verified handler.  If the answer is
;     Some v then v >= 0 ---
(assert (forall ((isSome Bool) (v Int))
  (=> (and (Opt (lambda ((a Int)) (>= a 0)) isSome v) isSome (< v 0)) false)))
(check-sat)
