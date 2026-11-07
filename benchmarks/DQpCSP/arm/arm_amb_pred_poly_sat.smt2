; The POPL 2024 ARM benchmark `amb-3-simpl-SAT.ml` in its ghost-free form, as QCHC
; (predicate polymorphism encoded by universally quantified predicates).
;
;   amb body = try_with body () {
;     Select -> fun k -> if continue k true then true else continue k false }   (* angelic *)
;   let rec select_from e l = match l with
;     | [] -> false | x::xs -> if perform Select then x = e else select_from e xs
;   let amb_find e l = amb e l (fun () -> select_from e l)
;   let test e' e = amb_find e (e' :: e :: [])
;   assert  test : int -> int -> {z: bool | z = true}
;
; What was removed.  In the evaluated version (benchmarks/OCaml/popl24/arm/amb-3-simpl-SAT.ml)
; `select_from` is defined *inside* the closure passed to `amb`, where RCaml's let-generalization
; can give it a predicate-polymorphic type; the ghost-free version defines it at top level, and
; then the implementation has no way to abstract the ambient answer refinement of a recursive
; function that performs an operation.  Measured 2026-09-06 with `rcaml_pp_pcsat_tb_ar`:
; `amb-3-simpl-SAT.ml` is `sat,7`, `amb-3-simpl-noctx-SAT.ml` is **`unsat,36`** -- the same program
; is rejected once the definition moves out.
;
; Here `select_from` is typed once for every ambient answer refinement `X` (an
; `Array Bool Bool` argument it carries explicitly, so the client can instantiate it), and the
; handler's Select clause is checked against the operation's polymorphic signature
;   Select : forall X:bool. (unit) -> ((v:bool) -> {z | X(z)}) -> {z | X(z)}
; (answer refinement transported unchanged -- ATM's `X => X`).  The angelic content is in the
; disjunction: the handler runs the continuation at `true`, and at `false` if that answered
; `false`, so the answer of `select_from e (x::xs)` is `(x = e) \/ answer(select_from e xs)`.
; The solver must find that `select_from e l` answers true whenever `e` occurs in `l`.
; expected: sat
(set-logic DQHORN)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))

(declare-forall-fun X (Bool) Bool)
; the Select clause's own spec, and the spec of select_from, both parameterised by the ambient
; answer refinement (explicit array argument: the front end prepends declared dependencies and
; has no syntax for instantiating one)
(declare-dep-exists-fun Sel () ((Array Bool Bool) Bool) Bool)
(declare-dep-exists-fun SF  () ((Array Bool Bool) Int Lst Bool) Bool)

; --- the handler, verified once for every X ---
; branch 1: continue k true answered true, so the clause answers true
(assert (=> (X true) (Sel X true)))
; branch 2: it answered false, so the clause answers whatever continue k false answers
(assert (forall ((z2 Bool)) (=> (X z2) (Sel X z2))))
; the clause must meet the operation's declared result type {z | X(z)}
(assert (forall ((z Bool)) (=> (and (Sel X z) (not (X z))) false)))

; --- select_from, typed once for every X ---
(assert (forall ((e Int)) (SF X e nil false)))
(assert (forall ((e Int) (x Int) (xs Lst) (z2 Bool))
  (=> (SF X e xs z2) (SF X e (cons x xs) (or (= x e) z2)))))

; --- client 1: X := (b |-> b), i.e. "the answer is true"; test e' e = amb_find e [e'; e] ---
(assert (forall ((e1 Int) (e2 Int) (z Bool))
  (=> (and (SF (lambda ((b Bool)) b) e2 (cons e1 (cons e2 nil)) z) (not z)) false)))
; --- client 2: the dual instantiation X := (b |-> not b) on the empty choice list, where the
;     answer is false; one solution for SF must serve both (one verification, several clients) ---
(assert (forall ((e Int) (z Bool))
  (=> (and (SF (lambda ((b Bool)) (not b)) e nil z) z) false)))
(check-sat)
