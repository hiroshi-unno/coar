; The POPL 2024 ARM benchmark `modulus-SAT.ml` with its ghost parameter `_r` replaced by
; predicate polymorphism, encoded by universally quantified predicates.
;
;   mu f sequence = match_with (fun () -> f (fun x -> perform (Call x))) () {
;     retc = fun x -> fun n -> n;
;     Call n -> fun k -> fun i -> let j = max i n in continue k (sequence n) j } 0
;   let test _r(*ctx*) a b = let f a = a 10 in mu f a = mu f b
;   assert  test : (r:int) -> ((xa:int) -> {z | xa = 10 => z = r})
;                          -> ((xb:int) -> {z | xb = 10 => z = r}) -> {z: bool | z = true}
;
; Modulus of continuity: `mu` runs `f` with a probe that queries the sequence, and the two runs
; must agree because the two sequences agree at the queried index.  What is abstracted here is
; **a function argument's contract** — the sequence's — not an answer refinement: `S(n, v)` says
; the sequence may map `n` to `v`.  The ghost parameter `_r` was the first-order stand-in for it,
; carrying the common value at index 10 into the handler.
;
; The two clients are the two sequences `a` and `b` of the program: different instantiations of
; the same, once-verified `mu`, and the equality `mu f a = mu f b` follows because each answers
; `r`.
; expected: unsat
(set-logic DQHORN)

(declare-forall-fun S (Int Int) Bool)      ; S(n, v): the sequence may map n to v
(declare-dep-exists-fun Mu () ((Array Int (Array Int Bool)) Int) Bool)

; --- mu, verified once for every sequence contract S: `f` probes at 10 and returns what it gets
(assert (forall ((v Int)) (=> (S 10 v) (Mu S v))))

; --- client 1: the sequence `a`, whose contract pins the value at 10 to r ---
(assert (forall ((r Int) (z Int))
  (=> (and (Mu (lambda ((n Int)) (lambda ((v Int)) (=> (= n 10) (= v r)))) z) (not (= z r)))
      false)))
; --- client 2 (wrong): a sequence contract that says nothing at index 10, yet the specification
;     still demands r -- the modulus argument does not apply and this must be refuted ---
(assert (forall ((r Int) (z Int))
  (=> (and (Mu (lambda ((n Int)) (lambda ((v Int)) (>= v 0))) z) (not (= z r))) false)))
(check-sat)
