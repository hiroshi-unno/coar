; The middle file of the triple (see arm_state_mono_chc_unsat.smt2): POPL 2024's own repair --
; a **ghost parameter**.  The client passes its local `c` to `Lookup` and `Update`, so the one
; answer refinement may be indexed by it: `A(c, z, s)` instead of `A(z, s)`, with the annotations
; `{z | z = ctx + s}` and `{z | z = ctx2 + 1 + s'}` of
; benchmarks/OCaml/popl24/arm/state-SAT.ml spelling out the instance.
;
; The dependence on the context is now carried by an ordinary first-order argument, so the
; system stays in CHC -- and it is satisfiable (`A(c,z,s) := (z = c + s)`), which is why the
; POPL 2024 experiments could run at all.  The price is written into the source: the operations
; take an argument they never use, the client must pass exactly the right value, and the trick
; works only when the needed predicate factors through a first-order value.
;
; Plain CHC, no `declare-forall-fun`.  expected: sat
(set-logic HORN)
(declare-fun A (Int Int Int) Bool)

; Update at ghost c: the clause's type is {z | A(c, z, x)} and the continuation's {z | A(c, z, s)},
; both indexed by the same context, so nothing is forced to be state-independent
(assert (forall ((c Int) (x Int) (z Int)) (=> (A c z x) (A c z x))))
; the loop: at state s > 0 the counter recurses with c+1 and state s-1
(assert (forall ((c Int) (s Int) (z Int))
  (=> (and (> s 0) (A (+ c 1) z (- s 1))) (A c z s))))
; the base: at state 0 the answer is c
(assert (forall ((c Int)) (A c c 0)))
; the specification: from ghost 0 and initial state init >= 0 the answer is init
(assert (forall ((init Int) (z Int))
  (=> (and (>= init 0) (A 0 z init) (not (= z init))) false)))
(check-sat)
