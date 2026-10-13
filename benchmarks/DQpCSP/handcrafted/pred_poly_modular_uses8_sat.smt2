; The modular counterpart of benchmarks/OCaml/safety/simple/pred_poly_uses8_sat.ml
; the *same* situation -- one predicate-polymorphic definition used
; eight times -- with the definition verified once instead of copied per use.
;
;   app : forall X. (f : (a:{X}) -> {b | X b}) -> (x:{X}) -> {r | P(X, r)}
;
; RCaml generalizes `app` at its let-binding and then instantiates by copying
; (`Rtype.instantiate_val`, case `RForall`), so its constraint system grows by ~12 clauses and
; ~12 unknowns per use: 14 clauses at one use, 26 at two, 50 at four, 98 at eight, and the
; increment grows with the definition's size (+16 per use for `f (f (f x))`) -- measured
; 2026-09-06 with config/solver/rcaml_wopp_printer.json.
;
; Here the definition is **one clause and one unknown**, whatever the number of uses; each use
; adds a single clause that applies the same `P` at its own instantiation.  Eight clients, eight
; different instantiations `(>= i)`.  expected: sat
(set-logic DQHORN)
(declare-forall-fun X (Int) Bool)
(declare-dep-exists-fun P () ((Array Int Bool) Int) Bool)

; the definition, verified once for every X: the argument and the result satisfy X
(assert (forall ((x Int) (r Int)) (=> (and (X x) (X r)) (P X r))))

; the eight uses
(assert (forall ((r Int)) (=> (and (P (lambda ((a Int)) (>= a 0)) r) (< r 0)) false)))
(assert (forall ((r Int)) (=> (and (P (lambda ((a Int)) (>= a 1)) r) (< r 1)) false)))
(assert (forall ((r Int)) (=> (and (P (lambda ((a Int)) (>= a 2)) r) (< r 2)) false)))
(assert (forall ((r Int)) (=> (and (P (lambda ((a Int)) (>= a 3)) r) (< r 3)) false)))
(assert (forall ((r Int)) (=> (and (P (lambda ((a Int)) (>= a 4)) r) (< r 4)) false)))
(assert (forall ((r Int)) (=> (and (P (lambda ((a Int)) (>= a 5)) r) (< r 5)) false)))
(assert (forall ((r Int)) (=> (and (P (lambda ((a Int)) (>= a 6)) r) (< r 6)) false)))
(assert (forall ((r Int)) (=> (and (P (lambda ((a Int)) (>= a 7)) r) (< r 7)) false)))
(check-sat)
