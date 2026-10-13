; **Nested predicate polymorphism**: the case where RCaml's copying is exponential and the
; modular encoding is linear.
;
;   let app0 f x = f x
;   let app1 f x = app0 f (app0 f x)
;   let app2 f x = app1 f (app1 f x)
;   let app3 f x = app2 f (app2 f x)
;   let main u = let a = app3 (fun z -> z + 1) u in assert (a >= u)
;
; Each level uses the level below **twice**, and every use of a predicate-polymorphic definition
; is instantiated by copying its constraints, so the system doubles per level.  Measured with
; config/solver/rcaml_wopp_printer.json on 2026-09-06: 28 clauses at depth 1, 56 at depth 2,
; 112 at depth 3 (unknowns 25 / 49 / 97) -- `2^d` copies of the innermost definition.
;
; Modularly there is nothing to copy: each level is verified once, for every `X`, and refers to
; the level below through its unknown.  Four clauses and four unknowns for depth 3, and one more
; clause per level after that.  expected: sat
(set-logic DQHORN)
(declare-forall-fun X (Int) Bool)
(declare-dep-exists-fun P0 () ((Array Int Bool) Int Int) Bool)
(declare-dep-exists-fun P1 () ((Array Int Bool) Int Int) Bool)
(declare-dep-exists-fun P2 () ((Array Int Bool) Int Int) Bool)
(declare-dep-exists-fun P3 () ((Array Int Bool) Int Int) Bool)

; app0 f x = f x, for every contract X the argument preserves
(assert (forall ((x Int) (r Int)) (=> (and (X x) (X r)) (P0 X x r))))
; app_{i+1} f x = app_i f (app_i f x)
(assert (forall ((x Int) (m Int) (r Int)) (=> (and (P0 X x m) (P0 X m r)) (P1 X x r))))
(assert (forall ((x Int) (m Int) (r Int)) (=> (and (P1 X x m) (P1 X m r)) (P2 X x r))))
(assert (forall ((x Int) (m Int) (r Int)) (=> (and (P2 X x m) (P2 X m r)) (P3 X x r))))

; the client: X := (>= 0), f = (+1) preserves it, so the result is non-negative
(assert (forall ((r Int))
  (=> (and (P3 (lambda ((a Int)) (>= a 0)) 0 r) (< r 0)) false)))
(check-sat)
