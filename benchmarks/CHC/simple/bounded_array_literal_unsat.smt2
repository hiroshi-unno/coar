; expected: unsat
;
; The constraint has no predicate variable, so the whole verdict is the validity
; check in preprocessing: the clause is invalid because its premise fixes x1[0]
; to 11 and its conclusion asks for 12.
;
; What makes it a regression test is the premise's shape.  Both sides of the
; equation are array LITERALS whose index is confined to [0, 1), and the two are
; one `store` apart, so the premise is satisfiable -- but a solver asked about
; array literals answers "incomplete (theory array)" and decides nothing, which
; leaves the tool with `unknown` and no verdict.  An array literal bounded to a
; finite concrete range denotes a chain of `store`s over a constant array, and
; written that way the same question is inside the fragment the solver decides.
;
; PCSat: `unknown,0` until the simplifier expanded such a literal, `unsat,0`
; since.  The shape is taken from a Rust program whose slice `split_first_mut`
; writes through the first element; there the literal is the tail of a slice.
(set-logic HORN)
(assert (forall ((x0 (Array Int Int)) (x1 (Array Int Int)))
  (=> (and (= (store (lambda ((i Int)) (ite (and (< i 1) (>= i 0)) (select x0 (+ 1 i)) 0))
                     0
                     (select x1 1))
              (lambda ((i Int)) (ite (and (< i 1) (>= i 0)) (select x1 (+ 1 i)) 0)))
           (= (select x1 0) 11))
      (= (select x1 0) 12))))
(check-sat)
