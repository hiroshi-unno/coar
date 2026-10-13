; expected: unsat
;
; `(distinct 0 0)` is false, so no `f` satisfies the constraints and the
; synthesis problem is infeasible; cvc5 answers `infeasible`.
;
; It answered `sat` because this frontend collected `distinct`'s operands into a
; set before generating the pairwise disequalities, so the two operands became
; one and the conjunction over zero pairs was `true`. Unlike the SMT-LIB2
; frontend, where two separately parsed literals carry different fresh sort
; variables and so survive the deduplication, here the literals are already
; identical typed terms -- so the ground case collapses too, and the masking is
; a property of that frontend rather than of the simplifier.
(set-logic LIA)
(synth-fun f ((z Int)) Int)
(constraint (= (f 0) 0))
(constraint (distinct 0 0))
(check-synth)
