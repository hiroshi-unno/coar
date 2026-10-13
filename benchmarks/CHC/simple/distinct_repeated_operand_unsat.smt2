; expected: unsat
;
; `(distinct x x)` is false for every `x` -- SMT-LIB makes `distinct` false as
; soon as two of its arguments are equal -- so the premise never holds... except
; that this clause asserts it of every `x`, which is therefore not valid, and
; with no unknown to choose the verdict is `unsat`. z3 and cvc5 both refute the
; assertion.
;
; It answered `sat` because the operands were collected into a set before the
; pairwise disequalities were generated: the two occurrences of `x` became one
; and the conjunction over zero pairs is `true`. Ground repetitions did not show
; it -- two separately parsed literals carry different fresh sort variables at
; that point, so `(distinct 0 0)` survived the deduplication and was refuted
; correctly. It takes a named variable, a repeated `let` reference or three
; operands with a repetition to see it.
(set-logic HORN)
(assert (forall ((x Int)) (distinct x x)))
(check-sat)
