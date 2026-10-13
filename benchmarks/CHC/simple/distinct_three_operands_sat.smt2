; expected: sat
;
; `(distinct x y x)` is false for every `x` and `y` -- SMT-LIB makes `distinct`
; false as soon as two of its arguments are equal, and the first and third are
; the same operand -- so its negation is valid and, with no unknown, the verdict
; is `sat`. z3 and cvc5 agree.
;
; It answered `unsat` because the operands were collected into a set before the
; pairwise disequalities were generated: the repeated `x` was dropped, what was
; left was `x != y`, and its negation `x = y` is not valid. The repetition is at
; the first and third positions on purpose -- the twin beside it repeats an
; adjacent pair -- so the two together pin that the repair compares list
; positions rather than removing duplicates.
;
; Ground repetitions do not show this: two separately parsed literals carry
; different fresh sort variables at that point, so `(distinct 0 1 0)` survived
; the deduplication and was refuted correctly all along.
(set-logic HORN)
(assert (forall ((x Int) (y Int)) (not (distinct x y x))))
(check-sat)
