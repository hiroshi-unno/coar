; expected: unsat
;
; The companion of `bounded_array_literal_unsat.smt2`, differing in the one
; thing that decides which mechanism has to answer it: the array literals here
; are bounded by a VARIABLE, so nothing can expand them into a chain of stores,
; and the solver goes on saying "incomplete (theory array)" about a goal that is
; otherwise ground.
;
; The clause is invalid -- at n = 0 both literals are the constant 0 array, so
; the premise holds while the conclusion asks for 12 where the premise fixes 11.
; Finding that needs a guess, and the guess is sound in one direction only: a
; refutation is a model of the NEGATED constraint, and adding conjuncts to a
; negation only removes models, so a satisfiable strengthening is still a
; refutation while an unsatisfiable one says nothing. Pinning the terms that
; bound an array literal's index to small integers is the strengthening, and it
; is tried only where the answer would otherwise be `unknown`.
;
; PCSat: `unknown,0` before that search existed, `unsat,0` since.
(set-logic HORN)
(assert (forall ((n Int) (x0 (Array Int Int)) (x1 (Array Int Int)))
  (=> (and (= (lambda ((i Int)) (ite (and (< i n) (>= i 0)) (select x0 i) 0))
              (lambda ((i Int)) (ite (and (< i n) (>= i 0)) (select x1 i) 0)))
           (= (select x0 0) 11))
      (= (select x0 0) 12))))
(check-sat)
