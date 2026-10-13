; The law on a universally quantified function written where the function is declared, rather
; than repeated in every clause that needs it.  `:law` is *defined* as the expansion into the
; plain declaration plus that premise, inserted into each following assertion that mentions the
; function -- so this file and fresh_function_law_sat.smt2 beside it are the same problem, and
; both answer sat with Q(x, y) := (x != y).
;
; Writing the law with the clause's own variable name, as here, instantiates it at that
; variable; writing it closed, under its own forall, nests it instead -- also sound, and more
; work for the solver.
;
; Why it cannot be a top-level assertion: `fresh` is universal in every clause, so asserting the
; law on its own would read as "this holds for every interpretation of fresh", which none does.
; As a premise it reads "for every fresh satisfying the law", which is what a law means.
;
; expected: sat
(set-logic DQHORN)
(declare-forall-sort a)
(declare-forall-fun fresh (a) a :law (distinct (fresh x) x))
(declare-fun Q (a a) Bool)
(assert (forall ((x a)) (Q x (fresh x))))
(assert (forall ((x a) (y a)) (=> (and (Q x y) (= x y)) false)))
(check-sat)
