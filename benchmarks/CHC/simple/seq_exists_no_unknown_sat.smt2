; expected: sat
;
; Pins that the last question a problem gets once preprocessing has eliminated
; every unknown -- is the remaining constraint valid? -- is ASKED even when it
; quantifies over a sequence, with a budget, rather than refused for its shape.
; The solver's shape guard refuses a quantifier binding a sequence because some
; such queries never return; at this site refusing is giving up the answer, and
; a version that refused answered `unknown,0` here where the default answers
; `sat,0` in a quarter of a second.
;
; Why it is satisfiable: `Inv(x, s) := s = [x]` satisfies both clauses, the
; second with the witness `t = []`. `Inv` is eliminated before the loop, which
; leaves `forall x. exists t. [x] = t ++ [x]`, decided valid at once. The
; existential is not reduced to arithmetic by preprocessing (unlike one that
; reads the bound sequence only through its length), so the query still binds
; a sequence.
(set-logic HORN)
(declare-fun Inv (Int (Seq Int)) Bool)
(assert (forall ((x Int)) (Inv x (seq.unit x))))
(assert (forall ((x Int) (s (Seq Int)))
  (=> (Inv x s) (exists ((t (Seq Int))) (= s (seq.++ t (seq.unit x)))))))
(check-sat)
