; expected: sat
;
; The twin of the `unsat` file beside this one, differing only in the number the
; conclusion asks for: 11 is what the premise fixes, so the clause is valid and
; the problem -- which has no predicate variable -- is satisfiable.
;
; It pins the other direction of the same simplification.  Expanding an array
; literal whose index is confined to a finite concrete range into a chain of
; `store`s is exact, so it must not turn a valid clause into anything else; a
; rewrite that got the range wrong would most likely show up here rather than in
; the `unsat` twin, where a wrong array still leaves the premise satisfiable.
(set-logic HORN)
(assert (forall ((x0 (Array Int Int)) (x1 (Array Int Int)))
  (=> (and (= (store (lambda ((i Int)) (ite (and (< i 1) (>= i 0)) (select x0 (+ 1 i)) 0))
                     0
                     (select x1 1))
              (lambda ((i Int)) (ite (and (< i 1) (>= i 0)) (select x1 (+ 1 i)) 0)))
           (= (select x1 0) 11))
      (= (select x1 0) 11))))
(check-sat)
