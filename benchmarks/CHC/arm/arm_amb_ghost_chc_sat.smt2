; POPL 2024's repair for `amb-3-simpl`: `select_from` is used in a context that supplies the
; searched element and the list, and the refinement is indexed by them -- `A(e, l, z)` -- which
; is what defining it inside the handler's closure achieves in the source.  Middle file of the
; triple.  Lists are abstracted to "does the element occur", the only thing the answer depends
; on.  Plain CHC, satisfiable with `A(occurs, z) := (z = occurs)`.  expected: sat
(set-logic HORN)
(declare-fun A (Bool Bool) Bool)     ; A(occurs, z): with the element present or not, the answer
(assert (A false false))             ; absent: the search answers false
(assert (A true true))               ; present: the angelic handler finds it
(assert (forall ((z Bool)) (=> (and (A true z) (not z)) false)))   ; the specification
(check-sat)
