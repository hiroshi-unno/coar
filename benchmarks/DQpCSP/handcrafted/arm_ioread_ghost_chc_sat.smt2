; POPL 2024's repair for `io-read-1`: the ghost parameter carries the read count into the
; handler, so the refinement may be indexed by the state it describes -- `A(nonempty, z)`.
; Middle file of the triple.  Plain CHC, satisfiable with `A(n, z) := (z = n)`.  expected: sat
(set-logic HORN)
(declare-fun A (Bool Bool) Bool)
(assert (A true true))      ; input remains: Ok
(assert (A false false))    ; no input: the invented Err
(assert (forall ((z Bool)) (=> (and (A true z) (not z)) false)))
(check-sat)
