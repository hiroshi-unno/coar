; Expected: unsat, and it answers so.  Kept because of how it used to fail.
;
; The clause is violated at l = (cons (const 0) 0): (len (cons a 0)) is 0 and (hd (cons a 0)) is a
; by the constructor axioms, so the premise holds and `false` is demanded -- and it holds that way
; in EVERY model, because both selectors are applied to the constructor they belong to.
;
; Between 2026-09-05 and 2026-09-12 this answered unknown,0.  The verdict was decided by asking
; whether the universal closure is satisfiable -- the other reading of satisfiability, under which
; a system is satisfiable if SOME model of the theory satisfies it -- and Z3 cannot decide such a
; closure once an array is involved.  The question asked here now is validity, for which Z3 finds
; a countermodel immediately.
(set-logic HORN)
(declare-datatypes ((L 0)) (((nil) (cons (hd (Array Int Int)) (len Int)))))
(assert (forall ((l L) (i Int))
  (=> (and (= (len l) 0) (= (select (hd l) i) 0)) false)))
(check-sat)
