; A satisfiable formula that Z3 does not decide, and the reason a solver-facing
; obligation over a universally quantified FUNCTION needs that function instantiated.
;
; Where it comes from.  A predicate constraint solver had a functional (total,
; single-valued) unknown occurring only as a premise.  The totality of such an unknown
; turns its clauses into one closed obligation -- for every argument tuple a result
; exists, so the clause holds at that result -- and refuting the obligation refutes the
; whole system.  The obligation keeps the clause's own universals, and one of them is a
; universally quantified function, which in SMT is an array-sorted variable.  Written
; out, with m, b, c the other universals:
;
;   forall m b c. exists i. forall a.
;     ( a[i] \/ not c[m] \/ (not b[m+1] /\ not b[m]) \/ (not b[i+1] /\ not b[i])
;             \/ (exists j. not b[j+1] /\ not b[j]) \/ (exists k. not a[k+1] /\ not a[k]) )
;
; asserted negated below, so `sat` here means the obligation is invalid and the original
; system is refuted.
;
; Why it is hard.  Refuting it asks the solver to INVENT an array: for each i, one that is
; false at i and never false twice in a row.  Measured 2026-09-14: Z3 answers neither at
; 20 s nor at 30 s; nor with the inner existential array Skolemised into an array of
; arrays; nor under smt.macro_finder=true, smt.mbqi=false or smt.ematching=false.  cvc5
; returns `unknown`.  Pinning b and c to the constant true array does not help either.
;
; expected: sat -- and the two files beside it are why.  fn_point_hole_witnessed_sat.smt2
; supplies every witness by hand and gets `sat` at once, so the formula really is
; satisfiable; fn_point_hole_instantiated_sat.smt2 supplies only the array and Z3 decides
; it in well under a second.
(set-logic ALL)
(declare-const m Int)
(declare-const b (Array Int Bool))
(declare-const c (Array Int Bool))
(assert (not
  (exists ((i Int))
    (forall ((a (Array Int Bool)))
      (or (select a i)
          (not (select c m))
          (and (not (select b (+ m 1))) (not (select b m)))
          (and (not (select b (+ i 1))) (not (select b i)))
          (exists ((j Int)) (and (not (select b (+ j 1))) (not (select b j))))
          (exists ((k Int)) (and (not (select a (+ k 1))) (not (select a k)))))))))
(check-sat)
