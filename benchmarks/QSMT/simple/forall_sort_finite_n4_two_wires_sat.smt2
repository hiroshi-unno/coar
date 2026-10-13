; The two-wire sibling of forall_sort_finite_n4_unsat.smt2, and a FALSIFIER for the sharpened
; judgement rule rather than another instance of it.
;
; The rule.  The refutation of the one-wire family needs two INCOMPARABLE interpretations of the
; predicate F can see, sharing one wire value: incomparability is what supplies the two points of
; difference h, h' and what keeps the premise satisfiable on both sides.  So a solution avoids the
; refutation exactly when the non-empty subsets of T can be covered by as many CHAINS as the wire
; has values.  By Dilworth's theorem that least number of chains is the largest antichain, and by
; Sperner's theorem the largest antichain in the subset lattice of an n-element set is
; C(n, floor(n/2)).  With r values on the wire the wire carries n^r combinations, so the rule fires
; exactly when C(n, floor(n/2)) > n^r.
;
; The prediction being tested here.  At r = 1 the least such n is 4 -- which is why the one-wire
; file at four elements is unsat while its n2 and n3 siblings are sat.  At r = 2 it is EIGHT
; (C(8,4) = 70 > 64, while C(7,3) = 35 <= 49), so this file, which is the same shape at four
; elements with a second wire value, must be **sat**.  If it were unsat the rule would be wrong:
; the count, not the shape, is what the rule claims to be doing the work.
;
; Why that matters beyond this file: it says the threshold is a computed quantity and not the
; constant 4 this one shape happens to have, so a generator must compute it, and a search over
; finitely many sizes must be told how far to go.
;
; Measured 2026-09-15.  The one-wire control at four elements is `unsat` in seconds, as it must be.
; **Z3 answers `unknown` on this file after 900 s** -- so this file does not confirm the
; prediction by itself, and it is not evidence until it answers.  What confirms it is the companion
; `forall_sort_finite_n4_two_wires_witness_sat.smt2`, which gives F and G explicitly and is `sat`:
; the wire pair is a bijection on 16 points, so no two interpretations collide at all and G reads
; back exactly what F saw.  Mutating that witness so the wire carries one value again makes it
; `unsat`, which is the same boundary from the third side.  This file is kept as the solver's
; challenge, with its verdict now settled by construction rather than by search.
;
; expected: sat
(set-logic ALL)
(declare-datatypes ((T 0)) (( (t0) (t1) (t2) (t3))))
(declare-fun F ( Bool Bool Bool Bool T T T) Bool)
(declare-fun G ( Bool Bool Bool Bool T T T T) Bool)
(define-fun at ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool) (t T)) Bool (ite (= t t0) a0 (ite (= t t1) a1 (ite (= t t2) a2 a3))))
(assert (forall ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool)  (b0 Bool) (b1 Bool) (b2 Bool) (b3 Bool) (x T) (w T))
  (=> (and (at a0 a1 a2 a3 w) (at b0 b1 b2 b3 w)) (exists ((y1 T) (y2 T)) (F a0 a1 a2 a3 x y1 y2)))))
(assert (forall ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool)  (b0 Bool) (b1 Bool) (b2 Bool) (b3 Bool) (x T) (w T) (y1 T) (y2 T))
  (=> (and (at a0 a1 a2 a3 w) (at b0 b1 b2 b3 w) (F a0 a1 a2 a3 x y1 y2)) (exists ((z T)) (G b0 b1 b2 b3 x y1 y2 z)))))
(assert (forall ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool)  (b0 Bool) (b1 Bool) (b2 Bool) (b3 Bool) (x T) (w T) (y1 T) (y2 T) (z T))
  (=> (and (at a0 a1 a2 a3 w) (at b0 b1 b2 b3 w) (F a0 a1 a2 a3 x y1 y2) (G b0 b1 b2 b3 x y1 y2 z)) (and (at a0 a1 a2 a3 z) (at b0 b1 b2 b3 z)))))
(check-sat)
