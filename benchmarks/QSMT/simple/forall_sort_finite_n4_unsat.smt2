; e5_rust_two_holes_a_wire_unsat with its `declare-forall-sort` T fixed at an 4-ELEMENT type,
; the predicates on T written as their 4 bits so the question is propositional.
;
; Why fixing the sort is sound in the direction used.  A forall-sort ranges over every non-empty
; type, so fixing one is an instance of that quantifier and therefore a weakening: `unsat` here means
; `unsat` for the original, while `sat` here means only that this type does not refute it.
;
; Why the three files are kept together.  The input's own proof is a pigeonhole -- two interpretations
; of one predicate on which the wire value agrees, then the two points of difference made valid under
; the other -- and the question a finite instantiation has to answer is HOW BIG a type that needs.
; Measured: |T| = 2 sat, |T| = 3 sat, |T| = 4 **unsat**.  Two and three elements leave too little room to pick the two points of
; difference; four is enough.  A mechanism that instantiates forall-sorts at small finite types would
; refute this input at the third try, and the pair of `sat` answers is what says it must not stop at
; the first.
;
; expected: unsat
(set-logic ALL)
(declare-datatypes ((T 0)) (( (t0) (t1) (t2) (t3))))
(declare-fun F ( Bool Bool Bool Bool T T) Bool)
(declare-fun G ( Bool Bool Bool Bool T T T) Bool)
(define-fun at ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool) (t T)) Bool (ite (= t t0) a0 (ite (= t t1) a1 (ite (= t t2) a2 a3))))
(assert (forall ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool)  (b0 Bool) (b1 Bool) (b2 Bool) (b3 Bool) (x T) (w T))
  (=> (and (at a0 a1 a2 a3 w) (at b0 b1 b2 b3 w)) (exists ((y T)) (F a0 a1 a2 a3 x y)))))
(assert (forall ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool)  (b0 Bool) (b1 Bool) (b2 Bool) (b3 Bool) (x T) (w T) (y T))
  (=> (and (at a0 a1 a2 a3 w) (at b0 b1 b2 b3 w) (F a0 a1 a2 a3 x y)) (exists ((z T)) (G b0 b1 b2 b3 x y z)))))
(assert (forall ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool)  (b0 Bool) (b1 Bool) (b2 Bool) (b3 Bool) (x T) (w T) (y T) (z T))
  (=> (and (at a0 a1 a2 a3 w) (at b0 b1 b2 b3 w) (F a0 a1 a2 a3 x y) (G b0 b1 b2 b3 x y z)) (and (at a0 a1 a2 a3 z) (at b0 b1 b2 b3 z)))))
(check-sat)
