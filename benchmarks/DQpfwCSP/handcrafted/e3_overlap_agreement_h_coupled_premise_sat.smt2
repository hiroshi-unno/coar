; E3-H-coupled  expected: sat   (rule C does NOT apply; the file exists to show why its product
; hypothesis is not decorative)
;
; This is e3_overlap_agreement_g_pair_disjoint_unsat.smt2 with ONE change: the premise Phi, besides
; the adjacency it already stated for Q2, now says that Q1 and Q3 agree with Q2 everywhere.  The
; dependency sets are untouched -- Dev1 sees Q1 only, Dev2 sees Q3 only, and their intersection is
; still empty, which is the hypothesis rule C is usually quoted by.
;
; Rule C's proof runs: agreement forces both output sets to be one singleton {c} with
; c = f1(i, Q1) = f2(i, Q3); since f1 cannot read Q3 and f2 cannot read Q1, c depends only on
; D1 n D2; that is empty, so c is a constant; the adversary then removes it from Q2.  **The middle
; step is where a product is used.**  "f1 does not depend on Q3" means f1 is constant along the Q3
; axis -- which is a statement about a SPACE, not about a signature, and it is true only when Q3 can
; be varied with Q1 held fixed.  Here it cannot: Phi ties both to Q2, so knowing Q1 is knowing Q3,
; and c may depend on everything while reading only its own predicate.
;
; And it does: the solution is the deterministic choice of rule A2,
;
;   Dev1 i c  :=  c = (ite (Q1 i) i (+ i 1))        Dev2 i c  :=  c = (ite (Q3 i) i (+ i 1))
;
; which are the SAME function under Phi, because Phi makes Q1 = Q3 = Q2; the adjacency then makes
; the chosen point usable, so S holds.  Agreement comes from the two deciders computing one
; expression, not from communication -- which is exactly A2's shape.
;
; What it is evidence for: applying rule C to a file by checking only "the dependency sets are
; disjoint" would call this unsat, and it is sat.  The hypothesis to check is that the admissible
; interpretations form a PRODUCT, i.e. that the premise constrains each predicate separately.  Its
; disjoint sibling next to this file has exactly that (Phi there mentions Q2 alone) and is unsat.
(set-logic DQHORN)
(declare-forall-fun Q1 (Int) Bool)
(declare-forall-fun Q2 (Int) Bool)
(declare-forall-fun Q3 (Int) Bool)
(define-fun Phi () Bool (and
  (forall ((h Int)) (or (Q2 h) (Q2 (+ h 1))))
  (forall ((h Int)) (= (Q1 h) (Q2 h)))
  (forall ((h Int)) (= (Q3 h) (Q2 h)))))
(define-fun S ((c1 Int) (c2 Int)) Bool (and (= c1 c2) (Q2 c1)))
(declare-dep-exists-fun Dev1 (Q1) (Int Int) Bool)
(declare-dep-exists-fun Dev2 (Q3) (Int Int) Bool)
(assert (forall ((i Int)) (=> Phi (exists ((c Int)) (Dev1 i c)))))
(assert (forall ((i Int)) (=> Phi (exists ((c Int)) (Dev2 i c)))))
(assert (forall ((i Int) (c1 Int) (c2 Int)) (=> (and Phi (Dev1 i c1) (Dev2 i c2)) (S c1 c2))))
