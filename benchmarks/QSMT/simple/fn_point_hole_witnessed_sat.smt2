; The ground truth for fn_point_hole_uninstantiated_sat.smt2: every witness supplied by
; hand, so that `sat` here settles that the formula really is satisfiable and the solver's
; failure to decide it is a failure to search rather than a wrong expectation.
;
; The witnesses are
;   b = c = the constant true array   -- so no b-disjunct and no c-disjunct can fire, and
;   a_i = (lambda n. (n - i) is odd)  -- false at i, and alternating, so never false twice
;                                        in a row.
;
; Note that this is NOT the witness the instantiated twin uses.  That one offers the much
; simpler (lambda n. n /= i), which works for the same reason and is the candidate a
; solver can be expected to be handed.  Both are recorded because the parity array is what
; was found first by hand and the point hole is what a mechanical candidate family
; produces -- the gap between them is the reason such a family is worth having.
;
; expected: sat
(set-logic ALL)
(declare-const m Int)
(define-fun b () (Array Int Bool) ((as const (Array Int Bool)) true))
(define-fun c () (Array Int Bool) ((as const (Array Int Bool)) true))
(define-fun a ((i Int)) (Array Int Bool)
  (lambda ((n Int)) (not (= (mod (- n i) 2) 0))))
(assert (select c m))
(assert (forall ((j Int)) (or (select b (+ j 1)) (select b j))))
(assert (forall ((i Int))
  (and (not (select (a i) i))
       (forall ((k Int)) (or (select (a i) (+ k 1)) (select (a i) k))))))
(check-sat)
