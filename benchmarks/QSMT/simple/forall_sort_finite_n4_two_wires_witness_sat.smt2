; The WITNESS for forall_sort_finite_n4_two_wires_sat.smt2 beside it: the same three clauses with F
; and G given explicitly, so that the construction the sharpened judgement rule promises is machine
; checked rather than searched for.  Z3 does not find the solution for the declared version in 180 s;
; checking one takes no search at all, and it is the construction that the rule's sat direction is.
;
; The rule says a solution exists exactly when the non-empty subsets of T can be covered by as many
; chains as the wire has values.  With two wire values over a four-element T the wire carries 16
; combinations against 15 non-empty subsets, so the easiest cover is the extreme one: make the map
; from the predicate F sees to the wire pair INJECTIVE, and no two interpretations share a wire value
; at all, incomparable or not.
;
;   F sends the four bits a0..a3 to the pair (t[2*a0+a1], t[2*a2+a3]) -- a bijection on 16 points.
;   G reads the pair back (a0 is y1 in {t2,t3}, a1 is y1 in {t1,t3}, and likewise a2, a3 from y2),
;   which recovers exactly the interpretation F saw, and then outputs any z valid under both that
;   and its own b.  Such a z exists: the premise supplies a w valid under both.
;
; G never sees a0..a3.  It recovers them from the wire, which is what a wire is for, and which is
; exactly what the one-wire version cannot afford: there, 4 values must carry 15 subsets, two
; incomparable ones collide, and the collision is the refutation.
;
; expected: sat   (sat here means the three clauses HOLD of these definitions; with F and G defined
; the assertions are closed, so `unsat` would mean the construction is wrong)
(set-logic ALL)
(declare-datatypes ((T 0)) (( (t0) (t1) (t2) (t3))))
(define-fun at ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool) (t T)) Bool (ite (= t t0) a0 (ite (= t t1) a1 (ite (= t t2) a2 a3))))
(define-fun enc ( (p Bool) (q Bool)) T (ite p (ite q t3 t2) (ite q t1 t0)))
(define-fun hi ( (y T)) Bool (or (= y t2) (= y t3)))
(define-fun lo ( (y T)) Bool (or (= y t1) (= y t3)))
(define-fun F ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool) (x T) (y1 T) (y2 T)) Bool
  (and (= y1 (enc a0 a1)) (= y2 (enc a2 a3))))
(define-fun G ( (b0 Bool) (b1 Bool) (b2 Bool) (b3 Bool) (x T) (y1 T) (y2 T) (z T)) Bool
  (and (at (hi y1) (lo y1) (hi y2) (lo y2) z) (at b0 b1 b2 b3 z)))
(assert (forall ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool)  (b0 Bool) (b1 Bool) (b2 Bool) (b3 Bool) (x T) (w T))
  (=> (and (at a0 a1 a2 a3 w) (at b0 b1 b2 b3 w)) (exists ((y1 T) (y2 T)) (F a0 a1 a2 a3 x y1 y2)))))
(assert (forall ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool)  (b0 Bool) (b1 Bool) (b2 Bool) (b3 Bool) (x T) (w T) (y1 T) (y2 T))
  (=> (and (at a0 a1 a2 a3 w) (at b0 b1 b2 b3 w) (F a0 a1 a2 a3 x y1 y2)) (exists ((z T)) (G b0 b1 b2 b3 x y1 y2 z)))))
(assert (forall ( (a0 Bool) (a1 Bool) (a2 Bool) (a3 Bool)  (b0 Bool) (b1 Bool) (b2 Bool) (b3 Bool) (x T) (w T) (y1 T) (y2 T) (z T))
  (=> (and (at a0 a1 a2 a3 w) (at b0 b1 b2 b3 w) (F a0 a1 a2 a3 x y1 y2) (G b0 b1 b2 b3 x y1 y2 z)) (and (at a0 a1 a2 a3 z) (at b0 b1 b2 b3 z)))))
(check-sat)
