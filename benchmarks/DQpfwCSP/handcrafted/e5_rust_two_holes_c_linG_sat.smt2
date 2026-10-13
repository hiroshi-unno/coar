; E5-C-G  expected: sat   (linearised: G gets {ok1, ok2}, i.e. g<T: A + B>; rule A)
;
; Abstract model (Rust reading of e4): a generic combinator with two holes whose trait bounds differ.
;   trait A { fn ok1(&self) -> bool; }   trait B { fn ok2(&self) -> bool; }
;   fn f<T: A>(x: T) -> T { /* hole F: may call ok1 only */ }
;   fn g<T: B>(x: T, y: T) -> T { /* hole G: may call ok2 only */ }
;   fn combine<T: A + B>(x: T, ghost w: T) -> T   // requires w.ok1() && w.ok2()
;   { let y = f(x); let z = g(x, y); z }           // ensures z.ok1() && z.ok2()
; T is a universally quantified sort (declare-forall-sort: every non-empty type), ok1/ok2 are
; universally quantified predicates on it (the trait methods, unknown at synthesis time). The
; dependency set of a hole is the vocabulary its trait bound allows. The value y handed from f to g
; is the one-way wire of e4; the ghost w is e4's hidden witness (nobody receives it).
; Spec S: z is ok1 and ok2.
; Solution: F := true;  G := ok1 z /\ ok2 z (witness z := w).
; PCSat (2026-09-07): crashes, Failure "[gen_fun] T not supported" (see a_wire_unsat).
(set-logic DQHORN)
(declare-forall-sort T)
(declare-forall-fun ok1 (T) Bool)
(declare-forall-fun ok2 (T) Bool)
(define-fun A ((w T)) Bool (and (ok1 w) (ok2 w)))
(define-fun S ((z T)) Bool (and (ok1 z) (ok2 z)))
(declare-dep-exists-fun F (ok1) (T T) Bool)
(declare-dep-exists-fun G (ok1 ok2) (T T T) Bool)
(assert (forall ((x T) (w T)) (=> (A w) (exists ((y T)) (F x y)))))
(assert (forall ((x T) (w T) (y T)) (=> (and (A w) (F x y)) (exists ((z T)) (G x y z)))))
(assert (forall ((x T) (w T) (y T) (z T)) (=> (and (A w) (F x y) (G x y z)) (S z))))
