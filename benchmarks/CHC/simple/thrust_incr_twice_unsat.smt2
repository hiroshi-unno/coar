; A hand encoding, in Thrust's style, of
;   fn incr(x: &mut i64) { *x += 1; }
;   fn check(a: i64) { let mut v = a; incr(&mut v); incr(&mut v); assert!(v == a + 3); }
; pre/post are incr's pre- and postcondition over the mutable reference (current, final).
; Once pre is eliminated, post's defining clause is post(mut (x0 - 1) x0): one variable in
; both components of the constructor. Unifying it with an example atom whose second component
; is a parameter left x0 free in the parameter's image, and the resolution step then derived a
; negative example for every value where the clause refutes one: a wrong unsat on the safe side.
; Expected: unsat.
(set-logic HORN)
(declare-datatypes ((A0_Mut<Int> 0)) ((par () ((mut<Int> (mut_current<Int> Int) (mut_final<Int> Int))))))
(declare-fun pre (A0_Mut<Int>) Bool)
(declare-fun post (A0_Mut<Int>) Bool)
(assert (forall ((c Int) (f Int)) (=> (and (pre (mut<Int> c f)) (= f (+ c 1))) (post (mut<Int> c f)))))
(assert (forall ((a Int) (v1 Int)) (pre (mut<Int> a v1))))
(assert (forall ((a Int) (v1 Int) (v2 Int)) (=> (post (mut<Int> a v1)) (pre (mut<Int> v1 v2)))))
(assert (forall ((a Int) (v1 Int) (v2 Int)) (=> (and (post (mut<Int> a v1)) (post (mut<Int> v1 v2)) (not (= v2 (+ a 3)))) false)))
(check-sat)
