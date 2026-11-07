; A closure-like precondition left to inference over a mutable borrow `f`, whose final
; value `fin f` is a prophecy.  The body, run with the precondition `p`, steps the borrow
; (`fin f = cur f + 1`) and must show `cur f = s`; the caller establishes `p` for every
; prophecy `g`; the loop step assumes it beneath a universal at the borrow's current value.
; Expected sat: p(s, f) := cur f = s and inv(i, c) := c = i.  `p := true` is no solution
; (the body's obligation then has nothing to rest on).
(set-logic HORN)
(declare-datatypes ((M 0)) (((mut (cur Int) (fin Int)))))
(declare-fun p (Int M) Bool)
(declare-fun inv (Int Int) Bool)
(assert (forall ((s Int) (f M)) (=> (and (p s f) (= (fin f) (+ (cur f) 1))) (= (cur f) s))))
(assert (inv 0 0))
(assert (forall ((i Int) (c Int) (g Int)) (=> (inv i c) (p i (mut c g)))))
(assert (forall ((i Int) (c Int)) (=> (and (inv i c) (forall ((j Int)) (=> (and (>= j i) (<= j i)) (p j (mut c c))))) (inv (+ i 1) (+ c 1)))))
(check-sat)
