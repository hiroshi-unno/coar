; A closure's precondition and postcondition left to inference and assumed by a library loop beneath a
; universal (written by hand in the shape of a Thrust-emitted problem for a coroutine's values).
; pre(x, c) and post(r, c, x) are the contract of the closure |x| x == c.  find's loop invariant is written:
; post(false, c, s[k]) for every k already passed.  The reader skolemises the invariant assumed in the step
; clause into a witness index, which would have to be one at which the closure rejected for every k at once,
; so no witness term exists.  The twin of closure_post_find_sat: the caller claims every element is c.
; expected: unsat (the caller claims every element is c)
(set-logic HORN)
(declare-fun pre (Int Int) Bool)
(declare-fun post (Bool Int Int) Bool)
; the closure's body under its precondition
(assert (forall ((x Int) (c Int)) (=> (pre x c) (post (= x c) c x))))
; find's requires at the call site: the precondition for every element
(assert (forall ((c Int) (x Int)) (pre x c)))
; find's loop step: the invariant at i and a rejecting call at s[i] give the invariant at i + 1
(assert (forall ((s (Seq Int)) (c Int) (i Int))
  (=> (and (<= 0 i) (< i (seq.len s))
           (forall ((k Int)) (=> (and (<= 0 k) (< k i)) (post false c (seq.nth s k))))
           (post false c (seq.nth s i)))
      (forall ((k Int)) (=> (and (<= 0 k) (< k (+ i 1))) (post false c (seq.nth s k)))))))
; the caller, after find returned None: no element is c
(assert (forall ((s (Seq Int)) (c Int) (k Int))
  (=> (and (forall ((j Int)) (=> (and (<= 0 j) (< j (seq.len s))) (post false c (seq.nth s j))))
           (<= 0 k) (< k (seq.len s)))
      (= (seq.nth s k) c))))
