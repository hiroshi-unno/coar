; The same system with the intended invariant supplied, as the control for
; "is only synthesis missing?": I(a,i,bound) = forall j. 0<=j<=i -> a[j]<=bound
(set-logic HORN)
(define-fun I ((a (Array Int Int)) (i Int) (bound Int)) Bool
  (forall ((j Int)) (=> (and (<= 0 j) (<= j i)) (<= (select a j) bound))))
(assert (forall ((a (Array Int Int)) (bound Int))
                (=> (<= (select a 0) bound) (I a 0 bound))))
(assert (forall ((a (Array Int Int)) (i Int) (bound Int))
                (=> (and (I a i bound) (<= (select a (+ i 1)) bound))
                    (I a (+ i 1) bound))))
(assert (forall ((a (Array Int Int)) (i Int) (j Int) (bound Int))
                (=> (and (<= 0 j) (<= j i) (I a i bound) (> (select a j) bound)) false)))
(check-sat)
