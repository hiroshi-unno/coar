; The same system under a 1-cell abstraction, by hand.
; I#(j, v, i, bound) with v = a[j]; concretization is
;   I(a,i,bound) := forall j. I#(j, a[j], i, bound).
; Body atoms are instantiated at every index term the clause reads the array
; at, together with the fresh index the head is proved at.
(set-logic HORN)
(declare-fun I# (Int Int Int Int) Bool)
(assert (forall ((a (Array Int Int)) (bound Int) (j Int))
                (=> (<= (select a 0) bound) (I# j (select a j) 0 bound))))
(assert (forall ((a (Array Int Int)) (i Int) (bound Int) (j Int))
                (=> (and (I# (+ i 1) (select a (+ i 1)) i bound)
                         (I# j (select a j) i bound)
                         (<= (select a (+ i 1)) bound))
                    (I# j (select a j) (+ i 1) bound))))
(assert (forall ((a (Array Int Int)) (i Int) (j Int) (bound Int))
                (=> (and (<= 0 j) (<= j i) (I# j (select a j) i bound)
                         (> (select a j) bound)) false)))
(check-sat)
