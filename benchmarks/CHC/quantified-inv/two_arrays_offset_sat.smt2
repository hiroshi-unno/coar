; The shape of a slice walk, in twenty lines: an invariant relating TWO arrays
; at an offset.
;
;   I(a, b, i, n) = forall k. 0 <= k < n -> a[k] = b[i + k]
;
; It was written as the acceptance test for a missing vocabulary -- two cells of
; two DIFFERENT arrays whose indices differ by a parameter -- and that reading is
; refuted.  The vocabulary exists and is generated: the index offsets and the
; value equality between two arrays' cells are seven qualifiers here, the space
; grows from 30 to 37 with them, and this file still gives no verdict at 90 s.
; Nor is it the index set: with the enumeration's product bound cleared, so that
; every pair of candidate indices is offered, and again with the pairs narrowed
; to those whose indices differ by an argument, and again with the indices the
; refuting model itself named -- no verdict in any of them.
;
; What it demonstrates instead is why a finite set of instances cannot pin a
; universal demand.  The head atom says "for every k", the constraint says it at
; the sampled k, and a candidate true there and false elsewhere satisfies
; everything the synthesizer is given, is refuted by the validator, and comes
; back as the same counterexample: 767 of 801 in one run were the base clause,
; I(a, b, i, 0), which n = 0 makes vacuous.  The invariant above IS expressible
; in the space -- 0 <= k and k < n are comparisons of a cell index with a
; parameter, the offset and the value equality are the cross-array pair -- so
; what is missing is not what a candidate can say.
;
; So this is a twenty-line acceptance test for whatever answers that, and it
; should not be quoted as evidence about a vocabulary.
(set-logic HORN)
(declare-fun I ((Array Int Int) (Array Int Int) Int Int) Bool)
(assert (forall ((a (Array Int Int)) (b (Array Int Int)) (i Int))
                (I a b i 0)))
(assert (forall ((a (Array Int Int)) (b (Array Int Int)) (i Int) (n Int))
                (=> (and (I a b i n) (<= 0 n) (= (select a n) (select b (+ i n))))
                    (I a b i (+ n 1)))))
(assert (forall ((a (Array Int Int)) (b (Array Int Int)) (i Int) (n Int) (k Int))
                (=> (and (<= 0 k) (< k n) (I a b i n)
                         (not (= (select a k) (select b (+ i k)))))
                    false)))
(check-sat)
