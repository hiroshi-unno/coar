; The shape of a slice walk, in twenty lines: an invariant relating TWO arrays
; at an offset.
;
;   I(a, b, i, n) = forall k. 0 <= k < n -> a[k] = b[i + k]
;
; sat: the invariant above satisfies all three clauses.
;
; It tests two things a solver needs at once.  The invariant compares cells of
; two different arrays whose indices differ by a parameter, so a vocabulary of
; one array's cells against parameters, or of two cells of one array, cannot
; state it.  And no clause states the relation for every k: each states it only
; at the index it reads, and generalising to every k is what the induction is
; for, so a candidate true at the sampled indices and false elsewhere fits
; everything a finite set of instances says.
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
