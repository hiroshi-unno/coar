; The shape of a slice walk, in twenty lines: an invariant relating TWO arrays
; at an offset.
;
;   I(a, b, i, n) = forall k. 0 <= k < n -> a[k] = b[i + k]
;
; The same system as two_arrays_offset_sat.smt2 with the invariant supplied, as
; the control for "is only synthesis missing?".
(set-logic HORN)
(define-fun I ((a (Array Int Int)) (b (Array Int Int)) (i Int) (n Int)) Bool
  (forall ((k Int)) (=> (and (<= 0 k) (< k n)) (= (select a k) (select b (+ i k))))))
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
