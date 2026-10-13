; The shape of a slice walk, in twenty lines: an invariant relating TWO arrays
; at an offset.
;
;   I(a, b, i, n) = forall k. 0 <= k < n -> a[k] = b[i + k]
;
; It exists as the acceptance test for the one vocabulary the cell route is
; measured to be missing.  Every qualifier family generated from a predicate's
; parameters compares a cell column with a parameter, and the family that
; compares two cells compares two cells of ONE array; what this needs is two
; cells of two different arrays whose indices differ by a parameter.  The
; clause-driven lifting cannot supply it either: a clause states the relation
; only at the index it is written at, and generalising to every k is what the
; induction is for.
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
