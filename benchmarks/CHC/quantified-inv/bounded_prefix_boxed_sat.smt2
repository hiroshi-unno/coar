; bounded_prefix_sat.smt2 with the array wrapped in a single-constructor
; datatype, which is the shape every Rust-derived input in this tree has: a
; function's arguments arrive as a tuple, so the array is never a parameter of
; the predicate but a field reachable from one.
;
; I(box a, i, bound) = forall j. 0 <= j <= i -> a[j] <= bound
;
; It exists because the index/value cell route counts array-SORTED PARAMETERS,
; so a predicate over a datatype holding an array gets no cells at all and the
; route is a no-op -- measured on the Rust-derived corpus, where every unknown
; takes such a datatype and none takes an array.  Keying the cells on the
; array-valued paths into the parameters is what this file is the test for.
(set-logic HORN)
(declare-datatypes ((Box 0)) (((box (unbox (Array Int Int))))))
(declare-fun I (Box Int Int) Bool)
(assert (forall ((a (Array Int Int)) (bound Int))
                (=> (<= (select a 0) bound) (I (box a) 0 bound))))
(assert (forall ((a (Array Int Int)) (i Int) (bound Int))
                (=> (and (I (box a) i bound) (<= (select a (+ i 1)) bound))
                    (I (box a) (+ i 1) bound))))
(assert (forall ((a (Array Int Int)) (i Int) (j Int) (bound Int))
                (=> (and (<= 0 j) (<= j i) (I (box a) i bound) (> (select a j) bound)) false)))
(check-sat)
