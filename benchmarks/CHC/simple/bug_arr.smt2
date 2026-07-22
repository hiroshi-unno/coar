(set-logic HORN)
(assert (forall ((A (Array Int Int)) (i Int))
    (=> (= 0 (select (store (store A 0 2) i 0) 0)) false)))

(check-sat)