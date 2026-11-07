; Invariant of P: c agrees with b at every index except possibly j.  So
; overwriting c at j with b's value there gives b back, the query's body is
; unsatisfiable and the system has a model.  The auxiliary array x is read
; only at 0 and its read is pinned to b[j]; eliminating x must keep "c and b
; differ away from j", not weaken it to "c and b differ".
(set-logic HORN)
(declare-fun P ((Array Int Int) (Array Int Int) Int) Bool)
(assert (forall ((b (Array Int Int)) (j Int))
  (P (store b j (+ (select b j) 1)) b j)))
(assert (forall ((c (Array Int Int)) (b (Array Int Int)) (j Int) (k Int) (v Int))
  (=> (and (P c b j) (not (= k j)))
      (P (store c k v) (store b k v) j))))
(assert (forall ((c (Array Int Int)) (b (Array Int Int)) (j Int) (x (Array Int Int)))
  (=> (and (P c b j)
           (not (= (store c j (select x 0)) b))
           (= (select x 0) (select b j)))
      false)))
(check-sat)
