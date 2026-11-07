; The query reads an array through a store under an addition, and the array is local to it, so a
; model-based projection onto inv's arguments must remove it: (store a 0 7)[x] + 1 = y with a[1] = 5
; leaves exactly x >= 2 (x = 0 gives 8, x = 1 gives 6).  A projection that stopped at the top of
; the atom returned the read unchanged, with a free, and dropped a[1] = 5.
; Reachable: (0,0), (1,1); neither meets the query, so the system is satisfiable.
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (inv x y))))
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (< x 1)) (inv (+ x 1) (+ y 1)))))
(assert (forall ((x Int) (y Int) (a (Array Int Int)))
  (=> (and (inv x y) (= (select a 1) 5) (= y (+ (select (store a 0 7) x) 1))) false)))
(check-sat)
