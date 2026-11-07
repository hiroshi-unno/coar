; Commutativity of multiplication by repeated addition, asked about two
; copies of the graph, as a frontend that copies a function's predicates
; per call site states it: K1 and K2 are mult's graph restricted to the
; argument pairs reachable from the calls mult a b and mult b a with a, b
; unrestricted (the argument predicates A1, A2), and W is mult's whole
; graph.  The lemmas say that each copy is contained in W, and that
; mult x y = r implies mult (x - 1) y = r - y, of W.  All three are proved
; by MuCyc's relational search before they are used.  The query, over K1
; and K2, is then not proved by induction on a K1 atom: the lemma's
; conclusion is a W atom, and the induction hypothesis speaks about K1 and
; K2.  With "generalise_goals_by_containment": true in the MuCyc
; configuration, the query with K1 and K2 replaced by W is tried as a
; conjecture, proved by induction on W, and closes the query through the
; containments.  The lemmas are given by (set-info :coar-lemma ...), which
; only that search reads.  Expected: sat.
(set-logic HORN)
(declare-fun W (Int Int Int) Bool)
(declare-fun A1 (Int Int) Bool)
(declare-fun K1 (Int Int Int) Bool)
(declare-fun A2 (Int Int) Bool)
(declare-fun K2 (Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (r Int))
  (=> (and (= y 0) (= r 0)) (W x y r))))
(assert (forall ((x Int) (y Int) (r Int) (y1 Int) (r1 Int))
  (=> (and (W x y1 r1) (not (= y 0)) (= y (+ y1 1)) (= r (+ x r1))) (W x y r))))
(assert (forall ((x Int) (y Int)) (A1 x y)))
(assert (forall ((x Int) (y Int))
  (=> (and (A1 x y) (not (= y 0))) (A1 x (- y 1)))))
(assert (forall ((x Int) (y Int) (r Int))
  (=> (and (A1 x y) (= y 0) (= r 0)) (K1 x y r))))
(assert (forall ((x Int) (y Int) (r Int) (y1 Int) (r1 Int))
  (=> (and (A1 x y) (K1 x y1 r1) (not (= y 0)) (= y (+ y1 1)) (= r (+ x r1)))
      (K1 x y r))))
(assert (forall ((x Int) (y Int)) (A2 x y)))
(assert (forall ((x Int) (y Int))
  (=> (and (A2 x y) (not (= y 0))) (A2 x (- y 1)))))
(assert (forall ((x Int) (y Int) (r Int))
  (=> (and (A2 x y) (= y 0) (= r 0)) (K2 x y r))))
(assert (forall ((x Int) (y Int) (r Int) (y1 Int) (r1 Int))
  (=> (and (A2 x y) (K2 x y1 r1) (not (= y 0)) (= y (+ y1 1)) (= r (+ x r1)))
      (K2 x y r))))
(assert (forall ((x Int) (y Int) (r1 Int) (r2 Int))
  (=> (and (K1 x y r1) (K2 y x r2)) (= r1 r2))))
(set-info :coar-lemma
  (forall ((x Int) (y Int) (r Int)) (=> (K1 x y r) (W x y r))))
(set-info :coar-lemma
  (forall ((x Int) (y Int) (r Int)) (=> (K2 x y r) (W x y r))))
(set-info :coar-lemma
  (forall ((x Int) (y Int) (r Int))
    (=> (W x y r) (W (- x 1) y (- r y)))))
(check-sat)
