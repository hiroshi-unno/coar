; Commutativity of multiplication defined by repeated addition: P(x, y, r)
; is the graph of mult x y (recursion on y), and the query asks that
; P(x, y, r1) and P(y, x, r2) imply r1 = r2.  The relational proof search of
; MuCyc (config/solver/mucyc_relational.json) proves the query by induction
; once it has the lemma below, which it first proves by induction itself:
; mult x y = r implies mult (x - 1) y = r - y.  The lemma is given by
; (set-info :coar-lemma ...), which only that search reads; for every other
; solver the problem is the assertions alone.  Expected: sat.
(set-logic HORN)
(declare-fun P (Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (r Int))
  (=> (and (= y 0) (= r 0)) (P x y r))))
(assert (forall ((x Int) (y Int) (r Int) (y1 Int) (r1 Int))
  (=> (and (P x y1 r1) (not (= y 0)) (= y (+ y1 1)) (= r (+ x r1))) (P x y r))))
(assert (forall ((x Int) (y Int) (r1 Int) (r2 Int))
  (=> (and (P x y r1) (P y x r2)) (= r1 r2))))
(set-info :coar-lemma
  (forall ((x Int) (y Int) (r Int))
    (=> (P x y r) (P (- x 1) y (- r y)))))
(check-sat)
