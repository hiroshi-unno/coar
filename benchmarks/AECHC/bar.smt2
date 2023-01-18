; test for constraints with existential quantifiers
; a solution: p(m,n) := m>n,  q(m,n) := n=m
(set-logic HORN)
(declare-fun p (Int Int) Bool)
(declare-fun q (Int Int) Bool)

(assert (forall ((m Int) (n Int))
  (=> (> m n)
      (p m n))))
(assert (forall ((m Int) (n Int) (r Int))
  (=> (and (p m n) (q m r))
      (< n r))))
      
(assert (forall ((m Int))
  (=> true
      (exists ((r Int)) (q m r)))))
