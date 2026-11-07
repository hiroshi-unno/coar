(set-logic HORN)
(declare-datatypes ((W 0)) (((mk (arr (Array Int Int))))))
(declare-datatypes ((L 0)) (((nil) (cons (hd W) (tl L)))))
(declare-fun p (Int) Bool)
(assert (forall ((n Int)) (p n)))
; the two records are one (the arrays agree everywhere: index 7 is overwritten),
; so in a background with hd nil equal to it the goal fails: unsat
(assert (forall ((n Int)) (=> (and (p n) (= (hd nil) (mk (store (lambda ((x Int)) x) 7 0)))) (not (= (hd nil) (mk (store (lambda ((x Int)) (ite (= x 7) 1 x)) 7 0)))))))
(check-sat)
