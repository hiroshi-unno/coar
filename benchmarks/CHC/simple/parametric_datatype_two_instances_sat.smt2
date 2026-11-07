; One parametric datatype used at two instances, (Lst Int) and (Lst (Lst Int)):
; a size function shared by name between them would have two definitions.
; P holds of the lists of 1s, so (cons 2 nil) is not among them: sat.
(set-logic HORN)
(declare-datatypes ((Lst 1)) ((par (T) ((nil) (cons (hd T) (tl (Lst T)))))))
(declare-fun P ((Lst Int)) Bool)
(declare-fun Q ((Lst (Lst Int))) Bool)
(assert (forall ((x (Lst Int))) (=> (= x (as nil (Lst Int))) (P x))))
(assert (forall ((x (Lst Int)) (y (Lst Int))) (=> (and (P x) (= y (cons 1 x))) (P y))))
(assert (forall ((x (Lst (Lst Int)))) (=> (= x (as nil (Lst (Lst Int)))) (Q x))))
(assert (forall ((x (Lst (Lst Int))) (y (Lst (Lst Int)))) (=> (and (Q x) (= y (cons (as nil (Lst Int)) x))) (Q y))))
(assert (forall ((x (Lst Int))) (=> (and (P x) (= x (cons 2 (as nil (Lst Int))))) false)))
(check-sat)
