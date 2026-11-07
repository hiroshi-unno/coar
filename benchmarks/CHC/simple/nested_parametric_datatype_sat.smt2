; A datatype nested through a parametric one: Tree's children are a (Lst Tree).
; P relates a tree to its number of nodes, which is at least 1, so the query
; clause never fires: sat (z3 4.x answers sat).
(set-logic HORN)
(declare-datatypes ((Lst 1)) ((par (T) ((nil) (cons (hd T) (tl (Lst T)))))))
(declare-datatypes ((Tree 0)) (((node (val Int) (kids (Lst Tree))))))
(declare-fun P (Tree Int) Bool)
(declare-fun Q ((Lst Tree) Int) Bool)
(assert (forall ((v Int) (ks (Lst Tree)) (n Int)) (=> (Q ks n) (P (node v ks) (+ n 1)))))
(assert (forall ((n Int)) (=> (= n 0) (Q (as nil (Lst Tree)) n))))
(assert (forall ((t Tree) (ks (Lst Tree)) (a Int) (b Int)) (=> (and (P t a) (Q ks b)) (Q (cons t ks) (+ a b)))))
(assert (forall ((t Tree) (a Int)) (=> (and (P t a) (< a 1)) false)))
(check-sat)
