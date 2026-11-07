; Three datatype sorts whose readable printed names would collide: a nullary
; datatype the user named |Lst Int|, the instance (Lst Int) of a parametric
; datatype, and its instance (Lst int) at an uninterpreted sort spelled int.
; The printer must give the three distinct names, and printing its own output
; again must give the same names.  Expected: sat (P, Q, R := true).
(set-logic HORN)
(declare-sort int 0)
(declare-datatypes ((Lst 1)) ((par (T) ((nil) (cons (hd T) (tl (Lst T)))))))
(declare-datatypes ((|Lst Int| 0)) (((mk (val Int)))))
(declare-fun P ((Lst Int)) Bool)
(declare-fun Q ((Lst int)) Bool)
(declare-fun R (|Lst Int|) Bool)
(assert (forall ((l (Lst Int))) (=> (= l (cons 1 (as nil (Lst Int)))) (P l))))
(assert (forall ((x int) (l (Lst int))) (=> (= l (cons x (as nil (Lst int)))) (Q l))))
(assert (forall ((m |Lst Int|)) (=> (= (val m) 2) (R m))))
(assert (forall ((l (Lst Int))) (=> (and (P l) (= l (as nil (Lst Int)))) false)))
(check-sat)
