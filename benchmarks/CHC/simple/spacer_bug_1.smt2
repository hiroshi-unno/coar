; spacer_bug_1.smt2
(set-logic HORN)
(declare-datatypes ((A0_List 0)) (((List.Cons (_getList.Cons.0 Int) (_getList.Cons.1 A0_List)) (List.Nil))))

(declare-fun p1 (Int A0_List) Bool)

(assert (forall ((A A0_List) (B Int) (C Int))
       (=> (and (p1 B A) (p1 C A)) (= B C))
    ))
(assert (forall ((A A0_List))
  (=> (= A List.Nil) (p1 1 A))))
(assert (forall ((A A0_List) (B Int) (D A0_List) (E Int) (F A0_List))
       (=> (and (p1 B D) (p1 B F) (= A (List.Cons (- E B) F))) (p1 E A))
    ))

(check-sat)