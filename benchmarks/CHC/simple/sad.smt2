(set-logic HORN)
(define-fun rel->=-out ((out Int) (x1 Int) (x2 Int)) Bool
 (ite (>= x1 x2) (= out 0) (= out 1)))
(define-fun rel->-out ((out Int) (x1 Int) (x2 Int)) Bool
 (ite (> x1 x2) (= out 0) (= out 1)))
(define-fun rel-<-out ((out Int) (x1 Int) (x2 Int)) Bool
 (ite (< x1 x2) (= out 0) (= out 1)))
(define-fun rel-<=-out ((out Int) (x1 Int) (x2 Int)) Bool
 (ite (<= x1 x2) (= out 0) (= out 1)))
(define-fun rel-=-out ((out Int) (x1 Int) (x2 Int)) Bool
 (ite (= x1 x2) (= out 0) (= out 1)))
(define-fun times-*-out ((out Int) (x1 Int) (x2 Int)) Bool (= out (* x1 x2)))
(define-fun minus---out ((out Int) (x1 Int) (x2 Int)) Bool (= out (- x1 x2)))
(define-fun plus-+-out ((out Int) (x1 Int) (x2 Int)) Bool (= out (+ x1 x2)))
(define-fun uneq ((x1 Int) (x2 Int)) Bool (not (= x1 x2)))
(declare-fun call-15-nxt-out-nxt->*->0 (Int Int Int Int Int Int Int Int Bool)
 Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int)
   (!g7 Int))
  (call-15-nxt-out-nxt->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 !g7 false)))
(declare-fun call-15-nxt-out-nxt->*->1->*->0
 (Int Int Int Int Int Int Int Int Int Bool) Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int)
   (!g7 Int) (!g8 Int))
  (call-15-nxt-out-nxt->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 !g7 !g8 false)))
(declare-fun call-2-nxt-out-nxt->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (call-2-nxt-out-nxt->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun call-2-nxt-out-nxt->*->1->*->0
 (Int Int Int Int Int Int Int Bool) Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int))
  (call-2-nxt-out-nxt->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 false)))
(declare-fun call-23-hd-out-hd->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (call-23-hd-out-hd->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun call-23-hd-out-hd->*->1->*->0 (Int Int Int Int Int Int Bool)
 Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (call-23-hd-out-hd->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun call-30-l-out-l->*->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (call-30-l-out-l->*->*->0 !g0 !g1 !g2 false)))
(declare-fun call-30-l-out-l->*->*->1->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (call-30-l-out-l->*->*->1->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun call-32-l-out-l->*->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (call-32-l-out-l->*->*->0 !g0 !g1 !g2 false)))
(declare-fun call-32-l-out-l->*->*->1->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (call-32-l-out-l->*->*->1->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun call-34-l-out-l->*->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (call-34-l-out-l->*->*->0 !g0 !g1 !g2 false)))
(declare-fun call-34-l-out-l->*->*->1->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (call-34-l-out-l->*->*->1->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun call-36-l-out-l->*->*->0 (Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int)) (call-36-l-out-l->*->*->0 !g0 !g1 false)))
(declare-fun call-36-l-out-l->*->*->1->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (call-36-l-out-l->*->*->1->*->0 !g0 !g1 !g2 false)))
(declare-fun call-9-hd-out-hd->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (call-9-hd-out-hd->*->0 !g0 !g1 !g2 false)))
(declare-fun call-9-hd-out-hd->*->1->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (call-9-hd-out-hd->*->1->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun fold-14-p->*->0 (Int Int Int Int Int Int Int Bool) Bool)
(declare-fun fold-14-p->*->1->*->0 (Int Int Int Int Int Int Int Int Bool)
 Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int)
   (!g7 Int))
  (fold-14-p->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 !g7 false)))
(declare-fun fold-19-p->*->0 (Int Int Int Int Int Int Int Bool) Bool)
(declare-fun fold-19-p->*->1->*->0 (Int Int Int Int Int Int Int Int Bool)
 Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int)
   (!g7 Int))
  (fold-19-p->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 !g7 false)))
(declare-fun fold-53-__t2->*->0 (Int Int Int Int Int Int Int Bool) Bool)
(declare-fun fold-53-__t2->*->1->*->0 (Int Int Int Int Int Int Int Int Bool)
 Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int)
   (!g7 Int))
  (fold-53-__t2->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 !g7 false)))
(declare-fun fold-62-__t3->*->0 (Int Int Int Int Int Int Int Bool) Bool)
(declare-fun fold-62-__t3->*->1->*->0 (Int Int Int Int Int Int Int Int Bool)
 Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int)
   (!g7 Int))
  (fold-62-__t3->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 !g7 false)))
(declare-fun fold-72-__t2->*->0 (Int Int Int Int Int Bool) Bool)
(declare-fun fold-72-__t2->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (fold-72-__t2->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun fresh_list-ret-RET->*->*->0 (Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int)) (fresh_list-ret-RET->*->*->0 !g0 !g1 false)))
(declare-fun fresh_list-ret-RET->*->*->1->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (fresh_list-ret-RET->*->*->1->*->0 !g0 !g1 !g2 false)))
(declare-fun ifnull-12-hd->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (ifnull-12-hd->*->0 !g0 !g1 !g2 false)))
(declare-fun ifnull-12-hd->*->1->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (ifnull-12-hd->*->1->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun ifnull-18-nxt->*->0 (Int Int Int Int Int Int Int Int Bool) Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int)
   (!g7 Int))
  (ifnull-18-nxt->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 !g7 false)))
(declare-fun ifnull-18-nxt->*->1->*->0
 (Int Int Int Int Int Int Int Int Int Bool) Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int)
   (!g7 Int) (!g8 Int))
  (ifnull-18-nxt->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 !g7 !g8 false)))
(declare-fun ifnull-26-hd->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (ifnull-26-hd->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun ifnull-26-hd->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (ifnull-26-hd->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun ifnull-5-nxt->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (ifnull-5-nxt->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun ifnull-5-nxt->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (ifnull-5-nxt->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun ifnull-64-__t1->*->0 (Int Int Int Int Int Int Int Bool) Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int))
  (ifnull-64-__t1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 false)))
(declare-fun ifnull-64-__t1->*->1->*->0
 (Int Int Int Int Int Int Int Int Bool) Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int)
   (!g7 Int))
  (ifnull-64-__t1->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 !g7 false)))
(declare-fun ifnull-74-__t0->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (ifnull-74-__t0->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun ifnull-74-__t0->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (ifnull-74-__t0->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun ifnull-76-__t0->*->0 (Int Int Bool) Bool)
(assert (forall ((!g0 Int) (!g1 Int)) (ifnull-76-__t0->*->0 !g0 !g1 false)))
(declare-fun ifnull-76-__t0->*->1->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (ifnull-76-__t0->*->1->*->0 !g0 !g1 !g2 false)))
(declare-fun insert-p-in-p->*->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (insert-p-in-p->*->*->0 !g0 !g1 !g2 false)))
(declare-fun insert-p-in-p->*->*->1->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (insert-p-in-p->*->*->1->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun insert-p-out-p->*->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (insert-p-out-p->*->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun insert-p-out-p->*->*->1->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (insert-p-out-p->*->*->1->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun insert-ret-RET (Int Int Int Bool) Bool)
(declare-fun insert-x-in-x (Int Int Bool) Bool)
(declare-fun insert-x-out-x (Int Int Int Bool) Bool)
(declare-fun insert_loop-p-in-p->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (insert_loop-p-in-p->*->0 !g0 !g1 !g2 false)))
(declare-fun insert_loop-p-in-p->*->1->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (insert_loop-p-in-p->*->1->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun insert_loop-p-out-p->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (insert_loop-p-out-p->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun insert_loop-p-out-p->*->1->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (insert_loop-p-out-p->*->1->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun insert_loop-ret-RET (Int Int Int Bool) Bool)
(declare-fun insert_loop-x-in-x (Int Int Bool) Bool)
(declare-fun insert_loop-x-out-x (Int Int Int Bool) Bool)
(declare-fun join-12-p!old->*->*->0 (Int Int Bool) Bool)
(declare-fun join-12-p->*->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (join-12-p->*->*->0 !g0 !g1 !g2 false)))
(declare-fun join-12-p->*->*->1->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (join-12-p->*->*->1->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun join-18-p!old->*->0 (Int Int Int Int Bool) Bool)
(declare-fun join-18-p->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (join-18-p->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun join-18-p->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (join-18-p->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun join-18-x (Int Int Int Int Bool) Bool)
(declare-fun join-18-x!old (Int Int Int Int Bool) Bool)
(declare-fun join-20-p!old->*->0 (Int Int Int Int Bool) Bool)
(declare-fun join-20-p->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (join-20-p->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun join-20-p->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (join-20-p->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun join-20-x (Int Int Int Int Bool) Bool)
(declare-fun join-20-x!old (Int Int Int Int Bool) Bool)
(declare-fun join-26-p!old->*->*->0 (Int Int Int Int Bool) Bool)
(declare-fun join-26-p->*->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (join-26-p->*->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun join-26-p->*->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (join-26-p->*->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun join-26-x (Int Int Int Int Bool) Bool)
(declare-fun join-26-x!old (Int Int Int Int Bool) Bool)
(declare-fun join-5-nxt->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (join-5-nxt->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun join-5-nxt->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (join-5-nxt->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun join-5-p!old->*->0 (Int Int Int Bool) Bool)
(declare-fun join-5-p->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (join-5-p->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun join-5-p->*->1->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (join-5-p->*->1->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun join-5-v (Int Int Int Bool) Bool)
(declare-fun scope-16-x (Int Int Int Int Int Int Bool) Bool)
(declare-fun scope-24-x (Int Int Int Int Bool) Bool)
(declare-fun scope-3-nxt->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (scope-3-nxt->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun scope-3-nxt->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (scope-3-nxt->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun scope-3-v (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int)) (scope-3-v !g0 !g1 !g2 false)))
(declare-fun scope-31-l->*->*->0 (Int Int Bool) Bool)
(assert (forall ((!g0 Int) (!g1 Int)) (scope-31-l->*->*->0 !g0 !g1 false)))
(declare-fun scope-31-l->*->*->1->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (scope-31-l->*->*->1->*->0 !g0 !g1 !g2 false)))
(declare-fun scope-33-l->*->*->0 (Int Int Bool) Bool)
(assert (forall ((!g0 Int) (!g1 Int)) (scope-33-l->*->*->0 !g0 !g1 false)))
(declare-fun scope-33-l->*->*->1->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (scope-33-l->*->*->1->*->0 !g0 !g1 !g2 false)))
(declare-fun scope-35-l->*->*->0 (Int Int Bool) Bool)
(assert (forall ((!g0 Int) (!g1 Int)) (scope-35-l->*->*->0 !g0 !g1 false)))
(declare-fun scope-35-l->*->*->1->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (scope-35-l->*->*->1->*->0 !g0 !g1 !g2 false)))
(declare-fun scope-39-p!old->*->0 (Int Int Bool) Bool)
(declare-fun scope-39-p->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (scope-39-p->*->0 !g0 !g1 !g2 false)))
(declare-fun scope-39-p->*->1->*->0 (Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int))
  (scope-39-p->*->1->*->0 !g0 !g1 !g2 !g3 false)))
(declare-fun scope-44-p!old->*->*->0 (Int Int Bool) Bool)
(declare-fun scope-50-p!old->*->0 (Int Int Int Int Bool) Bool)
(declare-fun scope-50-p->*->0 (Int Int Int Int Int Bool) Bool)
(declare-fun scope-50-p->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (scope-50-p->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun scope-50-x (Int Int Int Int Bool) Bool)
(declare-fun scope-50-x!old (Int Int Int Int Bool) Bool)
(declare-fun scope-55-p!old->*->0 (Int Int Int Int Bool) Bool)
(declare-fun scope-55-p->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (scope-55-p->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun scope-55-p->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (scope-55-p->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun scope-55-x (Int Int Int Int Bool) Bool)
(declare-fun scope-55-x!old (Int Int Int Int Bool) Bool)
(declare-fun scope-59-p!old->*->0 (Int Int Int Int Bool) Bool)
(declare-fun scope-59-p->*->0 (Int Int Int Int Int Bool) Bool)
(declare-fun scope-59-p->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (scope-59-p->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun scope-59-x (Int Int Int Int Bool) Bool)
(declare-fun scope-59-x!old (Int Int Int Int Bool) Bool)
(declare-fun scope-70-p!old->*->*->0 (Int Int Int Int Bool) Bool)
(declare-fun scope-70-p->*->*->0 (Int Int Int Int Int Bool) Bool)
(declare-fun scope-70-x (Int Int Int Int Bool) Bool)
(declare-fun scope-70-x!old (Int Int Int Int Bool) Bool)
(declare-fun scope-8-p!old->*->*->0 (Int Int Bool) Bool)
(declare-fun shuf-17-nxt->*->0 (Int Int Int Int Int Int Int Int Bool) Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int)
   (!g7 Int))
  (shuf-17-nxt->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 !g7 false)))
(declare-fun shuf-17-nxt->*->1->*->0
 (Int Int Int Int Int Int Int Int Int Bool) Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int)
   (!g7 Int) (!g8 Int))
  (shuf-17-nxt->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 !g7 !g8 false)))
(declare-fun shuf-17-p->*->1->*->0 (Int Int Int Int Int Int Int Int Bool)
 Bool)
(assert
 (forall
  ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int) (!g6 Int)
   (!g7 Int))
  (shuf-17-p->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 !g6 !g7 false)))
(declare-fun shuf-6-nxt->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (shuf-6-nxt->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun shuf-6-nxt->*->1->*->0 (Int Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int) (!g5 Int))
  (shuf-6-nxt->*->1->*->0 !g0 !g1 !g2 !g3 !g4 !g5 false)))
(declare-fun shuf-6-p->*->1->*->0 (Int Int Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int) (!g3 Int) (!g4 Int))
  (shuf-6-p->*->1->*->0 !g0 !g1 !g2 !g3 !g4 false)))
(declare-fun test_sorted-p-in-p->*->*->0 (Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int)) (test_sorted-p-in-p->*->*->0 !g0 !g1 false)))
(declare-fun test_sorted-p-in-p->*->*->1->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (test_sorted-p-in-p->*->*->1->*->0 !g0 !g1 !g2 false)))
(declare-fun test_sorted-p-out-p->*->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (test_sorted-p-out-p->*->*->0 !g0 !g1 !g2 false)))
(declare-fun test_sorted-p-out-p->*->*->1->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (test_sorted-p-out-p->*->*->1->*->0 !g0 !g1 !g2 false)))
(declare-fun test_sorted-ret-RET (Int Int Bool) Bool)
(declare-fun test_sorted_loop-p-in-p->*->0 (Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int)) (test_sorted_loop-p-in-p->*->0 !g0 !g1 false)))
(declare-fun test_sorted_loop-p-in-p->*->1->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (test_sorted_loop-p-in-p->*->1->*->0 !g0 !g1 !g2 false)))
(declare-fun test_sorted_loop-p-out-p->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (test_sorted_loop-p-out-p->*->0 !g0 !g1 !g2 false)))
(declare-fun test_sorted_loop-p-out-p->*->1->*->0 (Int Int Int Bool) Bool)
(assert
 (forall ((!g0 Int) (!g1 Int) (!g2 Int))
  (test_sorted_loop-p-out-p->*->1->*->0 !g0 !g1 !g2 false)))
(declare-fun test_sorted_loop-ret-RET (Int Int Bool) Bool)
(define-const ovar-299 Real 0.02)
(define-const ovar-298 Real 0.02)
(define-const ovar-297 Real 0.02)
(define-const ovar-292 Real 0.02)
(define-const ovar-291 Real 0.02)
(define-const ovar-290 Real 0.02)
(define-const ovar-285 Real 0.02)
(define-const ovar-284 Real 0.02)
(define-const ovar-283 Real 0.02)
(define-const ovar-278 Real 0.02)
(define-const ovar-277 Real 0.02)
(define-const ovar-276 Real 0.02)
(define-const ovar-273 Real 0.02)
(define-const ovar-272 Real 0.02)
(define-const ovar-271 Real 0.02)
(define-const ovar-270 Real 0.02)
(define-const ovar-269 Real 0.02)
(define-const ovar-268 Real 0.98)
(define-const ovar-267 Real 0.04)
(define-const ovar-266 Real 0.02)
(define-const ovar-265 Real 0.04)
(define-const ovar-264 Real 0.02)
(define-const ovar-262 Real 0.06)
(define-const ovar-260 Real 0.06)
(define-const ovar-256 Real 1.)
(define-const ovar-255 Real 1.)
(define-const ovar-254 Real 1.)
(define-const ovar-251 Real 0.02)
(define-const ovar-250 Real 0.02)
(define-const ovar-247 Real 0.02)
(define-const ovar-246 Real 0.02)
(define-const ovar-242 Real 0.02)
(define-const ovar-241 Real 0.02)
(define-const ovar-234 Real 0.02)
(define-const ovar-233 Real 0.02)
(define-const ovar-232 Real 0.02)
(define-const ovar-231 Real 0.98)
(define-const ovar-230 Real 0.04)
(define-const ovar-229 Real 0.02)
(define-const ovar-228 Real 0.04)
(define-const ovar-227 Real 0.02)
(define-const ovar-225 Real 0.04)
(define-const ovar-223 Real 1.)
(define-const ovar-222 Real 0.02)
(define-const ovar-221 Real 0.06)
(define-const ovar-220 Real 0.02)
(define-const ovar-219 Real 0.06)
(define-const ovar-217 Real 0.08)
(define-const ovar-215 Real 0.08)
(define-const ovar-214 Real 0.02)
(define-const ovar-213 Real 0.02)
(define-const ovar-210 Real 0.02)
(define-const ovar-209 Real 0.02)
(define-const ovar-208 Real 0.02)
(define-const ovar-207 Real 0.02)
(define-const ovar-203 Real 1.)
(define-const ovar-202 Real 1.)
(define-const ovar-194 Real 0.02)
(define-const ovar-191 Real 0.02)
(define-const ovar-190 Real 0.02)
(define-const ovar-189 Real 0.02)
(define-const ovar-188 Real 0.02)
(define-const ovar-187 Real 0.02)
(define-const ovar-186 Real 0.04)
(define-const ovar-185 Real 0.96)
(define-const ovar-184 Real 0.04)
(define-const ovar-183 Real 0.06)
(define-const ovar-182 Real 0.02)
(define-const ovar-181 Real 0.06)
(define-const ovar-180 Real 0.02)
(define-const ovar-178 Real 0.06)
(define-const ovar-176 Real 1.)
(define-const ovar-175 Real 0.92)
(define-const ovar-174 Real 0.08)
(define-const ovar-173 Real 0.92)
(define-const ovar-172 Real 0.08)
(define-const ovar-168 Real 1.)
(define-const ovar-167 Real 1.)
(define-const ovar-159 Real 0.02)
(define-const ovar-158 Real 0.02)
(define-const ovar-155 Real 0.02)
(define-const ovar-152 Real 0.02)
(define-const ovar-151 Real 0.02)
(define-const ovar-143 Real 0.02)
(define-const ovar-140 Real 0.02)
(define-const ovar-139 Real 0.02)
(define-const ovar-138 Real 0.02)
(define-const ovar-137 Real 0.02)
(define-const ovar-136 Real 0.02)
(define-const ovar-135 Real 0.04)
(define-const ovar-134 Real 0.96)
(define-const ovar-133 Real 0.04)
(define-const ovar-132 Real 0.06)
(define-const ovar-131 Real 0.02)
(define-const ovar-130 Real 0.06)
(define-const ovar-129 Real 0.02)
(define-const ovar-127 Real 0.06)
(define-const ovar-125 Real 1.)
(define-const ovar-124 Real 0.02)
(define-const ovar-123 Real 0.08)
(define-const ovar-122 Real 0.02)
(define-const ovar-121 Real 0.08)
(define-const ovar-119 Real 0.1)
(define-const ovar-117 Real 0.1)
(define-const ovar-116 Real 0.02)
(define-const ovar-115 Real 0.02)
(define-const ovar-112 Real 0.02)
(define-const ovar-111 Real 0.02)
(define-const ovar-109 Real 0.02)
(define-const ovar-108 Real 0.02)
(define-const ovar-107 Real 0.02)
(define-const ovar-103 Real 0.02)
(define-const ovar-102 Real 0.02)
(define-const ovar-99 Real 0.02)
(define-const ovar-98 Real 0.02)
(define-const ovar-95 Real 0.02)
(define-const ovar-94 Real 0.02)
(define-const ovar-90 Real 0.02)
(define-const ovar-89 Real 0.02)
(define-const ovar-86 Real 0.02)
(define-const ovar-85 Real 0.02)
(define-const ovar-84 Real 0.02)
(define-const ovar-83 Real 0.02)
(define-const ovar-79 Real 0.02)
(define-const ovar-78 Real 0.02)
(define-const ovar-75 Real 0.02)
(define-const ovar-71 Real 0.02)
(define-const ovar-70 Real 0.)
(define-const ovar-67 Real 0.04)
(define-const ovar-66 Real 0.02)
(define-const ovar-60 Real 0.02)
(define-const ovar-59 Real 0.02)
(define-const ovar-56 Real 0.02)
(define-const ovar-55 Real 0.02)
(define-const ovar-54 Real 0.02)
(define-const ovar-53 Real 0.02)
(define-const ovar-50 Real 0.02)
(define-const ovar-49 Real 0.02)
(define-const ovar-47 Real 0.02)
(define-const ovar-45 Real 0.02)
(define-const ovar-44 Real 0.02)
(define-const ovar-40 Real 1.)
(define-const ovar-38 Real 1.)
(define-const ovar-37 Real 1.)
(define-const ovar-34 Real 0.04)
(define-const ovar-32 Real 0.04)
(define-const ovar-31 Real 0.02)
(define-const ovar-27 Real 1.)
(define-const ovar-25 Real 1.)
(define-const ovar-22 Real 0.04)
(define-const ovar-20 Real 0.02)
(define-const ovar-17 Real 0.02)
(define-const ovar-15 Real 0.02)
(define-const ovar-14 Real 0.02)
(define-const ovar-12 Real 0.04)
(define-const ovar-10 Real 0.04)
(define-const ovar-9 Real 0.02)
(define-const ovar-6 Real 0.02)
(define-const ovar-4 Real 0.02)
(define-const ovar-2 Real 0.04)
(define-const ovar-0 Real 0.02)
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-35-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-35-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (scope-35-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))
   (test_sorted-p-in-p->*->*->1->*->0 36 NU l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-35-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-35-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= NU l->*->*->0) (scope-35-l->*->*->0 CTXT0 NU null?2))
   (test_sorted-p-in-p->*->*->0 36 NU null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-35-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-35-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (> 0.02 0.) (> 0.02 0.) (> 0.02 0.) (> 0.98 0.) (> 0.94 0.) (> 0.92 0.)
    (> 1. 0.) (> 0.96 0.) (> 0.94 0.)
    (test_sorted-p-out-p->*->*->1->*->0 36 NU l->*->*->0 null?2)
    (scope-35-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))
   (call-36-l-out-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-35-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-35-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (> 0.02 0.) (> 0.02 0.) (> 0.02 0.)
    (or (= 0.92 0.) (= 0.94 0.) (= 0.98 0.)) (> 1. 0.) (> 0.96 0.)
    (> 0.94 0.) (test_sorted-p-out-p->*->*->1->*->0 36 NU l->*->*->0 null?2))
   (call-36-l-out-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-35-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-35-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (or (= 0.02 0.) (= 0.02 0.) (= 0.02 0.)) (> 0.98 0.) (> 0.94 0.)
    (> 0.92 0.) (> 1. 0.) (> 0.96 0.) (> 0.94 0.)
    (scope-35-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))
   (call-36-l-out-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-35-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-35-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (or (= 0.94 0.) (= 0.96 0.) (= 1. 0.)))
   (call-36-l-out-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-35-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-35-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (scope-35-l->*->*->0 CTXT0 !pre null?2) (> 0.02 0.) (> 0.02 0.)
    (> 0.98 0.) (> 0.94 0.) (> 1. 0.) (> 0.96 0.)
    (test_sorted-p-out-p->*->*->0 36 NU !pre null?3)
    (scope-35-l->*->*->0 CTXT0 NU null?3))
   (call-36-l-out-l->*->*->0 CTXT0 NU null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-35-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-35-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (scope-35-l->*->*->0 CTXT0 !pre null?2) (> 0.02 0.) (> 0.02 0.)
    (or (= 0.94 0.) (= 0.98 0.)) (> 1. 0.) (> 0.96 0.)
    (test_sorted-p-out-p->*->*->0 36 NU !pre null?3))
   (call-36-l-out-l->*->*->0 CTXT0 NU null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-35-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-35-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (scope-35-l->*->*->0 CTXT0 !pre null?2) (or (= 0.02 0.) (= 0.02 0.))
    (> 0.98 0.) (> 0.94 0.) (> 1. 0.) (> 0.96 0.)
    (scope-35-l->*->*->0 CTXT0 NU null?3))
   (call-36-l-out-l->*->*->0 CTXT0 NU null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-35-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-35-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (scope-35-l->*->*->0 CTXT0 !pre null?2) (or (= 0.96 0.) (= 1. 0.)))
   (call-36-l-out-l->*->*->0 CTXT0 NU null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t1 Int)
   (__t0 Int) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (insert-ret-RET 34 __t1 __t0 true)
    (call-34-l-out-l->*->*->0 CTXT0 l->*->*->0 __t0 null?0)
    (call-34-l-out-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 __t0 l->*->*->0
     null?1)
    (= NU l->*->*->1->*->0)
    (call-34-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))
   (scope-35-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t1 Int)
   (__t0 Int) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (insert-ret-RET 34 __t1 __t0 true)
    (call-34-l-out-l->*->*->0 CTXT0 l->*->*->0 __t0 null?0)
    (call-34-l-out-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 __t0 l->*->*->0
     null?1)
    (= NU l->*->*->0) (call-34-l-out-l->*->*->0 CTXT0 NU __t0 null?2))
   (scope-35-l->*->*->0 CTXT0 NU null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-33-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-33-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (scope-33-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))
   (insert-p-in-p->*->*->1->*->0 34 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-33-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-33-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= NU l->*->*->0) (scope-33-l->*->*->0 CTXT0 NU null?2))
   (insert-p-in-p->*->*->0 34 NU __t0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-33-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-33-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (> 1. 0.) (> 1. 0.) (> 1. 0.) (> 0. 0.) (> 0. 0.) (> 0. 0.) (> 1. 0.)
    (> 1. 0.) (> 1. 0.)
    (insert-p-out-p->*->*->1->*->0 34 NU __t0 l->*->*->0 null?2)
    (scope-33-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))
   (call-34-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-33-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-33-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (> 1. 0.) (> 1. 0.) (> 1. 0.) (or (= 0. 0.) (= 0. 0.) (= 0. 0.))
    (> 1. 0.) (> 1. 0.) (> 1. 0.)
    (insert-p-out-p->*->*->1->*->0 34 NU __t0 l->*->*->0 null?2))
   (call-34-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-33-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-33-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (or (= 1. 0.) (= 1. 0.) (= 1. 0.)) (> 0. 0.) (> 0. 0.) (> 0. 0.)
    (> 1. 0.) (> 1. 0.) (> 1. 0.)
    (scope-33-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))
   (call-34-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-33-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-33-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (or (= 1. 0.) (= 1. 0.) (= 1. 0.)))
   (call-34-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-33-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-33-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (scope-33-l->*->*->0 CTXT0 !pre null?2) (> 1. 0.) (> 1. 0.) (> 0. 0.)
    (> 0. 0.) (> 1. 0.) (> 1. 0.)
    (insert-p-out-p->*->*->0 34 NU !pre __t0 null?3)
    (scope-33-l->*->*->0 CTXT0 NU null?3))
   (call-34-l-out-l->*->*->0 CTXT0 NU __t0 null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-33-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-33-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (scope-33-l->*->*->0 CTXT0 !pre null?2) (> 1. 0.) (> 1. 0.)
    (or (= 0. 0.) (= 0. 0.)) (> 1. 0.) (> 1. 0.)
    (insert-p-out-p->*->*->0 34 NU !pre __t0 null?3))
   (call-34-l-out-l->*->*->0 CTXT0 NU __t0 null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-33-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-33-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (scope-33-l->*->*->0 CTXT0 !pre null?2) (or (= 1. 0.) (= 1. 0.))
    (> 0. 0.) (> 0. 0.) (> 1. 0.) (> 1. 0.)
    (scope-33-l->*->*->0 CTXT0 NU null?3))
   (call-34-l-out-l->*->*->0 CTXT0 NU __t0 null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-33-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-33-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (scope-33-l->*->*->0 CTXT0 !pre null?2) (or (= 1. 0.) (= 1. 0.)))
   (call-34-l-out-l->*->*->0 CTXT0 NU __t0 null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-33-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-33-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= NU __t0))
   (insert-x-in-x 34 NU true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t1 Int)
   (__t0 Int) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (insert-ret-RET 32 __t1 __t0 true)
    (call-32-l-out-l->*->*->0 CTXT0 l->*->*->0 __t0 null?0)
    (call-32-l-out-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 __t0 l->*->*->0
     null?1)
    (= NU l->*->*->1->*->0)
    (call-32-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))
   (scope-33-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t1 Int)
   (__t0 Int) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (insert-ret-RET 32 __t1 __t0 true)
    (call-32-l-out-l->*->*->0 CTXT0 l->*->*->0 __t0 null?0)
    (call-32-l-out-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 __t0 l->*->*->0
     null?1)
    (= NU l->*->*->0) (call-32-l-out-l->*->*->0 CTXT0 NU __t0 null?2))
   (scope-33-l->*->*->0 CTXT0 NU null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-31-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-31-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (scope-31-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))
   (insert-p-in-p->*->*->1->*->0 32 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-31-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-31-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= NU l->*->*->0) (scope-31-l->*->*->0 CTXT0 NU null?2))
   (insert-p-in-p->*->*->0 32 NU __t0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-31-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-31-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (> 1. 0.) (> 1. 0.) (> 1. 0.) (> 0. 0.) (> 0. 0.) (> 0. 0.) (> 1. 0.)
    (> 1. 0.) (> 1. 0.)
    (insert-p-out-p->*->*->1->*->0 32 NU __t0 l->*->*->0 null?2)
    (scope-31-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))
   (call-32-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-31-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-31-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (> 1. 0.) (> 1. 0.) (> 1. 0.) (or (= 0. 0.) (= 0. 0.) (= 0. 0.))
    (> 1. 0.) (> 1. 0.) (> 1. 0.)
    (insert-p-out-p->*->*->1->*->0 32 NU __t0 l->*->*->0 null?2))
   (call-32-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-31-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-31-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (or (= 1. 0.) (= 1. 0.) (= 1. 0.)) (> 0. 0.) (> 0. 0.) (> 0. 0.)
    (> 1. 0.) (> 1. 0.) (> 1. 0.)
    (scope-31-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))
   (call-32-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-31-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-31-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (or (= 1. 0.) (= 1. 0.) (= 1. 0.)))
   (call-32-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-31-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-31-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (scope-31-l->*->*->0 CTXT0 !pre null?2) (> 1. 0.) (> 1. 0.) (> 0. 0.)
    (> 0. 0.) (> 1. 0.) (> 1. 0.)
    (insert-p-out-p->*->*->0 32 NU !pre __t0 null?3)
    (scope-31-l->*->*->0 CTXT0 NU null?3))
   (call-32-l-out-l->*->*->0 CTXT0 NU __t0 null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-31-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-31-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (scope-31-l->*->*->0 CTXT0 !pre null?2) (> 1. 0.) (> 1. 0.)
    (or (= 0. 0.) (= 0. 0.)) (> 1. 0.) (> 1. 0.)
    (insert-p-out-p->*->*->0 32 NU !pre __t0 null?3))
   (call-32-l-out-l->*->*->0 CTXT0 NU __t0 null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-31-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-31-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (scope-31-l->*->*->0 CTXT0 !pre null?2) (or (= 1. 0.) (= 1. 0.))
    (> 0. 0.) (> 0. 0.) (> 1. 0.) (> 1. 0.)
    (scope-31-l->*->*->0 CTXT0 NU null?3))
   (call-32-l-out-l->*->*->0 CTXT0 NU __t0 null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-31-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-31-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (scope-31-l->*->*->0 CTXT0 !pre null?2) (or (= 1. 0.) (= 1. 0.)))
   (call-32-l-out-l->*->*->0 CTXT0 NU __t0 null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-31-l->*->*->0 CTXT0 l->*->*->0 null?0)
    (scope-31-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 l->*->*->0 null?1)
    (= NU __t0))
   (insert-x-in-x 32 NU true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t1 Int)
   (__t0 Int) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (insert-ret-RET 30 __t1 __t0 true)
    (call-30-l-out-l->*->*->0 CTXT0 l->*->*->0 __t0 null?0)
    (call-30-l-out-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 __t0 l->*->*->0
     null?1)
    (= NU l->*->*->1->*->0)
    (call-30-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))
   (scope-31-l->*->*->1->*->0 CTXT0 NU l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t1 Int)
   (__t0 Int) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (insert-ret-RET 30 __t1 __t0 true)
    (call-30-l-out-l->*->*->0 CTXT0 l->*->*->0 __t0 null?0)
    (call-30-l-out-l->*->*->1->*->0 CTXT0 l->*->*->1->*->0 __t0 l->*->*->0
     null?1)
    (= NU l->*->*->0) (call-30-l-out-l->*->*->0 CTXT0 NU __t0 null?2))
   (scope-31-l->*->*->0 CTXT0 NU null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (fresh_list-ret-RET->*->*->0 29 l->*->*->0 null?0)
    (fresh_list-ret-RET->*->*->1->*->0 29 l->*->*->1->*->0 l->*->*->0 null?1)
    (fresh_list-ret-RET->*->*->1->*->0 29 NU l->*->*->0 null?2))
   (insert-p-in-p->*->*->1->*->0 30 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (fresh_list-ret-RET->*->*->0 29 l->*->*->0 null?0)
    (fresh_list-ret-RET->*->*->1->*->0 29 l->*->*->1->*->0 l->*->*->0 null?1)
    (= NU l->*->*->0) (fresh_list-ret-RET->*->*->0 29 NU null?2))
   (insert-p-in-p->*->*->0 30 NU __t0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (fresh_list-ret-RET->*->*->0 29 l->*->*->0 null?0)
    (fresh_list-ret-RET->*->*->1->*->0 29 l->*->*->1->*->0 l->*->*->0 null?1)
    (> 1. 0.) (> 1. 0.) (> 1. 0.) (> 0. 0.) (> 0. 0.) (> 0. 0.) (> 1. 0.)
    (> 1. 0.) (> 1. 0.)
    (insert-p-out-p->*->*->1->*->0 30 NU __t0 l->*->*->0 null?2)
    (fresh_list-ret-RET->*->*->1->*->0 29 NU l->*->*->0 null?2))
   (call-30-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (fresh_list-ret-RET->*->*->0 29 l->*->*->0 null?0)
    (fresh_list-ret-RET->*->*->1->*->0 29 l->*->*->1->*->0 l->*->*->0 null?1)
    (> 1. 0.) (> 1. 0.) (> 1. 0.) (or (= 0. 0.) (= 0. 0.) (= 0. 0.))
    (> 1. 0.) (> 1. 0.) (> 1. 0.)
    (insert-p-out-p->*->*->1->*->0 30 NU __t0 l->*->*->0 null?2))
   (call-30-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (fresh_list-ret-RET->*->*->0 29 l->*->*->0 null?0)
    (fresh_list-ret-RET->*->*->1->*->0 29 l->*->*->1->*->0 l->*->*->0 null?1)
    (or (= 1. 0.) (= 1. 0.) (= 1. 0.)) (> 0. 0.) (> 0. 0.) (> 0. 0.)
    (> 1. 0.) (> 1. 0.) (> 1. 0.)
    (fresh_list-ret-RET->*->*->1->*->0 29 NU l->*->*->0 null?2))
   (call-30-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (fresh_list-ret-RET->*->*->0 29 l->*->*->0 null?0)
    (fresh_list-ret-RET->*->*->1->*->0 29 l->*->*->1->*->0 l->*->*->0 null?1)
    (or (= 1. 0.) (= 1. 0.) (= 1. 0.)))
   (call-30-l-out-l->*->*->1->*->0 CTXT0 NU __t0 l->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (fresh_list-ret-RET->*->*->0 29 l->*->*->0 null?0)
    (fresh_list-ret-RET->*->*->1->*->0 29 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (fresh_list-ret-RET->*->*->0 29 !pre null?2) (> 1. 0.) (> 1. 0.)
    (> 0. 0.) (> 0. 0.) (> 1. 0.) (> 1. 0.)
    (insert-p-out-p->*->*->0 30 NU !pre __t0 null?3)
    (fresh_list-ret-RET->*->*->0 29 NU null?3))
   (call-30-l-out-l->*->*->0 CTXT0 NU __t0 null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (fresh_list-ret-RET->*->*->0 29 l->*->*->0 null?0)
    (fresh_list-ret-RET->*->*->1->*->0 29 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (fresh_list-ret-RET->*->*->0 29 !pre null?2) (> 1. 0.) (> 1. 0.)
    (or (= 0. 0.) (= 0. 0.)) (> 1. 0.) (> 1. 0.)
    (insert-p-out-p->*->*->0 30 NU !pre __t0 null?3))
   (call-30-l-out-l->*->*->0 CTXT0 NU __t0 null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (fresh_list-ret-RET->*->*->0 29 l->*->*->0 null?0)
    (fresh_list-ret-RET->*->*->1->*->0 29 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (fresh_list-ret-RET->*->*->0 29 !pre null?2) (or (= 1. 0.) (= 1. 0.))
    (> 0. 0.) (> 0. 0.) (> 1. 0.) (> 1. 0.)
    (fresh_list-ret-RET->*->*->0 29 NU null?3))
   (call-30-l-out-l->*->*->0 CTXT0 NU __t0 null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (fresh_list-ret-RET->*->*->0 29 l->*->*->0 null?0)
    (fresh_list-ret-RET->*->*->1->*->0 29 l->*->*->1->*->0 l->*->*->0 null?1)
    (= !pre l->*->*->0) (= !pre l->*->*->0)
    (fresh_list-ret-RET->*->*->0 29 !pre null?2) (or (= 1. 0.) (= 1. 0.)))
   (call-30-l-out-l->*->*->0 CTXT0 NU __t0 null?3))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (l->*->*->1->*->0 Int) (l->*->*->0 Int) (__t0 Int)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (fresh_list-ret-RET->*->*->0 29 l->*->*->0 null?0)
    (fresh_list-ret-RET->*->*->1->*->0 29 l->*->*->1->*->0 l->*->*->0 null?1)
    (= NU __t0))
   (insert-x-in-x 30 NU true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (<ret>->*->*->1->*->0 Int) (<ret>->*->*->0 Int)
   (__t1->*->*->1->*->0 Int) (__t1->*->*->0 Int) (__t0->*->1->*->0 Int)
   (__t0->*->0 Int) (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-76-__t0->*->0 CTXT0 __t0->*->0 null?0)
    (ifnull-76-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 __t0->*->0 null?1)
    (ifnull-76-__t0->*->0 CTXT0 __t1->*->*->0 null?2)
    (ifnull-76-__t0->*->1->*->0 CTXT0 __t1->*->*->1->*->0 __t1->*->*->0
     null?3)
    (ifnull-76-__t0->*->0 CTXT0 <ret>->*->*->0 null?4)
    (ifnull-76-__t0->*->1->*->0 CTXT0 <ret>->*->*->1->*->0 <ret>->*->*->0
     null?5)
    (ifnull-76-__t0->*->1->*->0 CTXT0 NU <ret>->*->*->0 null?6))
   (fresh_list-ret-RET->*->*->1->*->0 CTXT0 NU <ret>->*->*->0 null?6))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (<ret>->*->*->1->*->0 Int) (<ret>->*->*->0 Int)
   (__t1->*->*->1->*->0 Int) (__t1->*->*->0 Int) (__t0->*->1->*->0 Int)
   (__t0->*->0 Int) (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-76-__t0->*->0 CTXT0 __t0->*->0 null?0)
    (ifnull-76-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 __t0->*->0 null?1)
    (ifnull-76-__t0->*->0 CTXT0 __t1->*->*->0 null?2)
    (ifnull-76-__t0->*->1->*->0 CTXT0 __t1->*->*->1->*->0 __t1->*->*->0
     null?3)
    (ifnull-76-__t0->*->0 CTXT0 <ret>->*->*->0 null?4)
    (ifnull-76-__t0->*->1->*->0 CTXT0 <ret>->*->*->1->*->0 <ret>->*->*->0
     null?5)
    (ifnull-76-__t0->*->0 CTXT0 NU null?6))
   (fresh_list-ret-RET->*->*->0 CTXT0 NU null?6))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and
    (call-23-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?0)
    (call-23-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x
     x!old p->*->*->0 null?1)
    (scope-24-x CTXT0 x p!old->*->*->0 x!old true) (= NU x!old))
   (join-26-x!old CTXT0 NU p!old->*->*->0 x true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-70-p->*->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?0)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?1)
    (scope-70-p!old->*->*->0 CTXT0 p!old->*->*->0 x x!old true)
    (scope-70-x CTXT0 x p!old->*->*->0 x!old true)
    (scope-70-x!old CTXT0 x!old p!old->*->*->0 x true) (= NU x!old)
    (scope-70-x!old CTXT0 NU p!old->*->*->0 x true))
   (join-26-x!old CTXT0 NU p!old->*->*->0 x true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and
    (call-23-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?0)
    (call-23-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x
     x!old p->*->*->0 null?1)
    (scope-24-x CTXT0 x p!old->*->*->0 x!old true) (= NU x)
    (scope-24-x CTXT0 NU p!old->*->*->0 x!old true))
   (join-26-x CTXT0 NU p!old->*->*->0 x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-70-p->*->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?0)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?1)
    (scope-70-p!old->*->*->0 CTXT0 p!old->*->*->0 x x!old true)
    (scope-70-x CTXT0 x p!old->*->*->0 x!old true)
    (scope-70-x!old CTXT0 x!old p!old->*->*->0 x true) (= NU x)
    (scope-70-x CTXT0 NU p!old->*->*->0 x!old true))
   (join-26-x CTXT0 NU p!old->*->*->0 x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and
    (call-23-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?0)
    (call-23-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x
     x!old p->*->*->0 null?1)
    (scope-24-x CTXT0 x p!old->*->*->0 x!old true) (= NU p!old->*->*->0))
   (join-26-p!old->*->*->0 CTXT0 NU x x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-70-p->*->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?0)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?1)
    (scope-70-p!old->*->*->0 CTXT0 p!old->*->*->0 x x!old true)
    (scope-70-x CTXT0 x p!old->*->*->0 x!old true)
    (scope-70-x!old CTXT0 x!old p!old->*->*->0 x true) (= NU p!old->*->*->0)
    (scope-70-p!old->*->*->0 CTXT0 NU x x!old true))
   (join-26-p!old->*->*->0 CTXT0 NU x x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and
    (call-23-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?0)
    (call-23-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x
     x!old p->*->*->0 null?1)
    (scope-24-x CTXT0 x p!old->*->*->0 x!old true)
    (call-23-hd-out-hd->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old p->*->*->0
     null?2))
   (join-26-p->*->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old p->*->*->0
    null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and
    (call-23-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?0)
    (call-23-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x
     x!old p->*->*->0 null?1)
    (scope-24-x CTXT0 x p!old->*->*->0 x!old true) (= NU p->*->*->0)
    (call-23-hd-out-hd->*->0 CTXT0 NU p!old->*->*->0 x x!old null?2))
   (join-26-p->*->*->0 CTXT0 NU p!old->*->*->0 x x!old null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (scope-70-p->*->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?0)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?1)
    (scope-70-p!old->*->*->0 CTXT0 p!old->*->*->0 x x!old true)
    (scope-70-x CTXT0 x p!old->*->*->0 x!old true)
    (scope-70-x!old CTXT0 x!old p!old->*->*->0 x true)
    (fold-72-__t2->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old p->*->*->0
     null?2))
   (join-26-p->*->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old p->*->*->0
    null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (scope-70-p->*->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?0)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?1)
    (scope-70-p!old->*->*->0 CTXT0 p!old->*->*->0 x x!old true)
    (scope-70-x CTXT0 x p!old->*->*->0 x!old true)
    (scope-70-x!old CTXT0 x!old p!old->*->*->0 x true) (= NU p->*->*->0)
    (scope-70-p->*->*->0 CTXT0 NU p!old->*->*->0 x x!old null?2))
   (join-26-p->*->*->0 CTXT0 NU p!old->*->*->0 x x!old null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0)
    (call-23-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?2)
    (call-23-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x
     x!old p->*->*->0 null?3)
    (scope-24-x CTXT0 x p!old->*->*->0 x!old true)
    (call-23-hd-out-hd->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old p->*->*->0
     null?4))
   (insert-p-out-p->*->*->1->*->0 CTXT0 NU x p->*->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0)
    (call-23-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?2)
    (call-23-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x
     x!old p->*->*->0 null?3)
    (scope-24-x CTXT0 x p!old->*->*->0 x!old true) (= NU p->*->*->0)
    (call-23-hd-out-hd->*->0 CTXT0 NU p!old->*->*->0 x x!old null?4))
   (insert-p-out-p->*->*->0 CTXT0 NU p!old->*->*->0 x null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0)
    (call-23-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?2)
    (call-23-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x
     x!old p->*->*->0 null?3)
    (scope-24-x CTXT0 x p!old->*->*->0 x!old true) (= NU x)
    (scope-24-x CTXT0 NU p!old->*->*->0 x!old true))
   (insert-x-out-x CTXT0 NU x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (<ret> Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0)
    (call-23-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?2)
    (call-23-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x
     x!old p->*->*->0 null?3)
    (scope-24-x CTXT0 x p!old->*->*->0 x!old true) (= <ret> 0) (= NU 0))
   (insert-ret-RET CTXT0 NU x true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (insert_loop-ret-RET 23 __t0 x true)
    (call-23-hd-out-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 x x!old null?0)
    (call-23-hd-out-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 x
     x!old hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?2)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?3)
    (= x x!old) (insert-x-in-x CTXT0 x true) (= NU x) (= NU x!old)
    (insert-x-in-x CTXT0 NU null?4))
   (scope-24-x CTXT0 NU p!old->*->*->0 x!old null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 hd->*->0 x null?0)
    (insert-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 x hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?2)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?3)
    (= x x!old) (insert-x-in-x CTXT0 x true)
    (insert-p-in-p->*->*->1->*->0 CTXT0 NU x hd->*->0 null?4))
   (insert_loop-p-in-p->*->1->*->0 23 NU x hd->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 hd->*->0 x null?0)
    (insert-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 x hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?2)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?3)
    (= x x!old) (insert-x-in-x CTXT0 x true) (= NU hd->*->0)
    (= NU p!old->*->*->0) (insert-p-in-p->*->*->0 CTXT0 NU x null?4))
   (insert_loop-p-in-p->*->0 23 NU x null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 hd->*->0 x null?0)
    (insert-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 x hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?2)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?3)
    (= x x!old) (insert-x-in-x CTXT0 x true) (> 1. 0.) (> 1. 0.) (> 0. 0.)
    (> 0. 0.) (> 1. 0.) (> 1. 0.)
    (insert_loop-p-out-p->*->1->*->0 23 NU x hd->*->0 null?4)
    (insert-p-in-p->*->*->1->*->0 CTXT0 NU x hd->*->0 null?4))
   (call-23-hd-out-hd->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old hd->*->0
    null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 hd->*->0 x null?0)
    (insert-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 x hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?2)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?3)
    (= x x!old) (insert-x-in-x CTXT0 x true) (> 1. 0.) (> 1. 0.)
    (or (= 0. 0.) (= 0. 0.)) (> 1. 0.) (> 1. 0.)
    (insert_loop-p-out-p->*->1->*->0 23 NU x hd->*->0 null?4))
   (call-23-hd-out-hd->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old hd->*->0
    null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 hd->*->0 x null?0)
    (insert-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 x hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?2)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?3)
    (= x x!old) (insert-x-in-x CTXT0 x true) (or (= 1. 0.) (= 1. 0.))
    (> 0. 0.) (> 0. 0.) (> 1. 0.) (> 1. 0.)
    (insert-p-in-p->*->*->1->*->0 CTXT0 NU x hd->*->0 null?4))
   (call-23-hd-out-hd->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old hd->*->0
    null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 hd->*->0 x null?0)
    (insert-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 x hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?2)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?3)
    (= x x!old) (insert-x-in-x CTXT0 x true) (or (= 1. 0.) (= 1. 0.)))
   (call-23-hd-out-hd->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old hd->*->0
    null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 hd->*->0 x null?0)
    (insert-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 x hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?2)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?3)
    (= x x!old) (insert-x-in-x CTXT0 x true) (= !pre hd->*->0)
    (= !pre hd->*->0) (= !pre p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 !pre x null?4) (> 1. 0.) (> 0. 0.)
    (> 1. 0.) (insert_loop-p-out-p->*->0 23 NU !pre x null?5)
    (= NU p!old->*->*->0) (insert-p-in-p->*->*->0 CTXT0 NU x null?5))
   (call-23-hd-out-hd->*->0 CTXT0 NU p!old->*->*->0 x x!old null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 hd->*->0 x null?0)
    (insert-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 x hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?2)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?3)
    (= x x!old) (insert-x-in-x CTXT0 x true) (= !pre hd->*->0)
    (= !pre hd->*->0) (= !pre p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 !pre x null?4) (> 1. 0.) (or (= 0. 0.))
    (> 1. 0.) (insert_loop-p-out-p->*->0 23 NU !pre x null?5))
   (call-23-hd-out-hd->*->0 CTXT0 NU p!old->*->*->0 x x!old null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 hd->*->0 x null?0)
    (insert-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 x hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?2)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?3)
    (= x x!old) (insert-x-in-x CTXT0 x true) (= !pre hd->*->0)
    (= !pre hd->*->0) (= !pre p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 !pre x null?4) (or (= 1. 0.)) (> 0. 0.)
    (> 1. 0.) (= NU p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 NU x null?5))
   (call-23-hd-out-hd->*->0 CTXT0 NU p!old->*->*->0 x x!old null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 hd->*->0 x null?0)
    (insert-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 x hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?2)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?3)
    (= x x!old) (insert-x-in-x CTXT0 x true) (= !pre hd->*->0)
    (= !pre hd->*->0) (= !pre p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 !pre x null?4) (or (= 1. 0.)))
   (call-23-hd-out-hd->*->0 CTXT0 NU p!old->*->*->0 x x!old null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 hd->*->0 x null?0)
    (insert-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 x hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?2)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?3)
    (= x x!old) (insert-x-in-x CTXT0 x true) (= NU x) (= NU x!old)
    (insert-x-in-x CTXT0 NU true))
   (insert_loop-x-in-x 23 NU true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t3 Int) (__t2->*->1->*->0 Int) (__t2->*->0 Int)
   (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int)
   (__t0->*->1->*->0 Int) (__t0->*->0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-74-__t0->*->0 CTXT0 __t0->*->0 p!old->*->*->0 x x!old null?0)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 p!old->*->*->0 x x!old
     __t0->*->0 null?1)
    (= __t1->0 x) (= __t1->0 x!old) (insert-x-in-x CTXT0 __t1->0 true)
    (ifnull-74-__t0->*->0 CTXT0 __t1->1->*->0 p!old->*->*->0 x x!old null?2)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t1->1->*->1->*->0 p!old->*->*->0 x
     x!old __t1->1->*->0 null?3)
    (= __t2->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 __t2->*->0 p!old->*->*->0 x x!old null?4)
    (fold-72-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 p!old->*->*->0 x x!old
     __t2->*->0 null?5)
    (= __t3 0)
    (ifnull-26-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 x x!old null?6)
    (ifnull-26-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 x x!old
     hd->*->0 null?7)
    (= p->*->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?8)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?9)
    (= x __t1->0) (= x x!old) (insert-x-in-x CTXT0 x true) (= NU x!old))
   (scope-70-x!old CTXT0 NU p!old->*->*->0 x null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t3 Int) (__t2->*->1->*->0 Int) (__t2->*->0 Int)
   (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int)
   (__t0->*->1->*->0 Int) (__t0->*->0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-74-__t0->*->0 CTXT0 __t0->*->0 p!old->*->*->0 x x!old null?0)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 p!old->*->*->0 x x!old
     __t0->*->0 null?1)
    (= __t1->0 x) (= __t1->0 x!old) (insert-x-in-x CTXT0 __t1->0 true)
    (ifnull-74-__t0->*->0 CTXT0 __t1->1->*->0 p!old->*->*->0 x x!old null?2)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t1->1->*->1->*->0 p!old->*->*->0 x
     x!old __t1->1->*->0 null?3)
    (= __t2->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 __t2->*->0 p!old->*->*->0 x x!old null?4)
    (fold-72-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 p!old->*->*->0 x x!old
     __t2->*->0 null?5)
    (= __t3 0)
    (ifnull-26-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 x x!old null?6)
    (ifnull-26-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 x x!old
     hd->*->0 null?7)
    (= p->*->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?8)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?9)
    (= x __t1->0) (= x x!old) (insert-x-in-x CTXT0 x true) (= NU x)
    (= NU __t1->0) (= NU x!old) (insert-x-in-x CTXT0 NU null?10))
   (scope-70-x CTXT0 NU p!old->*->*->0 x!old null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t3 Int) (__t2->*->1->*->0 Int) (__t2->*->0 Int)
   (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int)
   (__t0->*->1->*->0 Int) (__t0->*->0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-74-__t0->*->0 CTXT0 __t0->*->0 p!old->*->*->0 x x!old null?0)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 p!old->*->*->0 x x!old
     __t0->*->0 null?1)
    (= __t1->0 x) (= __t1->0 x!old) (insert-x-in-x CTXT0 __t1->0 true)
    (ifnull-74-__t0->*->0 CTXT0 __t1->1->*->0 p!old->*->*->0 x x!old null?2)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t1->1->*->1->*->0 p!old->*->*->0 x
     x!old __t1->1->*->0 null?3)
    (= __t2->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 __t2->*->0 p!old->*->*->0 x x!old null?4)
    (fold-72-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 p!old->*->*->0 x x!old
     __t2->*->0 null?5)
    (= __t3 0)
    (ifnull-26-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 x x!old null?6)
    (ifnull-26-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 x x!old
     hd->*->0 null?7)
    (= p->*->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?8)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?9)
    (= x __t1->0) (= x x!old) (insert-x-in-x CTXT0 x true)
    (= NU p!old->*->*->0))
   (scope-70-p!old->*->*->0 CTXT0 NU x x!old null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t3 Int) (__t2->*->1->*->0 Int) (__t2->*->0 Int)
   (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int)
   (__t0->*->1->*->0 Int) (__t0->*->0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-74-__t0->*->0 CTXT0 __t0->*->0 p!old->*->*->0 x x!old null?0)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 p!old->*->*->0 x x!old
     __t0->*->0 null?1)
    (= __t1->0 x) (= __t1->0 x!old) (insert-x-in-x CTXT0 __t1->0 true)
    (ifnull-74-__t0->*->0 CTXT0 __t1->1->*->0 p!old->*->*->0 x x!old null?2)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t1->1->*->1->*->0 p!old->*->*->0 x
     x!old __t1->1->*->0 null?3)
    (= __t2->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 __t2->*->0 p!old->*->*->0 x x!old null?4)
    (fold-72-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 p!old->*->*->0 x x!old
     __t2->*->0 null?5)
    (= __t3 0)
    (ifnull-26-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 x x!old null?6)
    (ifnull-26-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 x x!old
     hd->*->0 null?7)
    (= p->*->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?8)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?9)
    (= x __t1->0) (= x x!old) (insert-x-in-x CTXT0 x true) (= NU p->*->*->0)
    (= NU __t1->0)
    (fold-72-__t2->*->0 CTXT0 NU p!old->*->*->0 x x!old null?10))
   (scope-70-p->*->*->0 CTXT0 NU p!old->*->*->0 x x!old null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t3 Int) (__t2->*->1->*->0 Int) (__t2->*->0 Int)
   (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int)
   (__t0->*->1->*->0 Int) (__t0->*->0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-74-__t0->*->0 CTXT0 __t0->*->0 p!old->*->*->0 x x!old null?0)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 p!old->*->*->0 x x!old
     __t0->*->0 null?1)
    (= __t1->0 x) (= __t1->0 x!old) (insert-x-in-x CTXT0 __t1->0 true)
    (ifnull-74-__t0->*->0 CTXT0 __t1->1->*->0 p!old->*->*->0 x x!old null?2)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t1->1->*->1->*->0 p!old->*->*->0 x
     x!old __t1->1->*->0 null?3)
    (= __t2->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 __t2->*->0 p!old->*->*->0 x x!old null?4)
    (fold-72-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 p!old->*->*->0 x x!old
     __t2->*->0 null?5)
    (= __t3 0)
    (ifnull-26-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 x x!old null?6)
    (ifnull-26-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 x x!old
     hd->*->0 null?7)
    (= p->*->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?8)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?9)
    (= x __t1->0) (= x x!old) (insert-x-in-x CTXT0 x true)
    (fold-72-__t2->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old p->*->*->0
     null?10))
   (insert-p-out-p->*->*->1->*->0 CTXT0 NU x p->*->*->0 null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t3 Int) (__t2->*->1->*->0 Int) (__t2->*->0 Int)
   (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int)
   (__t0->*->1->*->0 Int) (__t0->*->0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-74-__t0->*->0 CTXT0 __t0->*->0 p!old->*->*->0 x x!old null?0)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 p!old->*->*->0 x x!old
     __t0->*->0 null?1)
    (= __t1->0 x) (= __t1->0 x!old) (insert-x-in-x CTXT0 __t1->0 true)
    (ifnull-74-__t0->*->0 CTXT0 __t1->1->*->0 p!old->*->*->0 x x!old null?2)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t1->1->*->1->*->0 p!old->*->*->0 x
     x!old __t1->1->*->0 null?3)
    (= __t2->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 __t2->*->0 p!old->*->*->0 x x!old null?4)
    (fold-72-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 p!old->*->*->0 x x!old
     __t2->*->0 null?5)
    (= __t3 0)
    (ifnull-26-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 x x!old null?6)
    (ifnull-26-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 x x!old
     hd->*->0 null?7)
    (= p->*->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?8)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?9)
    (= x __t1->0) (= x x!old) (insert-x-in-x CTXT0 x true) (= NU p->*->*->0)
    (= NU __t1->0)
    (fold-72-__t2->*->0 CTXT0 NU p!old->*->*->0 x x!old null?10))
   (insert-p-out-p->*->*->0 CTXT0 NU p!old->*->*->0 x null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t3 Int) (__t2->*->1->*->0 Int) (__t2->*->0 Int)
   (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int)
   (__t0->*->1->*->0 Int) (__t0->*->0 Int) (null?9 Bool) (null?8 Bool)
   (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-74-__t0->*->0 CTXT0 __t0->*->0 p!old->*->*->0 x x!old null?0)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 p!old->*->*->0 x x!old
     __t0->*->0 null?1)
    (= __t1->0 x) (= __t1->0 x!old) (insert-x-in-x CTXT0 __t1->0 true)
    (ifnull-74-__t0->*->0 CTXT0 __t1->1->*->0 p!old->*->*->0 x x!old null?2)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t1->1->*->1->*->0 p!old->*->*->0 x
     x!old __t1->1->*->0 null?3)
    (= __t2->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 __t2->*->0 p!old->*->*->0 x x!old null?4)
    (fold-72-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 p!old->*->*->0 x x!old
     __t2->*->0 null?5)
    (= __t3 0)
    (ifnull-26-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 x x!old null?6)
    (ifnull-26-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 x x!old
     hd->*->0 null?7)
    (= p->*->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?8)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?9)
    (= x __t1->0) (= x x!old) (insert-x-in-x CTXT0 x true) (= NU x)
    (= NU __t1->0) (= NU x!old) (insert-x-in-x CTXT0 NU true))
   (insert-x-out-x CTXT0 NU x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (<ret> Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t3 Int) (__t2->*->1->*->0 Int) (__t2->*->0 Int)
   (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int)
   (__t0->*->1->*->0 Int) (__t0->*->0 Int) (null?9 Bool) (null?8 Bool)
   (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-74-__t0->*->0 CTXT0 __t0->*->0 p!old->*->*->0 x x!old null?0)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 p!old->*->*->0 x x!old
     __t0->*->0 null?1)
    (= __t1->0 x) (= __t1->0 x!old) (insert-x-in-x CTXT0 __t1->0 true)
    (ifnull-74-__t0->*->0 CTXT0 __t1->1->*->0 p!old->*->*->0 x x!old null?2)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t1->1->*->1->*->0 p!old->*->*->0 x
     x!old __t1->1->*->0 null?3)
    (= __t2->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 __t2->*->0 p!old->*->*->0 x x!old null?4)
    (fold-72-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 p!old->*->*->0 x x!old
     __t2->*->0 null?5)
    (= __t3 0)
    (ifnull-26-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 x x!old null?6)
    (ifnull-26-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 x x!old
     hd->*->0 null?7)
    (= p->*->*->0 __t1->0)
    (fold-72-__t2->*->0 CTXT0 p->*->*->0 p!old->*->*->0 x x!old null?8)
    (fold-72-__t2->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0 x x!old
     p->*->*->0 null?9)
    (= x __t1->0) (= x x!old) (insert-x-in-x CTXT0 x true) (= <ret> 0)
    (= NU 0))
   (insert-ret-RET CTXT0 NU x true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int)
   (__t0->*->1->*->0 Int) (__t0->*->0 Int) (null?8 Bool) (null?7 Bool)
   (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-74-__t0->*->0 CTXT0 __t0->*->0 p!old->*->*->0 x x!old null?0)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 p!old->*->*->0 x x!old
     __t0->*->0 null?1)
    (= __t1->0 x) (= __t1->0 x!old) (insert-x-in-x CTXT0 __t1->0 true)
    (ifnull-74-__t0->*->0 CTXT0 __t1->1->*->0 p!old->*->*->0 x x!old null?2)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t1->1->*->1->*->0 p!old->*->*->0 x
     x!old __t1->1->*->0 null?3)
    (ifnull-26-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 x x!old null?4)
    (ifnull-26-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 x x!old
     hd->*->0 null?5)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?6)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?7)
    (= x __t1->0) (= x x!old) (insert-x-in-x CTXT0 x true)
    (ifnull-74-__t0->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old __t1->1->*->0
     null?8))
   (fold-72-__t2->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old __t1->1->*->0
    null?8))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int)
   (__t0->*->1->*->0 Int) (__t0->*->0 Int) (null?8 Bool) (null?7 Bool)
   (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-74-__t0->*->0 CTXT0 __t0->*->0 p!old->*->*->0 x x!old null?0)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 p!old->*->*->0 x x!old
     __t0->*->0 null?1)
    (= __t1->0 x) (= __t1->0 x!old) (insert-x-in-x CTXT0 __t1->0 true)
    (ifnull-74-__t0->*->0 CTXT0 __t1->1->*->0 p!old->*->*->0 x x!old null?2)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t1->1->*->1->*->0 p!old->*->*->0 x
     x!old __t1->1->*->0 null?3)
    (ifnull-26-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 x x!old null?4)
    (ifnull-26-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 x x!old
     hd->*->0 null?5)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?6)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?7)
    (= x __t1->0) (= x x!old) (insert-x-in-x CTXT0 x true)
    (ifnull-74-__t0->*->0 CTXT0 NU p!old->*->*->0 x x!old null?8))
   (fold-72-__t2->*->1->*->0 CTXT0 NU p!old->*->*->0 x x!old __t1->0 null?8))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int)
   (__t0->*->1->*->0 Int) (__t0->*->0 Int) (null?7 Bool) (null?6 Bool)
   (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (ifnull-74-__t0->*->0 CTXT0 __t0->*->0 p!old->*->*->0 x x!old null?0)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t0->*->1->*->0 p!old->*->*->0 x x!old
     __t0->*->0 null?1)
    (= __t1->0 x) (= __t1->0 x!old) (insert-x-in-x CTXT0 __t1->0 true)
    (ifnull-74-__t0->*->0 CTXT0 __t1->1->*->0 p!old->*->*->0 x x!old null?2)
    (ifnull-74-__t0->*->1->*->0 CTXT0 __t1->1->*->1->*->0 p!old->*->*->0 x
     x!old __t1->1->*->0 null?3)
    (ifnull-26-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 x x!old null?4)
    (ifnull-26-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 x x!old
     hd->*->0 null?5)
    (= p->*->*->0 p!old->*->*->0)
    (insert-p-in-p->*->*->0 CTXT0 p->*->*->0 x null?6)
    (insert-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 x p->*->*->0 null?7)
    (= x __t1->0) (= x x!old) (insert-x-in-x CTXT0 x true) (= NU x)
    (= NU x!old) (insert-x-in-x CTXT0 NU true))
   (fold-72-__t2->*->0 CTXT0 NU p!old->*->*->0 x x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-50-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-50-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-50-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-50-x CTXT0 x p!old->*->0 x!old true)
    (scope-50-x!old CTXT0 x!old p!old->*->0 x true) (= NU x!old)
    (scope-50-x!old CTXT0 NU p!old->*->0 x true))
   (join-20-x!old CTXT0 NU p!old->*->0 x true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-18-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (join-18-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (join-18-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (join-18-x CTXT0 x p!old->*->0 x!old true)
    (join-18-x!old CTXT0 x!old p!old->*->0 x true) (= NU x!old)
    (join-18-x!old CTXT0 NU p!old->*->0 x true))
   (join-20-x!old CTXT0 NU p!old->*->0 x true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-50-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-50-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-50-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-50-x CTXT0 x p!old->*->0 x!old true)
    (scope-50-x!old CTXT0 x!old p!old->*->0 x true) (= NU x)
    (scope-50-x CTXT0 NU p!old->*->0 x!old true))
   (join-20-x CTXT0 NU p!old->*->0 x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-18-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (join-18-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (join-18-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (join-18-x CTXT0 x p!old->*->0 x!old true)
    (join-18-x!old CTXT0 x!old p!old->*->0 x true) (= NU x)
    (join-18-x CTXT0 NU p!old->*->0 x!old true))
   (join-20-x CTXT0 NU p!old->*->0 x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-50-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-50-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-50-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-50-x CTXT0 x p!old->*->0 x!old true)
    (scope-50-x!old CTXT0 x!old p!old->*->0 x true) (= NU p!old->*->0)
    (scope-50-p!old->*->0 CTXT0 NU x x!old true))
   (join-20-p!old->*->0 CTXT0 NU x x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-18-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (join-18-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (join-18-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (join-18-x CTXT0 x p!old->*->0 x!old true)
    (join-18-x!old CTXT0 x!old p!old->*->0 x true) (= NU p!old->*->0)
    (join-18-p!old->*->0 CTXT0 NU x x!old true))
   (join-20-p!old->*->0 CTXT0 NU x x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (scope-50-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-50-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-50-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-50-x CTXT0 x p!old->*->0 x!old true)
    (scope-50-x!old CTXT0 x!old p!old->*->0 x true)
    (scope-50-p->*->1->*->0 CTXT0 NU p!old->*->0 x x!old p->*->0 null?2))
   (join-20-p->*->1->*->0 CTXT0 NU p!old->*->0 x x!old p->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (scope-50-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-50-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-50-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-50-x CTXT0 x p!old->*->0 x!old true)
    (scope-50-x!old CTXT0 x!old p!old->*->0 x true) (= NU p->*->0)
    (scope-50-p->*->0 CTXT0 NU p!old->*->0 x x!old null?2))
   (join-20-p->*->0 CTXT0 NU p!old->*->0 x x!old null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (join-18-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (join-18-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (join-18-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (join-18-x CTXT0 x p!old->*->0 x!old true)
    (join-18-x!old CTXT0 x!old p!old->*->0 x true)
    (join-18-p->*->1->*->0 CTXT0 NU p!old->*->0 x x!old p->*->0 null?2))
   (join-20-p->*->1->*->0 CTXT0 NU p!old->*->0 x x!old p->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (join-18-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (join-18-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (join-18-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (join-18-x CTXT0 x p!old->*->0 x!old true)
    (join-18-x!old CTXT0 x!old p!old->*->0 x true) (= NU p->*->0)
    (join-18-p->*->0 CTXT0 NU p!old->*->0 x x!old null?2))
   (join-20-p->*->0 CTXT0 NU p!old->*->0 x x!old null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t4 Int) (__t3->1->*->1->*->0 Int) (__t3->1->*->0 Int) (__t3->0 Int)
   (__t2->*->1->*->0 Int) (__t2->*->0 Int) (__t1->1->*->1->*->0 Int)
   (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (= __t2->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t2->*->0 __t0 p!old->*->0 v x x!old null?2)
    (fold-53-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t2->*->0 null?3)
    (= __t3->0 x) (= __t3->0 x!old) (insert_loop-x-in-x CTXT0 __t3->0 true)
    (= __t3->1->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t3->1->*->0 __t0 p!old->*->0 v x x!old
     null?4)
    (fold-53-__t2->*->1->*->0 CTXT0 __t3->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->1->*->0 null?5)
    (= __t4 0) (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?7)
    (= p->*->0 __t3->0)
    (fold-19-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?8)
    (fold-19-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?9)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t3->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true) (= NU x!old))
   (scope-50-x!old CTXT0 NU p!old->*->0 x null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t4 Int) (__t3->1->*->1->*->0 Int) (__t3->1->*->0 Int) (__t3->0 Int)
   (__t2->*->1->*->0 Int) (__t2->*->0 Int) (__t1->1->*->1->*->0 Int)
   (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (= __t2->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t2->*->0 __t0 p!old->*->0 v x x!old null?2)
    (fold-53-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t2->*->0 null?3)
    (= __t3->0 x) (= __t3->0 x!old) (insert_loop-x-in-x CTXT0 __t3->0 true)
    (= __t3->1->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t3->1->*->0 __t0 p!old->*->0 v x x!old
     null?4)
    (fold-53-__t2->*->1->*->0 CTXT0 __t3->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->1->*->0 null?5)
    (= __t4 0) (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?7)
    (= p->*->0 __t3->0)
    (fold-19-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?8)
    (fold-19-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?9)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t3->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true) (= NU x)
    (= NU __t3->0) (= NU x!old) (insert_loop-x-in-x CTXT0 NU null?10))
   (scope-50-x CTXT0 NU p!old->*->0 x!old null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t4 Int) (__t3->1->*->1->*->0 Int) (__t3->1->*->0 Int) (__t3->0 Int)
   (__t2->*->1->*->0 Int) (__t2->*->0 Int) (__t1->1->*->1->*->0 Int)
   (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (= __t2->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t2->*->0 __t0 p!old->*->0 v x x!old null?2)
    (fold-53-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t2->*->0 null?3)
    (= __t3->0 x) (= __t3->0 x!old) (insert_loop-x-in-x CTXT0 __t3->0 true)
    (= __t3->1->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t3->1->*->0 __t0 p!old->*->0 v x x!old
     null?4)
    (fold-53-__t2->*->1->*->0 CTXT0 __t3->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->1->*->0 null?5)
    (= __t4 0) (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?7)
    (= p->*->0 __t3->0)
    (fold-19-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?8)
    (fold-19-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?9)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t3->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (= NU p!old->*->0))
   (scope-50-p!old->*->0 CTXT0 NU x x!old null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t4 Int) (__t3->1->*->1->*->0 Int) (__t3->1->*->0 Int) (__t3->0 Int)
   (__t2->*->1->*->0 Int) (__t2->*->0 Int) (__t1->1->*->1->*->0 Int)
   (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (= __t2->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t2->*->0 __t0 p!old->*->0 v x x!old null?2)
    (fold-53-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t2->*->0 null?3)
    (= __t3->0 x) (= __t3->0 x!old) (insert_loop-x-in-x CTXT0 __t3->0 true)
    (= __t3->1->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t3->1->*->0 __t0 p!old->*->0 v x x!old
     null?4)
    (fold-53-__t2->*->1->*->0 CTXT0 __t3->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->1->*->0 null?5)
    (= __t4 0) (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?7)
    (= p->*->0 __t3->0)
    (fold-19-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?8)
    (fold-19-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?9)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t3->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (= NU p->*->1->*->0)
    (fold-19-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0
     null?10))
   (scope-50-p->*->1->*->0 CTXT0 NU p!old->*->0 x x!old p->*->0 null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t4 Int) (__t3->1->*->1->*->0 Int) (__t3->1->*->0 Int) (__t3->0 Int)
   (__t2->*->1->*->0 Int) (__t2->*->0 Int) (__t1->1->*->1->*->0 Int)
   (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (= __t2->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t2->*->0 __t0 p!old->*->0 v x x!old null?2)
    (fold-53-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t2->*->0 null?3)
    (= __t3->0 x) (= __t3->0 x!old) (insert_loop-x-in-x CTXT0 __t3->0 true)
    (= __t3->1->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t3->1->*->0 __t0 p!old->*->0 v x x!old
     null?4)
    (fold-53-__t2->*->1->*->0 CTXT0 __t3->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->1->*->0 null?5)
    (= __t4 0) (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?7)
    (= p->*->0 __t3->0)
    (fold-19-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?8)
    (fold-19-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?9)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t3->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (= NU p->*->0) (= NU __t3->0)
    (fold-19-p->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old null?10))
   (scope-50-p->*->0 CTXT0 NU p!old->*->0 x x!old null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t4 Int) (__t3->1->*->1->*->0 Int) (__t3->1->*->0 Int) (__t3->0 Int)
   (__t2->*->1->*->0 Int) (__t2->*->0 Int) (__t1->1->*->1->*->0 Int)
   (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (= __t2->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t2->*->0 __t0 p!old->*->0 v x x!old null?2)
    (fold-53-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t2->*->0 null?3)
    (= __t3->0 x) (= __t3->0 x!old) (insert_loop-x-in-x CTXT0 __t3->0 true)
    (= __t3->1->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t3->1->*->0 __t0 p!old->*->0 v x x!old
     null?4)
    (fold-53-__t2->*->1->*->0 CTXT0 __t3->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->1->*->0 null?5)
    (= __t4 0) (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?7)
    (= p->*->0 __t3->0)
    (fold-19-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?8)
    (fold-19-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?9)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t3->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (fold-19-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0
     null?10))
   (insert_loop-p-out-p->*->1->*->0 CTXT0 NU x p->*->0 null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t4 Int) (__t3->1->*->1->*->0 Int) (__t3->1->*->0 Int) (__t3->0 Int)
   (__t2->*->1->*->0 Int) (__t2->*->0 Int) (__t1->1->*->1->*->0 Int)
   (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (= __t2->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t2->*->0 __t0 p!old->*->0 v x x!old null?2)
    (fold-53-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t2->*->0 null?3)
    (= __t3->0 x) (= __t3->0 x!old) (insert_loop-x-in-x CTXT0 __t3->0 true)
    (= __t3->1->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t3->1->*->0 __t0 p!old->*->0 v x x!old
     null?4)
    (fold-53-__t2->*->1->*->0 CTXT0 __t3->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->1->*->0 null?5)
    (= __t4 0) (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?7)
    (= p->*->0 __t3->0)
    (fold-19-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?8)
    (fold-19-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?9)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t3->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (= NU p->*->0) (= NU __t3->0)
    (fold-19-p->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old null?10))
   (insert_loop-p-out-p->*->0 CTXT0 NU p!old->*->0 x null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t4 Int) (__t3->1->*->1->*->0 Int) (__t3->1->*->0 Int) (__t3->0 Int)
   (__t2->*->1->*->0 Int) (__t2->*->0 Int) (__t1->1->*->1->*->0 Int)
   (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int) (null?9 Bool) (null?8 Bool)
   (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (= __t2->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t2->*->0 __t0 p!old->*->0 v x x!old null?2)
    (fold-53-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t2->*->0 null?3)
    (= __t3->0 x) (= __t3->0 x!old) (insert_loop-x-in-x CTXT0 __t3->0 true)
    (= __t3->1->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t3->1->*->0 __t0 p!old->*->0 v x x!old
     null?4)
    (fold-53-__t2->*->1->*->0 CTXT0 __t3->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->1->*->0 null?5)
    (= __t4 0) (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?7)
    (= p->*->0 __t3->0)
    (fold-19-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?8)
    (fold-19-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?9)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t3->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true) (= NU x)
    (= NU __t3->0) (= NU x!old) (insert_loop-x-in-x CTXT0 NU true))
   (insert_loop-x-out-x CTXT0 NU x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (<ret> Int) (x!old Int) (x Int) (v Int)
   (p!old->*->0 Int) (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int)
   (nxt->*->0 Int) (__t4 Int) (__t3->1->*->1->*->0 Int) (__t3->1->*->0 Int)
   (__t3->0 Int) (__t2->*->1->*->0 Int) (__t2->*->0 Int)
   (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int)
   (null?9 Bool) (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (= __t2->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t2->*->0 __t0 p!old->*->0 v x x!old null?2)
    (fold-53-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t2->*->0 null?3)
    (= __t3->0 x) (= __t3->0 x!old) (insert_loop-x-in-x CTXT0 __t3->0 true)
    (= __t3->1->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t3->1->*->0 __t0 p!old->*->0 v x x!old
     null?4)
    (fold-53-__t2->*->1->*->0 CTXT0 __t3->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->1->*->0 null?5)
    (= __t4 0) (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?7)
    (= p->*->0 __t3->0)
    (fold-19-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?8)
    (fold-19-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?9)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t3->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true) (= <ret> 0)
    (= NU 0))
   (insert_loop-ret-RET CTXT0 NU x true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t3->1->*->1->*->0 Int) (__t3->1->*->0 Int) (__t3->0 Int)
   (__t2->*->1->*->0 Int) (__t2->*->0 Int) (__t1->1->*->1->*->0 Int)
   (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (= __t2->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t2->*->0 __t0 p!old->*->0 v x x!old null?2)
    (fold-53-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t2->*->0 null?3)
    (= __t3->0 x) (= __t3->0 x!old) (insert_loop-x-in-x CTXT0 __t3->0 true)
    (= __t3->1->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t3->1->*->0 __t0 p!old->*->0 v x x!old
     null?4)
    (fold-53-__t2->*->1->*->0 CTXT0 __t3->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->1->*->0 null?5)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?7)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?8)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?9)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t3->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (fold-53-__t2->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old
     __t3->1->*->0 null?10))
   (fold-19-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old __t3->1->*->0
    null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t3->1->*->1->*->0 Int) (__t3->1->*->0 Int) (__t3->0 Int)
   (__t2->*->1->*->0 Int) (__t2->*->0 Int) (__t1->1->*->1->*->0 Int)
   (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (= __t2->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t2->*->0 __t0 p!old->*->0 v x x!old null?2)
    (fold-53-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t2->*->0 null?3)
    (= __t3->0 x) (= __t3->0 x!old) (insert_loop-x-in-x CTXT0 __t3->0 true)
    (= __t3->1->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t3->1->*->0 __t0 p!old->*->0 v x x!old
     null?4)
    (fold-53-__t2->*->1->*->0 CTXT0 __t3->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->1->*->0 null?5)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?7)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?8)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?9)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t3->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (= NU __t1->0)
    (fold-53-__t2->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old null?10))
   (fold-19-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old __t3->0
    null?10))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t3->1->*->1->*->0 Int) (__t3->1->*->0 Int) (__t3->0 Int)
   (__t2->*->1->*->0 Int) (__t2->*->0 Int) (__t1->1->*->1->*->0 Int)
   (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int) (null?9 Bool) (null?8 Bool)
   (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (= __t2->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t2->*->0 __t0 p!old->*->0 v x x!old null?2)
    (fold-53-__t2->*->1->*->0 CTXT0 __t2->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t2->*->0 null?3)
    (= __t3->0 x) (= __t3->0 x!old) (insert_loop-x-in-x CTXT0 __t3->0 true)
    (= __t3->1->*->0 __t1->0)
    (fold-53-__t2->*->0 CTXT0 __t3->1->*->0 __t0 p!old->*->0 v x x!old
     null?4)
    (fold-53-__t2->*->1->*->0 CTXT0 __t3->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->1->*->0 null?5)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?7)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?8)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?9)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t3->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true) (= NU x)
    (= NU x!old) (insert_loop-x-in-x CTXT0 NU true))
   (fold-19-p->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int)
   (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?3)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?4)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?5)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x __t1->1->*->0 null?6))
   (fold-53-__t2->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old
    __t1->1->*->0 null?6))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int)
   (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?3)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?4)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?5)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x v null?6))
   (fold-53-__t2->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old __t1->0
    null?6))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t1->1->*->1->*->0 Int) (__t1->1->*->0 Int) (__t1->0 Int) (__t0 Int)
   (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (uneq __t0 0) (rel-<-out __t0 v x) (= __t1->0 v)
    (= __t1->0 p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 __t1->0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 __t1->1->*->1->*->0 x __t1->1->*->0
     null?1)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?3)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?4)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?5)
    (= v __t1->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x x!old) (insert_loop-x-in-x CTXT0 x true) (= NU v) (= NU p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 NU x true))
   (fold-53-__t2->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-55-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-55-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-55-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-55-x CTXT0 x p!old->*->0 x!old true)
    (scope-55-x!old CTXT0 x!old p!old->*->0 x true) (= NU x!old)
    (scope-55-x!old CTXT0 NU p!old->*->0 x true))
   (join-18-x!old CTXT0 NU p!old->*->0 x true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-59-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-59-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-59-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-59-x CTXT0 x p!old->*->0 x!old true)
    (scope-59-x!old CTXT0 x!old p!old->*->0 x true) (= NU x!old)
    (scope-59-x!old CTXT0 NU p!old->*->0 x true))
   (join-18-x!old CTXT0 NU p!old->*->0 x true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-55-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-55-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-55-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-55-x CTXT0 x p!old->*->0 x!old true)
    (scope-55-x!old CTXT0 x!old p!old->*->0 x true) (= NU x)
    (scope-55-x CTXT0 NU p!old->*->0 x!old true))
   (join-18-x CTXT0 NU p!old->*->0 x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-59-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-59-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-59-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-59-x CTXT0 x p!old->*->0 x!old true)
    (scope-59-x!old CTXT0 x!old p!old->*->0 x true) (= NU x)
    (scope-59-x CTXT0 NU p!old->*->0 x!old true))
   (join-18-x CTXT0 NU p!old->*->0 x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-55-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-55-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-55-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-55-x CTXT0 x p!old->*->0 x!old true)
    (scope-55-x!old CTXT0 x!old p!old->*->0 x true) (= NU p!old->*->0)
    (scope-55-p!old->*->0 CTXT0 NU x x!old true))
   (join-18-p!old->*->0 CTXT0 NU x x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-59-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-59-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-59-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-59-x CTXT0 x p!old->*->0 x!old true)
    (scope-59-x!old CTXT0 x!old p!old->*->0 x true) (= NU p!old->*->0)
    (scope-59-p!old->*->0 CTXT0 NU x x!old true))
   (join-18-p!old->*->0 CTXT0 NU x x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (scope-55-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-55-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-55-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-55-x CTXT0 x p!old->*->0 x!old true)
    (scope-55-x!old CTXT0 x!old p!old->*->0 x true)
    (scope-55-p->*->1->*->0 CTXT0 NU p!old->*->0 x x!old p->*->0 null?2))
   (join-18-p->*->1->*->0 CTXT0 NU p!old->*->0 x x!old p->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (scope-55-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-55-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-55-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-55-x CTXT0 x p!old->*->0 x!old true)
    (scope-55-x!old CTXT0 x!old p!old->*->0 x true) (= NU p->*->0)
    (scope-55-p->*->0 CTXT0 NU p!old->*->0 x x!old null?2))
   (join-18-p->*->0 CTXT0 NU p!old->*->0 x x!old null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (scope-59-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-59-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-59-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-59-x CTXT0 x p!old->*->0 x!old true)
    (scope-59-x!old CTXT0 x!old p!old->*->0 x true)
    (scope-59-p->*->1->*->0 CTXT0 NU p!old->*->0 x x!old p->*->0 null?2))
   (join-18-p->*->1->*->0 CTXT0 NU p!old->*->0 x x!old p->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (scope-59-p->*->0 CTXT0 p->*->0 p!old->*->0 x x!old null?0)
    (scope-59-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 x x!old p->*->0
     null?1)
    (scope-59-p!old->*->0 CTXT0 p!old->*->0 x x!old true)
    (scope-59-x CTXT0 x p!old->*->0 x!old true)
    (scope-59-x!old CTXT0 x!old p!old->*->0 x true) (= NU p->*->0)
    (scope-59-p->*->0 CTXT0 NU p!old->*->0 x x!old null?2))
   (join-18-p->*->0 CTXT0 NU p!old->*->0 x x!old null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t1 Int) (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x) (= __t1 0)
    (shuf-17-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old p->*->0
     null?0)
    (shuf-17-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (shuf-17-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (= NU x!old))
   (scope-55-x!old CTXT0 NU p!old->*->0 x null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t1 Int) (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x) (= __t1 0)
    (shuf-17-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old p->*->0
     null?0)
    (shuf-17-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (shuf-17-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (= NU x)
    (scope-16-x CTXT0 NU __t0 p!old->*->0 v x!old null?4))
   (scope-55-x CTXT0 NU p!old->*->0 x!old null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t1 Int) (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x) (= __t1 0)
    (shuf-17-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old p->*->0
     null?0)
    (shuf-17-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (shuf-17-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (= NU p!old->*->0))
   (scope-55-p!old->*->0 CTXT0 NU x x!old null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t1 Int) (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x) (= __t1 0)
    (shuf-17-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old p->*->0
     null?0)
    (shuf-17-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (shuf-17-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (= NU p->*->1->*->0)
    (shuf-17-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0
     null?4))
   (scope-55-p->*->1->*->0 CTXT0 NU p!old->*->0 x x!old p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t1 Int) (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x) (= __t1 0)
    (shuf-17-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old p->*->0
     null?0)
    (shuf-17-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (shuf-17-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (= NU p->*->0)
    (= NU v) (= NU p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 NU x null?4))
   (scope-55-p->*->0 CTXT0 NU p!old->*->0 x x!old null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t1 Int) (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x) (= __t1 0)
    (shuf-17-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old p->*->0
     null?0)
    (shuf-17-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (shuf-17-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true)
    (shuf-17-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0
     null?4))
   (insert_loop-p-out-p->*->1->*->0 CTXT0 NU x p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t1 Int) (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x) (= __t1 0)
    (shuf-17-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old p->*->0
     null?0)
    (shuf-17-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (shuf-17-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (= NU p->*->0)
    (= NU v) (= NU p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 NU x null?4))
   (insert_loop-p-out-p->*->0 CTXT0 NU p!old->*->0 x null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t1 Int) (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x) (= __t1 0)
    (shuf-17-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old p->*->0
     null?0)
    (shuf-17-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (shuf-17-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (= NU x)
    (scope-16-x CTXT0 NU __t0 p!old->*->0 v x!old true))
   (insert_loop-x-out-x CTXT0 NU x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (<ret> Int) (x!old Int) (x Int) (v Int)
   (p!old->*->0 Int) (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int)
   (nxt->*->0 Int) (__t1 Int) (__t0 Int) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x) (= __t1 0)
    (shuf-17-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old p->*->0
     null?0)
    (shuf-17-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (shuf-17-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (= <ret> 0) (= NU 0))
   (insert_loop-ret-RET CTXT0 NU x true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (> 0. 0.) (> 0. 0.)
    (> 1. 0.) (> 1. 0.) (> 0. 0.) (> 0. 0.)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x nxt->*->0 null?4)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v
     nxt->*->0 null?4))
   (shuf-17-nxt->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0
    nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (> 0. 0.) (> 0. 0.)
    (or (= 1. 0.) (= 1. 0.)) (> 0. 0.) (> 0. 0.)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x nxt->*->0 null?4))
   (shuf-17-nxt->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0
    nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true)
    (or (= 0. 0.) (= 0. 0.)) (> 1. 0.) (> 1. 0.) (> 0. 0.) (> 0. 0.)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v
     nxt->*->0 null?4))
   (shuf-17-nxt->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0
    nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true)
    (or (= 0. 0.) (= 0. 0.)))
   (shuf-17-nxt->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0
    nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (> 0. 0.) (> 1. 0.)
    (> 0. 0.) (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x p->*->0 null?4)
    (call-15-nxt-out-nxt->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v null?4))
   (shuf-17-nxt->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (> 0. 0.)
    (or (= 1. 0.)) (> 0. 0.)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x p->*->0 null?4))
   (shuf-17-nxt->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (or (= 0. 0.))
    (> 1. 0.) (> 0. 0.)
    (call-15-nxt-out-nxt->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v null?4))
   (shuf-17-nxt->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (or (= 0. 0.)))
   (shuf-17-nxt->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (> 0. 0.) (> 0. 0.)
    (> 1. 0.) (> 1. 0.) (> 1. 0.) (> 1. 0.)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x p->*->1->*->0 null?4)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v
     p->*->1->*->0 null?4))
   (shuf-17-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->1->*->0
    null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (> 0. 0.) (> 0. 0.)
    (or (= 1. 0.) (= 1. 0.)) (> 1. 0.) (> 1. 0.)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x p->*->1->*->0 null?4))
   (shuf-17-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->1->*->0
    null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true)
    (or (= 0. 0.) (= 0. 0.)) (> 1. 0.) (> 1. 0.) (> 1. 0.) (> 1. 0.)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v
     p->*->1->*->0 null?4))
   (shuf-17-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->1->*->0
    null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true)
    (or (= 1. 0.) (= 1. 0.)))
   (shuf-17-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->1->*->0
    null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (> 0. 0.) (> 1. 0.)
    (> 1. 0.) (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x p->*->0 null?4)
    (call-15-nxt-out-nxt->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v null?4))
   (shuf-17-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (> 0. 0.)
    (or (= 1. 0.)) (> 1. 0.)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x p->*->0 null?4))
   (shuf-17-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (or (= 0. 0.))
    (> 1. 0.) (> 1. 0.)
    (call-15-nxt-out-nxt->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v null?4))
   (shuf-17-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (scope-16-x CTXT0 x __t0 p!old->*->0 v x!old true) (or (= 1. 0.)))
   (shuf-17-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t1 Int) (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x) (insert_loop-ret-RET 15 __t1 x true)
    (call-15-nxt-out-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v
     null?0)
    (call-15-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v
     x x!old v nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (= NU x) (= NU x!old)
    (insert_loop-x-in-x CTXT0 NU null?4))
   (scope-16-x CTXT0 NU __t0 p!old->*->0 v x!old null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x nxt->*->0 null?4))
   (insert_loop-p-in-p->*->1->*->0 15 NU x nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (= NU nxt->*->0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x v null?4))
   (insert_loop-p-in-p->*->0 15 NU x null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (> 1. 0.) (> 1. 0.) (> 0. 0.) (> 0. 0.)
    (> 1. 0.) (> 1. 0.)
    (insert_loop-p-out-p->*->1->*->0 15 NU x nxt->*->0 null?4)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x nxt->*->0 null?4))
   (call-15-nxt-out-nxt->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v
    nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (> 1. 0.) (> 1. 0.)
    (or (= 0. 0.) (= 0. 0.)) (> 1. 0.) (> 1. 0.)
    (insert_loop-p-out-p->*->1->*->0 15 NU x nxt->*->0 null?4))
   (call-15-nxt-out-nxt->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v
    nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (or (= 1. 0.) (= 1. 0.)) (> 0. 0.)
    (> 0. 0.) (> 1. 0.) (> 1. 0.)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x nxt->*->0 null?4))
   (call-15-nxt-out-nxt->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v
    nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (or (= 1. 0.) (= 1. 0.)))
   (call-15-nxt-out-nxt->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v
    nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (x!old Int) (x Int) (v Int)
   (p!old->*->0 Int) (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int)
   (nxt->*->0 Int) (__t0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (= !pre nxt->*->0) (= !pre nxt->*->0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 !pre x v null?4) (> 1. 0.)
    (> 0. 0.) (> 1. 0.) (insert_loop-p-out-p->*->0 15 NU !pre x null?5)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x v null?5))
   (call-15-nxt-out-nxt->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (x!old Int) (x Int) (v Int)
   (p!old->*->0 Int) (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int)
   (nxt->*->0 Int) (__t0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (= !pre nxt->*->0) (= !pre nxt->*->0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 !pre x v null?4) (> 1. 0.)
    (or (= 0. 0.)) (> 1. 0.) (insert_loop-p-out-p->*->0 15 NU !pre x null?5))
   (call-15-nxt-out-nxt->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (x!old Int) (x Int) (v Int)
   (p!old->*->0 Int) (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int)
   (nxt->*->0 Int) (__t0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (= !pre nxt->*->0) (= !pre nxt->*->0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 !pre x v null?4) (or (= 1. 0.))
    (> 0. 0.) (> 1. 0.) (insert_loop-p-in-p->*->1->*->0 CTXT0 NU x v null?5))
   (call-15-nxt-out-nxt->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (x!old Int) (x Int) (v Int)
   (p!old->*->0 Int) (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int)
   (nxt->*->0 Int) (__t0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (= !pre nxt->*->0) (= !pre nxt->*->0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 !pre x v null?4) (or (= 1. 0.)))
   (call-15-nxt-out-nxt->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old v null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (= NU x) (= NU x!old)
    (insert_loop-x-in-x CTXT0 NU true))
   (insert_loop-x-in-x 15 NU true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t5 Int) (__t4->1->*->1->*->0 Int) (__t4->1->*->0 Int) (__t4->0 Int)
   (__t3->*->1->*->0 Int) (__t3->*->0 Int) (__t2->1->*->1->*->0 Int)
   (__t2->1->*->0 Int) (__t2->0 Int) (__t1->*->1->*->0 Int) (__t1->*->0 Int)
   (__t0 Int) (null?12 Bool) (null?11 Bool) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (= __t3->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t3->*->0 __t0 p!old->*->0 v x x!old null?4)
    (fold-62-__t3->*->1->*->0 CTXT0 __t3->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->*->0 null?5)
    (= __t4->0 v) (= __t4->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 __t4->0 x true) (= __t4->1->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t4->1->*->0 __t0 p!old->*->0 v x x!old
     null?6)
    (fold-62-__t3->*->1->*->0 CTXT0 __t4->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t4->1->*->0 null?7)
    (= __t5 0)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?8)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?9)
    (= p->*->0 __t4->0)
    (fold-14-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?10)
    (fold-14-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?11)
    (= v __t4->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t2->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true) (= NU x!old))
   (scope-59-x!old CTXT0 NU p!old->*->0 x null?12))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t5 Int) (__t4->1->*->1->*->0 Int) (__t4->1->*->0 Int) (__t4->0 Int)
   (__t3->*->1->*->0 Int) (__t3->*->0 Int) (__t2->1->*->1->*->0 Int)
   (__t2->1->*->0 Int) (__t2->0 Int) (__t1->*->1->*->0 Int) (__t1->*->0 Int)
   (__t0 Int) (null?12 Bool) (null?11 Bool) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (= __t3->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t3->*->0 __t0 p!old->*->0 v x x!old null?4)
    (fold-62-__t3->*->1->*->0 CTXT0 __t3->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->*->0 null?5)
    (= __t4->0 v) (= __t4->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 __t4->0 x true) (= __t4->1->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t4->1->*->0 __t0 p!old->*->0 v x x!old
     null?6)
    (fold-62-__t3->*->1->*->0 CTXT0 __t4->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t4->1->*->0 null?7)
    (= __t5 0)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?8)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?9)
    (= p->*->0 __t4->0)
    (fold-14-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?10)
    (fold-14-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?11)
    (= v __t4->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t2->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true) (= NU x)
    (= NU __t2->0) (= NU x!old) (insert_loop-x-in-x CTXT0 NU null?12))
   (scope-59-x CTXT0 NU p!old->*->0 x!old null?12))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t5 Int) (__t4->1->*->1->*->0 Int) (__t4->1->*->0 Int) (__t4->0 Int)
   (__t3->*->1->*->0 Int) (__t3->*->0 Int) (__t2->1->*->1->*->0 Int)
   (__t2->1->*->0 Int) (__t2->0 Int) (__t1->*->1->*->0 Int) (__t1->*->0 Int)
   (__t0 Int) (null?12 Bool) (null?11 Bool) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (= __t3->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t3->*->0 __t0 p!old->*->0 v x x!old null?4)
    (fold-62-__t3->*->1->*->0 CTXT0 __t3->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->*->0 null?5)
    (= __t4->0 v) (= __t4->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 __t4->0 x true) (= __t4->1->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t4->1->*->0 __t0 p!old->*->0 v x x!old
     null?6)
    (fold-62-__t3->*->1->*->0 CTXT0 __t4->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t4->1->*->0 null?7)
    (= __t5 0)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?8)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?9)
    (= p->*->0 __t4->0)
    (fold-14-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?10)
    (fold-14-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?11)
    (= v __t4->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t2->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (= NU p!old->*->0))
   (scope-59-p!old->*->0 CTXT0 NU x x!old null?12))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t5 Int) (__t4->1->*->1->*->0 Int) (__t4->1->*->0 Int) (__t4->0 Int)
   (__t3->*->1->*->0 Int) (__t3->*->0 Int) (__t2->1->*->1->*->0 Int)
   (__t2->1->*->0 Int) (__t2->0 Int) (__t1->*->1->*->0 Int) (__t1->*->0 Int)
   (__t0 Int) (null?12 Bool) (null?11 Bool) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (= __t3->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t3->*->0 __t0 p!old->*->0 v x x!old null?4)
    (fold-62-__t3->*->1->*->0 CTXT0 __t3->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->*->0 null?5)
    (= __t4->0 v) (= __t4->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 __t4->0 x true) (= __t4->1->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t4->1->*->0 __t0 p!old->*->0 v x x!old
     null?6)
    (fold-62-__t3->*->1->*->0 CTXT0 __t4->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t4->1->*->0 null?7)
    (= __t5 0)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?8)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?9)
    (= p->*->0 __t4->0)
    (fold-14-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?10)
    (fold-14-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?11)
    (= v __t4->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t2->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (= NU p->*->1->*->0)
    (fold-14-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0
     null?12))
   (scope-59-p->*->1->*->0 CTXT0 NU p!old->*->0 x x!old p->*->0 null?12))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t5 Int) (__t4->1->*->1->*->0 Int) (__t4->1->*->0 Int) (__t4->0 Int)
   (__t3->*->1->*->0 Int) (__t3->*->0 Int) (__t2->1->*->1->*->0 Int)
   (__t2->1->*->0 Int) (__t2->0 Int) (__t1->*->1->*->0 Int) (__t1->*->0 Int)
   (__t0 Int) (null?12 Bool) (null?11 Bool) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (= __t3->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t3->*->0 __t0 p!old->*->0 v x x!old null?4)
    (fold-62-__t3->*->1->*->0 CTXT0 __t3->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->*->0 null?5)
    (= __t4->0 v) (= __t4->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 __t4->0 x true) (= __t4->1->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t4->1->*->0 __t0 p!old->*->0 v x x!old
     null?6)
    (fold-62-__t3->*->1->*->0 CTXT0 __t4->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t4->1->*->0 null?7)
    (= __t5 0)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?8)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?9)
    (= p->*->0 __t4->0)
    (fold-14-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?10)
    (fold-14-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?11)
    (= v __t4->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t2->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (= NU p->*->0) (= NU __t4->0)
    (fold-14-p->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old null?12))
   (scope-59-p->*->0 CTXT0 NU p!old->*->0 x x!old null?12))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t5 Int) (__t4->1->*->1->*->0 Int) (__t4->1->*->0 Int) (__t4->0 Int)
   (__t3->*->1->*->0 Int) (__t3->*->0 Int) (__t2->1->*->1->*->0 Int)
   (__t2->1->*->0 Int) (__t2->0 Int) (__t1->*->1->*->0 Int) (__t1->*->0 Int)
   (__t0 Int) (null?12 Bool) (null?11 Bool) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (= __t3->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t3->*->0 __t0 p!old->*->0 v x x!old null?4)
    (fold-62-__t3->*->1->*->0 CTXT0 __t3->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->*->0 null?5)
    (= __t4->0 v) (= __t4->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 __t4->0 x true) (= __t4->1->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t4->1->*->0 __t0 p!old->*->0 v x x!old
     null?6)
    (fold-62-__t3->*->1->*->0 CTXT0 __t4->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t4->1->*->0 null?7)
    (= __t5 0)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?8)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?9)
    (= p->*->0 __t4->0)
    (fold-14-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?10)
    (fold-14-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?11)
    (= v __t4->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t2->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (fold-14-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old p->*->0
     null?12))
   (insert_loop-p-out-p->*->1->*->0 CTXT0 NU x p->*->0 null?12))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t5 Int) (__t4->1->*->1->*->0 Int) (__t4->1->*->0 Int) (__t4->0 Int)
   (__t3->*->1->*->0 Int) (__t3->*->0 Int) (__t2->1->*->1->*->0 Int)
   (__t2->1->*->0 Int) (__t2->0 Int) (__t1->*->1->*->0 Int) (__t1->*->0 Int)
   (__t0 Int) (null?12 Bool) (null?11 Bool) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (= __t3->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t3->*->0 __t0 p!old->*->0 v x x!old null?4)
    (fold-62-__t3->*->1->*->0 CTXT0 __t3->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->*->0 null?5)
    (= __t4->0 v) (= __t4->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 __t4->0 x true) (= __t4->1->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t4->1->*->0 __t0 p!old->*->0 v x x!old
     null?6)
    (fold-62-__t3->*->1->*->0 CTXT0 __t4->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t4->1->*->0 null?7)
    (= __t5 0)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?8)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?9)
    (= p->*->0 __t4->0)
    (fold-14-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?10)
    (fold-14-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?11)
    (= v __t4->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t2->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (= NU p->*->0) (= NU __t4->0)
    (fold-14-p->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old null?12))
   (insert_loop-p-out-p->*->0 CTXT0 NU p!old->*->0 x null?12))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t5 Int) (__t4->1->*->1->*->0 Int) (__t4->1->*->0 Int) (__t4->0 Int)
   (__t3->*->1->*->0 Int) (__t3->*->0 Int) (__t2->1->*->1->*->0 Int)
   (__t2->1->*->0 Int) (__t2->0 Int) (__t1->*->1->*->0 Int) (__t1->*->0 Int)
   (__t0 Int) (null?11 Bool) (null?10 Bool) (null?9 Bool) (null?8 Bool)
   (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (= __t3->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t3->*->0 __t0 p!old->*->0 v x x!old null?4)
    (fold-62-__t3->*->1->*->0 CTXT0 __t3->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->*->0 null?5)
    (= __t4->0 v) (= __t4->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 __t4->0 x true) (= __t4->1->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t4->1->*->0 __t0 p!old->*->0 v x x!old
     null?6)
    (fold-62-__t3->*->1->*->0 CTXT0 __t4->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t4->1->*->0 null?7)
    (= __t5 0)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?8)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?9)
    (= p->*->0 __t4->0)
    (fold-14-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?10)
    (fold-14-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?11)
    (= v __t4->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t2->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true) (= NU x)
    (= NU __t2->0) (= NU x!old) (insert_loop-x-in-x CTXT0 NU true))
   (insert_loop-x-out-x CTXT0 NU x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (<ret> Int) (x!old Int) (x Int) (v Int)
   (p!old->*->0 Int) (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int)
   (nxt->*->0 Int) (__t5 Int) (__t4->1->*->1->*->0 Int) (__t4->1->*->0 Int)
   (__t4->0 Int) (__t3->*->1->*->0 Int) (__t3->*->0 Int)
   (__t2->1->*->1->*->0 Int) (__t2->1->*->0 Int) (__t2->0 Int)
   (__t1->*->1->*->0 Int) (__t1->*->0 Int) (__t0 Int) (null?11 Bool)
   (null?10 Bool) (null?9 Bool) (null?8 Bool) (null?7 Bool) (null?6 Bool)
   (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (= __t3->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t3->*->0 __t0 p!old->*->0 v x x!old null?4)
    (fold-62-__t3->*->1->*->0 CTXT0 __t3->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->*->0 null?5)
    (= __t4->0 v) (= __t4->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 __t4->0 x true) (= __t4->1->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t4->1->*->0 __t0 p!old->*->0 v x x!old
     null?6)
    (fold-62-__t3->*->1->*->0 CTXT0 __t4->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t4->1->*->0 null?7)
    (= __t5 0)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?8)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?9)
    (= p->*->0 __t4->0)
    (fold-14-p->*->0 CTXT0 p->*->0 __t0 p!old->*->0 v x x!old null?10)
    (fold-14-p->*->1->*->0 CTXT0 p->*->1->*->0 __t0 p!old->*->0 v x x!old
     p->*->0 null?11)
    (= v __t4->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t2->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true) (= <ret> 0)
    (= NU 0))
   (insert_loop-ret-RET CTXT0 NU x true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t4->1->*->1->*->0 Int) (__t4->1->*->0 Int) (__t4->0 Int)
   (__t3->*->1->*->0 Int) (__t3->*->0 Int) (__t2->1->*->1->*->0 Int)
   (__t2->1->*->0 Int) (__t2->0 Int) (__t1->*->1->*->0 Int) (__t1->*->0 Int)
   (__t0 Int) (null?12 Bool) (null?11 Bool) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (= __t3->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t3->*->0 __t0 p!old->*->0 v x x!old null?4)
    (fold-62-__t3->*->1->*->0 CTXT0 __t3->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->*->0 null?5)
    (= __t4->0 v) (= __t4->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 __t4->0 x true) (= __t4->1->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t4->1->*->0 __t0 p!old->*->0 v x x!old
     null?6)
    (fold-62-__t3->*->1->*->0 CTXT0 __t4->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t4->1->*->0 null?7)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?8)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?9)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?10)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?11)
    (= v __t4->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t2->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (fold-62-__t3->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old
     __t4->1->*->0 null?12))
   (fold-14-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old __t4->1->*->0
    null?12))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t4->1->*->1->*->0 Int) (__t4->1->*->0 Int) (__t4->0 Int)
   (__t3->*->1->*->0 Int) (__t3->*->0 Int) (__t2->1->*->1->*->0 Int)
   (__t2->1->*->0 Int) (__t2->0 Int) (__t1->*->1->*->0 Int) (__t1->*->0 Int)
   (__t0 Int) (null?12 Bool) (null?11 Bool) (null?10 Bool) (null?9 Bool)
   (null?8 Bool) (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (= __t3->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t3->*->0 __t0 p!old->*->0 v x x!old null?4)
    (fold-62-__t3->*->1->*->0 CTXT0 __t3->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->*->0 null?5)
    (= __t4->0 v) (= __t4->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 __t4->0 x true) (= __t4->1->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t4->1->*->0 __t0 p!old->*->0 v x x!old
     null?6)
    (fold-62-__t3->*->1->*->0 CTXT0 __t4->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t4->1->*->0 null?7)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?8)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?9)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?10)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?11)
    (= v __t4->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t2->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (= NU __t2->0)
    (fold-62-__t3->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old null?12))
   (fold-14-p->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old __t4->0
    null?12))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t4->1->*->1->*->0 Int) (__t4->1->*->0 Int) (__t4->0 Int)
   (__t3->*->1->*->0 Int) (__t3->*->0 Int) (__t2->1->*->1->*->0 Int)
   (__t2->1->*->0 Int) (__t2->0 Int) (__t1->*->1->*->0 Int) (__t1->*->0 Int)
   (__t0 Int) (null?11 Bool) (null?10 Bool) (null?9 Bool) (null?8 Bool)
   (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (= __t3->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t3->*->0 __t0 p!old->*->0 v x x!old null?4)
    (fold-62-__t3->*->1->*->0 CTXT0 __t3->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t3->*->0 null?5)
    (= __t4->0 v) (= __t4->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 __t4->0 x true) (= __t4->1->*->0 __t2->0)
    (fold-62-__t3->*->0 CTXT0 __t4->1->*->0 __t0 p!old->*->0 v x x!old
     null?6)
    (fold-62-__t3->*->1->*->0 CTXT0 __t4->1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t4->1->*->0 null?7)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?8)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?9)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?10)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?11)
    (= v __t4->0) (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true)
    (= x __t2->0) (= x x!old) (insert_loop-x-in-x CTXT0 x true) (= NU v)
    (= NU p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 NU x true))
   (fold-14-p->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t2->1->*->1->*->0 Int) (__t2->1->*->0 Int) (__t2->0 Int)
   (__t1->*->1->*->0 Int) (__t1->*->0 Int) (__t0 Int) (null?8 Bool)
   (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?4)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?5)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?7)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x __t2->0)
    (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (ifnull-64-__t1->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old
     __t2->1->*->0 null?8))
   (fold-62-__t3->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old
    __t2->1->*->0 null?8))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t2->1->*->1->*->0 Int) (__t2->1->*->0 Int) (__t2->0 Int)
   (__t1->*->1->*->0 Int) (__t1->*->0 Int) (__t0 Int) (null?8 Bool)
   (null?7 Bool) (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?4)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?5)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?7)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x __t2->0)
    (= x x!old) (insert_loop-x-in-x CTXT0 x true)
    (ifnull-64-__t1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old null?8))
   (fold-62-__t3->*->1->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old __t2->0
    null?8))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t2->1->*->1->*->0 Int) (__t2->1->*->0 Int) (__t2->0 Int)
   (__t1->*->1->*->0 Int) (__t1->*->0 Int) (__t0 Int) (null?7 Bool)
   (null?6 Bool) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (rel-<-out __t0 v x)
    (ifnull-64-__t1->*->0 CTXT0 __t1->*->0 __t0 p!old->*->0 v x x!old null?0)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t1->*->1->*->0 __t0 p!old->*->0 v x
     x!old __t1->*->0 null?1)
    (= __t2->0 x) (= __t2->0 x!old) (insert_loop-x-in-x CTXT0 __t2->0 true)
    (ifnull-64-__t1->*->0 CTXT0 __t2->1->*->0 __t0 p!old->*->0 v x x!old
     null?2)
    (ifnull-64-__t1->*->1->*->0 CTXT0 __t2->1->*->1->*->0 __t0 p!old->*->0 v
     x x!old __t2->1->*->0 null?3)
    (ifnull-18-nxt->*->0 CTXT0 nxt->*->0 __t0 p!old->*->0 v x x!old v null?4)
    (ifnull-18-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 __t0 p!old->*->0 v x
     x!old v nxt->*->0 null?5)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?6)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?7)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x __t2->0)
    (= x x!old) (insert_loop-x-in-x CTXT0 x true) (= NU x) (= NU x!old)
    (insert_loop-x-in-x CTXT0 NU true))
   (fold-62-__t3->*->0 CTXT0 NU __t0 p!old->*->0 v x x!old true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (= NU x) (= NU x!old)
    (insert_loop-x-in-x CTXT0 NU true))
   true)))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (x!old Int) (x Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 x v null?0)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 x nxt->*->0 null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 p->*->0 x null?2)
    (insert_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 x p->*->0 null?3)
    (= v p!old->*->0) (insert_loop-p-in-p->*->0 CTXT0 v x true) (= x x!old)
    (insert_loop-x-in-x CTXT0 x true) (= NU v) (= NU p!old->*->0)
    (insert_loop-p-in-p->*->0 CTXT0 NU x true))
   true)))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?0)
    (call-9-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?1)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0
     p->*->*->0 null?1)
    (scope-44-p!old->*->*->0 CTXT0 p!old->*->*->0 true) (= NU p!old->*->*->0)
    (scope-44-p!old->*->*->0 CTXT0 NU true))
   (join-12-p!old->*->*->0 CTXT0 NU true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?1)
    (scope-8-p!old->*->*->0 CTXT0 p!old->*->*->0 true) (= NU p!old->*->*->0)
    (scope-8-p!old->*->*->0 CTXT0 NU true))
   (join-12-p!old->*->*->0 CTXT0 NU true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?0)
    (call-9-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?1)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0
     p->*->*->0 null?1)
    (scope-44-p!old->*->*->0 CTXT0 p!old->*->*->0 true)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 NU p->*->*->0 null?2)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 NU p!old->*->*->0 p->*->*->0 null?2))
   (join-12-p->*->*->1->*->0 CTXT0 NU p!old->*->*->0 p->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?0)
    (call-9-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?1)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0
     p->*->*->0 null?1)
    (scope-44-p!old->*->*->0 CTXT0 p!old->*->*->0 true) (= NU p->*->*->0)
    (= NU p!old->*->*->0) (test_sorted-p-in-p->*->*->0 CTXT0 NU null?2)
    (call-9-hd-out-hd->*->0 CTXT0 NU p!old->*->*->0 null?2))
   (join-12-p->*->*->0 CTXT0 NU p!old->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?1)
    (scope-8-p!old->*->*->0 CTXT0 p!old->*->*->0 true)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 NU p->*->*->0 null?2))
   (join-12-p->*->*->1->*->0 CTXT0 NU p!old->*->*->0 p->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?1)
    (scope-8-p!old->*->*->0 CTXT0 p!old->*->*->0 true) (= NU p->*->*->0)
    (= NU p!old->*->*->0) (test_sorted-p-in-p->*->*->0 CTXT0 NU null?2))
   (join-12-p->*->*->0 CTXT0 NU p!old->*->*->0 null?2))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (hd->*->1->*->0 Int) (hd->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (call-9-hd-out-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0
     hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (call-9-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0
     p->*->*->0 null?3)
    (= NU p!old->*->*->0))
   (scope-44-p!old->*->*->0 CTXT0 NU null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (hd->*->1->*->0 Int) (hd->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (call-9-hd-out-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0
     hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (call-9-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0
     p->*->*->0 null?3)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 NU p->*->*->0 null?4)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 NU p!old->*->*->0 p->*->*->0 null?4))
   (test_sorted-p-out-p->*->*->1->*->0 CTXT0 NU p->*->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (hd->*->1->*->0 Int) (hd->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (call-9-hd-out-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0
     hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (call-9-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0
     p->*->*->0 null?3)
    (= NU p->*->*->0) (= NU p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 NU null?4)
    (call-9-hd-out-hd->*->0 CTXT0 NU p!old->*->*->0 null?4))
   (test_sorted-p-out-p->*->*->0 CTXT0 NU p!old->*->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (<ret> Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (call-9-hd-out-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0
     hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (call-9-hd-out-hd->*->0 CTXT0 p->*->*->0 p!old->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (call-9-hd-out-hd->*->1->*->0 CTXT0 p->*->*->1->*->0 p!old->*->*->0
     p->*->*->0 null?3)
    (= <ret> 0) (= NU 0))
   (test_sorted-ret-RET CTXT0 NU true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (hd->*->1->*->0 Int) (hd->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 NU hd->*->0 null?4))
   (test_sorted_loop-p-in-p->*->1->*->0 9 NU hd->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (hd->*->1->*->0 Int) (hd->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (= NU hd->*->0) (= NU p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 NU null?4))
   (test_sorted_loop-p-in-p->*->0 9 NU null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (hd->*->1->*->0 Int) (hd->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (> 0.02 0.) (> 0.02 0.) (> 0.02 0.) (> 0.02 0.) (> 0.04 0.) (> 0.04 0.)
    (test_sorted_loop-p-out-p->*->1->*->0 9 NU hd->*->0 null?4)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 NU hd->*->0 null?4))
   (call-9-hd-out-hd->*->1->*->0 CTXT0 NU p!old->*->*->0 hd->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (hd->*->1->*->0 Int) (hd->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (> 0.02 0.) (> 0.02 0.) (or (= 0.02 0.) (= 0.02 0.)) (> 0.04 0.)
    (> 0.04 0.) (test_sorted_loop-p-out-p->*->1->*->0 9 NU hd->*->0 null?4))
   (call-9-hd-out-hd->*->1->*->0 CTXT0 NU p!old->*->*->0 hd->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (hd->*->1->*->0 Int) (hd->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (or (= 0.02 0.) (= 0.02 0.)) (> 0.02 0.) (> 0.02 0.) (> 0.04 0.)
    (> 0.04 0.) (test_sorted-p-in-p->*->*->1->*->0 CTXT0 NU hd->*->0 null?4))
   (call-9-hd-out-hd->*->1->*->0 CTXT0 NU p!old->*->*->0 hd->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (hd->*->1->*->0 Int) (hd->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (or (= 0.04 0.) (= 0.04 0.)))
   (call-9-hd-out-hd->*->1->*->0 CTXT0 NU p!old->*->*->0 hd->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (= !pre hd->*->0) (= !pre hd->*->0) (= !pre p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 !pre null?4) (> 0.02 0.) (> 0.02 0.)
    (> 0.04 0.) (test_sorted_loop-p-out-p->*->0 9 NU !pre null?5)
    (= NU p!old->*->*->0) (test_sorted-p-in-p->*->*->0 CTXT0 NU null?5))
   (call-9-hd-out-hd->*->0 CTXT0 NU p!old->*->*->0 null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (= !pre hd->*->0) (= !pre hd->*->0) (= !pre p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 !pre null?4) (> 0.02 0.)
    (or (= 0.02 0.)) (> 0.04 0.)
    (test_sorted_loop-p-out-p->*->0 9 NU !pre null?5))
   (call-9-hd-out-hd->*->0 CTXT0 NU p!old->*->*->0 null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (= !pre hd->*->0) (= !pre hd->*->0) (= !pre p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 !pre null?4) (or (= 0.02 0.))
    (> 0.02 0.) (> 0.04 0.) (= NU p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 NU null?5))
   (call-9-hd-out-hd->*->0 CTXT0 NU p!old->*->*->0 null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= hd->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 hd->*->0 null?0)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 hd->*->1->*->0 hd->*->0 null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (= !pre hd->*->0) (= !pre hd->*->0) (= !pre p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 !pre null?4) (or (= 0.04 0.)))
   (call-9-hd-out-hd->*->0 CTXT0 NU p!old->*->*->0 null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (hd->*->1->*->0 Int) (hd->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (ifnull-12-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 null?0)
    (ifnull-12-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 hd->*->0
     null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (= NU p!old->*->*->0))
   (scope-8-p!old->*->*->0 CTXT0 NU null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (hd->*->1->*->0 Int) (hd->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (ifnull-12-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 null?0)
    (ifnull-12-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 hd->*->0
     null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 NU p->*->*->0 null?4))
   (test_sorted-p-out-p->*->*->1->*->0 CTXT0 NU p->*->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (p!old->*->*->0 Int) (p->*->*->1->*->0 Int)
   (p->*->*->0 Int) (hd->*->1->*->0 Int) (hd->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0) (ifnull-12-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 null?0)
    (ifnull-12-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 hd->*->0
     null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (= NU p->*->*->0) (= NU p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 NU null?4))
   (test_sorted-p-out-p->*->*->0 CTXT0 NU p!old->*->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (<ret> Int) (p!old->*->*->0 Int)
   (p->*->*->1->*->0 Int) (p->*->*->0 Int) (hd->*->1->*->0 Int)
   (hd->*->0 Int) (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool)
   (null?0 Bool))
  (=>
   (and (= __t0 0) (ifnull-12-hd->*->0 CTXT0 hd->*->0 p!old->*->*->0 null?0)
    (ifnull-12-hd->*->1->*->0 CTXT0 hd->*->1->*->0 p!old->*->*->0 hd->*->0
     null?1)
    (= p->*->*->0 p!old->*->*->0)
    (test_sorted-p-in-p->*->*->0 CTXT0 p->*->*->0 null?2)
    (test_sorted-p-in-p->*->*->1->*->0 CTXT0 p->*->*->1->*->0 p->*->*->0
     null?3)
    (= <ret> 0) (= NU 0))
   (test_sorted-ret-RET CTXT0 NU true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0)
    (shuf-6-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v p->*->0 null?0)
    (shuf-6-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v p->*->0
     nxt->*->0 null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (shuf-6-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (= NU p!old->*->0)
    (join-5-p!old->*->0 CTXT0 NU v null?4))
   (scope-39-p!old->*->0 CTXT0 NU null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0)
    (shuf-6-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v p->*->0 null?0)
    (shuf-6-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v p->*->0
     nxt->*->0 null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (shuf-6-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (= NU p->*->1->*->0)
    (shuf-6-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))
   (scope-39-p->*->1->*->0 CTXT0 NU p!old->*->0 p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0)
    (shuf-6-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v p->*->0 null?0)
    (shuf-6-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v p->*->0
     nxt->*->0 null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (shuf-6-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (= NU p->*->0)
    (join-5-p->*->0 CTXT0 NU p!old->*->0 v null?4))
   (scope-39-p->*->0 CTXT0 NU p!old->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0)
    (shuf-6-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v p->*->0 null?0)
    (shuf-6-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v p->*->0
     nxt->*->0 null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (shuf-6-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true)
    (shuf-6-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))
   (test_sorted_loop-p-out-p->*->1->*->0 CTXT0 NU p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0)
    (shuf-6-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v p->*->0 null?0)
    (shuf-6-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v p->*->0
     nxt->*->0 null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (shuf-6-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (= NU p->*->0)
    (join-5-p->*->0 CTXT0 NU p!old->*->0 v null?4))
   (test_sorted_loop-p-out-p->*->0 CTXT0 NU p!old->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (<ret> Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (__t0 Int) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= __t0 0)
    (shuf-6-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v p->*->0 null?0)
    (shuf-6-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v p->*->0
     nxt->*->0 null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (shuf-6-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (= <ret> 0) (= NU 0))
   (test_sorted_loop-ret-RET CTXT0 NU true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (> 0. 0.) (> 0. 0.) (> 0.04 0.)
    (> 0.02 0.) (> 0.02 0.) (> 0. 0.)
    (join-5-p->*->1->*->0 CTXT0 NU p!old->*->0 v nxt->*->0 null?4)
    (join-5-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v v nxt->*->0 null?4))
   (shuf-6-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (> 0. 0.) (> 0. 0.)
    (or (= 0.02 0.) (= 0.04 0.)) (> 0.02 0.) (> 0. 0.)
    (join-5-p->*->1->*->0 CTXT0 NU p!old->*->0 v nxt->*->0 null?4))
   (shuf-6-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (or (= 0. 0.) (= 0. 0.)) (> 0.04 0.)
    (> 0.02 0.) (> 0.02 0.) (> 0. 0.)
    (join-5-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v v nxt->*->0 null?4))
   (shuf-6-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (or (= 0. 0.) (= 0.02 0.)))
   (shuf-6-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (> 0. 0.) (> 0.04 0.) (> 0.02 0.)
    (join-5-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4)
    (join-5-nxt->*->0 CTXT0 NU p!old->*->0 v v null?4))
   (shuf-6-nxt->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (> 0. 0.) (or (= 0.04 0.))
    (> 0.02 0.) (join-5-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))
   (shuf-6-nxt->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (or (= 0. 0.)) (> 0.04 0.)
    (> 0.02 0.) (join-5-nxt->*->0 CTXT0 NU p!old->*->0 v v null?4))
   (shuf-6-nxt->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (or (= 0.02 0.)))
   (shuf-6-nxt->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (> 0. 0.) (> 0. 0.) (> 0.04 0.)
    (> 0.02 0.) (> 0.02 0.) (> 0.02 0.)
    (join-5-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->1->*->0 null?4)
    (join-5-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v v p->*->1->*->0 null?4))
   (shuf-6-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->1->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (> 0. 0.) (> 0. 0.)
    (or (= 0.02 0.) (= 0.04 0.)) (> 0.02 0.) (> 0.02 0.)
    (join-5-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->1->*->0 null?4))
   (shuf-6-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->1->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (or (= 0. 0.) (= 0. 0.)) (> 0.04 0.)
    (> 0.02 0.) (> 0.02 0.) (> 0.02 0.)
    (join-5-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v v p->*->1->*->0 null?4))
   (shuf-6-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->1->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (or (= 0.02 0.) (= 0.02 0.)))
   (shuf-6-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->1->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (> 0. 0.) (> 0.04 0.) (> 0.02 0.)
    (join-5-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4)
    (join-5-nxt->*->0 CTXT0 NU p!old->*->0 v v null?4))
   (shuf-6-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (> 0. 0.) (or (= 0.04 0.))
    (> 0.02 0.) (join-5-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))
   (shuf-6-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (or (= 0. 0.)) (> 0.04 0.)
    (> 0.02 0.) (join-5-nxt->*->0 CTXT0 NU p!old->*->0 v v null?4))
   (shuf-6-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (join-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (join-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (join-5-p->*->0 CTXT0 p->*->0 p!old->*->0 v null?2)
    (join-5-p->*->1->*->0 CTXT0 p->*->1->*->0 p!old->*->0 v p->*->0 null?3)
    (join-5-p!old->*->0 CTXT0 p!old->*->0 v true)
    (join-5-v CTXT0 v p!old->*->0 true) (or (= 0.02 0.)))
   (shuf-6-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-3-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (scope-3-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (scope-3-v CTXT0 v p!old->*->0 true) (= NU v)
    (scope-3-v CTXT0 NU p!old->*->0 true))
   (join-5-v CTXT0 NU p!old->*->0 true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (ifnull-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true) (= NU v)
    (= NU p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 NU true))
   (join-5-v CTXT0 NU p!old->*->0 true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-3-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (scope-3-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (scope-3-v CTXT0 v p!old->*->0 true) (= NU p!old->*->0))
   (join-5-p!old->*->0 CTXT0 NU v true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?3 Bool)
   (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (ifnull-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (= NU p!old->*->0))
   (join-5-p!old->*->0 CTXT0 NU v true))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-3-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (scope-3-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (scope-3-v CTXT0 v p!old->*->0 true)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 NU p->*->0 null?4))
   (join-5-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-3-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (scope-3-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (scope-3-v CTXT0 v p!old->*->0 true) (= NU p->*->0) (= NU v)
    (= NU p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 NU null?4))
   (join-5-p->*->0 CTXT0 NU p!old->*->0 v null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (ifnull-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 NU p->*->0 null?4))
   (join-5-p->*->1->*->0 CTXT0 NU p!old->*->0 v p->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (ifnull-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (= NU p->*->0) (= NU v) (= NU p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 NU null?4))
   (join-5-p->*->0 CTXT0 NU p!old->*->0 v null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-3-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (scope-3-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (scope-3-v CTXT0 v p!old->*->0 true)
    (scope-3-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v v nxt->*->0 null?4))
   (join-5-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v v nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (scope-3-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (scope-3-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (scope-3-v CTXT0 v p!old->*->0 true) (= NU nxt->*->0)
    (scope-3-nxt->*->0 CTXT0 NU p!old->*->0 v v null?4))
   (join-5-nxt->*->0 CTXT0 NU p!old->*->0 v v null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (ifnull-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (ifnull-5-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v v nxt->*->0 null?4))
   (join-5-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v v nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (null?4 Bool)
   (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (ifnull-5-nxt->*->0 CTXT0 nxt->*->0 p!old->*->0 v v null?0)
    (ifnull-5-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 p!old->*->0 v v nxt->*->0
     null?1)
    (= p->*->0 v) (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (= NU nxt->*->0) (ifnull-5-nxt->*->0 CTXT0 NU p!old->*->0 v v null?4))
   (join-5-nxt->*->0 CTXT0 NU p!old->*->0 v v null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (test_sorted_loop-ret-RET 2 __t0 true)
    (call-2-nxt-out-nxt->*->0 CTXT0 nxt->*->0 nxt_v p!old->*->0 v v null?0)
    (call-2-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt_v p!old->*->0 v
     v nxt->*->0 null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true) (= NU v)
    (= NU p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 NU null?4))
   (scope-3-v CTXT0 NU p!old->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (test_sorted_loop-ret-RET 2 __t0 true)
    (call-2-nxt-out-nxt->*->0 CTXT0 nxt->*->0 nxt_v p!old->*->0 v v null?0)
    (call-2-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt_v p!old->*->0 v
     v nxt->*->0 null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (= NU nxt->*->1->*->0)
    (call-2-nxt-out-nxt->*->1->*->0 CTXT0 NU nxt_v p!old->*->0 v v nxt->*->0
     null?4))
   (scope-3-nxt->*->1->*->0 CTXT0 NU p!old->*->0 v v nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int) (__t0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (test_sorted_loop-ret-RET 2 __t0 true)
    (call-2-nxt-out-nxt->*->0 CTXT0 nxt->*->0 nxt_v p!old->*->0 v v null?0)
    (call-2-nxt-out-nxt->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt_v p!old->*->0 v
     v nxt->*->0 null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (= NU nxt->*->0)
    (call-2-nxt-out-nxt->*->0 CTXT0 NU nxt_v p!old->*->0 v v null?4))
   (scope-3-nxt->*->0 CTXT0 NU p!old->*->0 v v null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= nxt->*->0 nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 v null?0)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt->*->0
     null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 NU nxt->*->0 null?4))
   (test_sorted_loop-p-in-p->*->1->*->0 2 NU nxt->*->0 null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= nxt->*->0 nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 v null?0)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt->*->0
     null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (= NU nxt->*->0) (= NU nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 NU v null?4))
   (test_sorted_loop-p-in-p->*->0 2 NU null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= nxt->*->0 nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 v null?0)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt->*->0
     null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (> 0.02 0.) (> 0.02 0.) (> 0.02 0.) (> 0. 0.) (> 0.04 0.) (> 0.02 0.)
    (test_sorted_loop-p-out-p->*->1->*->0 2 NU nxt->*->0 null?4)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 NU nxt->*->0 null?4))
   (call-2-nxt-out-nxt->*->1->*->0 CTXT0 NU nxt_v p!old->*->0 v v nxt->*->0
    null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= nxt->*->0 nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 v null?0)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt->*->0
     null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (> 0.02 0.) (> 0.02 0.) (or (= 0. 0.) (= 0.02 0.)) (> 0.04 0.)
    (> 0.02 0.) (test_sorted_loop-p-out-p->*->1->*->0 2 NU nxt->*->0 null?4))
   (call-2-nxt-out-nxt->*->1->*->0 CTXT0 NU nxt_v p!old->*->0 v v nxt->*->0
    null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= nxt->*->0 nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 v null?0)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt->*->0
     null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (or (= 0.02 0.) (= 0.02 0.)) (> 0.02 0.) (> 0. 0.) (> 0.04 0.)
    (> 0.02 0.)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 NU nxt->*->0 null?4))
   (call-2-nxt-out-nxt->*->1->*->0 CTXT0 NU nxt_v p!old->*->0 v v nxt->*->0
    null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= nxt->*->0 nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 v null?0)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt->*->0
     null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (or (= 0.02 0.) (= 0.04 0.)))
   (call-2-nxt-out-nxt->*->1->*->0 CTXT0 NU nxt_v p!old->*->0 v v nxt->*->0
    null?4))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int)
   (nxt->*->0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= nxt->*->0 nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 v null?0)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt->*->0
     null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (= !pre nxt->*->0) (= !pre nxt->*->0) (= !pre nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 !pre v null?4) (> 0.02 0.)
    (> 0.02 0.) (> 0.04 0.) (test_sorted_loop-p-out-p->*->0 2 NU !pre null?5)
    (= NU nxt_v) (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 NU v null?5))
   (call-2-nxt-out-nxt->*->0 CTXT0 NU nxt_v p!old->*->0 v v null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int)
   (nxt->*->0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= nxt->*->0 nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 v null?0)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt->*->0
     null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (= !pre nxt->*->0) (= !pre nxt->*->0) (= !pre nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 !pre v null?4) (> 0.02 0.)
    (or (= 0.02 0.)) (> 0.04 0.)
    (test_sorted_loop-p-out-p->*->0 2 NU !pre null?5))
   (call-2-nxt-out-nxt->*->0 CTXT0 NU nxt_v p!old->*->0 v v null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int)
   (nxt->*->0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= nxt->*->0 nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 v null?0)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt->*->0
     null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (= !pre nxt->*->0) (= !pre nxt->*->0) (= !pre nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 !pre v null?4)
    (or (= 0.02 0.)) (> 0.02 0.) (> 0.04 0.) (= NU nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 NU v null?5))
   (call-2-nxt-out-nxt->*->0 CTXT0 NU nxt_v p!old->*->0 v v null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (!pre Int) (v Int) (p!old->*->0 Int)
   (p->*->1->*->0 Int) (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int)
   (nxt->*->0 Int) (null?5 Bool) (null?4 Bool) (null?3 Bool) (null?2 Bool)
   (null?1 Bool) (null?0 Bool))
  (=>
   (and (= nxt->*->0 nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 v null?0)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt->*->0
     null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true)
    (= !pre nxt->*->0) (= !pre nxt->*->0) (= !pre nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 !pre v null?4)
    (or (= 0.04 0.)))
   (call-2-nxt-out-nxt->*->0 CTXT0 NU nxt_v p!old->*->0 v v null?5))))
(assert
 (forall
  ((NU Int) (CTXT0 Int) (v Int) (p!old->*->0 Int) (p->*->1->*->0 Int)
   (p->*->0 Int) (nxt_v Int) (nxt->*->1->*->0 Int) (nxt->*->0 Int)
   (null?4 Bool) (null?3 Bool) (null?2 Bool) (null?1 Bool) (null?0 Bool))
  (=>
   (and (= nxt->*->0 nxt_v)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->0 v null?0)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt->*->1->*->0 nxt->*->0
     null?1)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 nxt_v v true) (= p->*->0 v)
    (= p->*->0 p!old->*->0)
    (test_sorted_loop-p-in-p->*->0 CTXT0 p->*->0 null?2)
    (test_sorted_loop-p-in-p->*->1->*->0 CTXT0 p->*->1->*->0 p->*->0 null?3)
    (= v p!old->*->0) (test_sorted_loop-p-in-p->*->0 CTXT0 v true))
   (<= v nxt_v))))

(check-sat-using (then propagate-values qe-light horn))
