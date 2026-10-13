(set-logic DQHORN)

(declare-forall-fun Q1 (Int) Bool)
(declare-forall-fun Q2 (Int) Bool)
(declare-forall-fun I1 (Int Int Int) Bool)
(declare-forall-fun I2 (Int Int Int) Bool)

(define-fun F1 ((x1 Int) (x2 Int) (i1 Int)) Bool (Q1 i1))
(define-fun F2 ((x1 Int) (x2 Int) (i2 Int)) Bool (Q2 i2))
(declare-fun Y1 (Int Int) Bool)
(declare-fun Y2 (Int Int) Bool)
;(define-fun Y1 ((i1 Int) (y1 Int)) Bool (= i1 y1))
;(define-fun Y2 ((i2 Int) (y2 Int)) Bool (= i2 y2))

(assert (forall ((x1 Int) (x2 Int) (i1 Int) (i2 Int))
    (=>
        (and
            (= (I1 x1 x2 i1) (F1 x1 x2 i1))
            (= (I2 x1 x2 i2) (F2 x1 x2 i2))
            (I1 x1 x2 i1)
            (I2 x1 x2 i2)
        )
        (exists ((y1 Int) (y2 Int))
            (and
                (Y1 i1 y1)
                (Y2 i2 y2)
            )
        )
    )
))

(assert (forall ((x1 Int) (x2 Int) (i1 Int) (y1 Int) (i2 Int) (y2 Int))
    (=>
        (and
            (= (I1 x1 x2 i1) (F1 x1 x2 i1))
            (= (I2 x1 x2 i2) (F2 x1 x2 i2))
            (I1 x1 x2 i1)
            (I2 x1 x2 i2)
            (Y1 i1 y1)
            (Y2 i2 y2)
        )
        (and
            (Q1 y1)
            (Q2 y2)
        )
    )
))
