(set-logic HORN)

(declare-sort X 0)
(declare-sort a48 0)
(declare-sort a50 0)
(declare-sort a51 0)
(declare-sort a52 0)
(declare-sort a53 0)
(declare-datatypes (T) ((List nil (cons (hd T) (tl (List))))))

(declare-fun find ((a48) (List X) (a50) (a51) (a52) (a53)) Bool)

(assert (forall ( (p a48) (l (List X)) (ok a50) (exc a51) (var128 a52) (_v36 a53) )
    (=>
        (and
            ((_ is nil) l)
        )
        (find p l ok exc var128 _v36)
    )
))

(assert (forall ( (p a48) (l (List X)) (var13 (List X)) (ok a50) (exc a51) (var127 a52) (_v65 a53) (_v62 X) )
    (=>
        (and
            (not ((_ is nil) l))
            ((_ is cons) l)
            (= var13 (tl l))
            (= _v62 (hd l))
        )
        (find p l ok exc var127 _v65)
    )
))

(assert (forall ( (p a48) (l (List X)) (ok a50) (exc a51) (var125 a52) (_v132 a53) (_v108 a48) (_v114 (List X)) (_v117 a50) (_v123 a51) (_v129 a52) (var12 X) )
    (=>
        (and
            (find _v108 _v114 _v117 _v123 _v129 _v132)
            (not ((_ is nil) l))
            ((_ is cons) l)
            (= var12 (hd l))
            (= _v114 (tl l))
        )
        (find p l ok exc var125 _v132)
    )
))



(check-sat)
(exit)