; expected: sat; currently (Box Int) and (Box int) collide in the datatype environment, which
; keys instances by their printed names.
; This requires distinct identities for actual datatype instances too.
(set-logic ALL)
(declare-sort int 0)
(declare-datatypes ((Box 1)) ((par (T) ((mkBox (value T))))))
(declare-const a (Box Int))
(declare-const b (Box int))
(declare-const u int)
(assert (= (value a) 0))
(assert (= b (mkBox u)))
(check-sat)
