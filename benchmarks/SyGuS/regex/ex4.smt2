(set-logic SYGUS)

(declare-fun r () (RegEx String))

(assert (= r (str.to.re "a")))

(check-sat)
