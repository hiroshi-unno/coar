(set-logic SYGUS)

(declare-fun r () (RegEx String))
(declare-fun r1 () (RegEx String))
(declare-fun r2 () (RegEx String))

(assert (= (re.union r (re.comp (re.++ (str.to.re "a") r))) re.all))
(assert (= (re.union r1 (re.comp (str.to.re "a"))) re.all))
(assert (= (re.union r2 (re.comp (re.union r1 r2))) re.all))
;(assert (= r (re.++ (str.to.re "a") r)))
;(assert (= r1 (str.to.re "a")))
;(assert (= r2 (re.union r1 r2)))

(check-sat)
