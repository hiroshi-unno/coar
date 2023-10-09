(set-logic SYGUS)

(declare-fun r () (RegEx String))
(declare-fun r1 () (RegEx String))
(declare-fun r2 () (RegEx String))

(assert (= (re.union r (re.comp (re.++ (str.to.re "O") r))) re.all))
(assert (= (re.union r1 (re.comp (str.to.re "O"))) re.all))
(assert (= (re.union r2 (re.comp (re.union r1 r2))) re.all))

(check-sat)
