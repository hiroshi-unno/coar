(set-logic RE)

(synth-fun r () (RegEx String))
(synth-fun r1 () (RegEx String))
(synth-fun r2 () (RegEx String))

(constraint (= (re.union r (re.comp (re.++ (str.to.re "O") r))) re.all))
(constraint (= (re.union r1 (re.comp (str.to.re "O"))) re.all))
(constraint (= (re.union r2 (re.comp (re.union r1 r2))) re.all))

(check-synth)
