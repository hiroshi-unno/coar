(set-logic RE)

(synth-fun r () (RegEx String))
(synth-fun r1 () (RegEx String))
(synth-fun r2 () (RegEx String))

(constraint (= (re.union r (re.comp (re.++ (str.to.re "x") (str.to.re "y") r))) re.all))
(constraint (= (re.union r1 (re.comp (re.++ (str.to.re "x") (str.to.re "y")))) re.all))
(constraint (= (re.union r2 (re.comp (re.union r1 r2))) re.all))

(check-synth)
