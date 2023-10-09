(declare-const x String)
(assert (str.in.re x (re.++ (str.to.re "hello") re.all (str.to.re "world"))))
(check-sat)
(get-model)
