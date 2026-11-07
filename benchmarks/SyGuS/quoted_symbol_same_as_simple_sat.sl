; SMT-LIB: |f| and f are one symbol, as are |x| and x.  f = identity.
(set-logic LIA)
(synth-fun |f| ((z Int)) Int)
(declare-var |x| Int)
(constraint (= (f x) |x|))
(constraint (= (|f| 3) 3))
(check-synth)
