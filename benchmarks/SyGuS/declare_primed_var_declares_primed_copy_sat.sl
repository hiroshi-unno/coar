; SyGuS-IF 1.0: declare-primed-var declares x and x!.  f = identity works.
(set-logic LIA)
(synth-fun f ((z Int)) Int)
(declare-primed-var x Int)
(constraint (= (f x!) x!))
(constraint (= (f x) x))
(check-synth)
