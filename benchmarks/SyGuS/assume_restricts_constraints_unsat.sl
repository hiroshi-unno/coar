; Inside the assumption x > 0 the constraint x > 5 still fails at x = 1:
; infeasible.  Control for the _sat twin: an assumption weakens the
; constraints only outside its own region.
(set-logic LIA)
(synth-fun f ((z Int)) Int)
(declare-var x Int)
(assume (> x 0))
(constraint (= (f x) 0))
(constraint (> x 5))
(check-synth)
