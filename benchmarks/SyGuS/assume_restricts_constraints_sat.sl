; SyGuS-IF 2.1: the constraints need hold only where the assumptions hold.
; f x = x satisfies (> (f x) 0) for x > 0, and f 0 = -1 does not contradict
; it because x = 0 is outside the assumption.  set-info, set-option and
; set-feature carry no meaning for the problem.
(set-logic LIA)
(set-info :source |a reproducer|)
(set-option :produce-models true)
(set-feature :fwd-decls true)
(synth-fun f ((z Int)) Int)
(declare-var x Int)
(constraint (> (f x) 0))
(assume (> x 0))
(constraint (=> (= x 1) (= (f 0) (- 1))))
(check-synth)
