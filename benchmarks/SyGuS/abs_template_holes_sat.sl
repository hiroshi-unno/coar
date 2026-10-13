; expected: sat
;
; A function synthesis whose solution needs a case split, so the template the
; synthesizer grows to has condition holes: f x := ite (x >= 0) x (-x).  The
; constraint generator once bound the holes of an applied function variable
; twice (once for the application, once more as if the function were a nullary
; unknown) and stopped with an uncaught exception instead of an answer.
(set-logic LIA)
(synth-fun f ((x Int)) Int)
(declare-var x Int)
(constraint (>= (f x) x))
(constraint (>= (f x) (- x)))
(constraint (or (= (f x) x) (= (f x) (- x))))
(check-synth)
