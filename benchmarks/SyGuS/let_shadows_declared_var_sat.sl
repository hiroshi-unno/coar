; expected: sat
;
; The `let` binding is the nearer one, so the body's `x` is 0 and the constraint
; holds; `f z := 0` synthesises and cvc5 returns a definition.
;
; It answered unsat. A `let` with more than one binding puts its definitions in
; one environment while a `declare-var` lives in another, and the lookup for an
; atom consulted the declared one first -- so the outer `x` won over the inner
; binding and the constraint read as `x = 0`, required of every integer.
(set-logic LIA)
(synth-fun f ((z Int)) Int)
(constraint (= (f 0) 0))
(declare-var x Int)
(constraint (= (let ((x 0)) x) 0))
(check-synth)
