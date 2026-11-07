; The invariant x >= 0 exists.  The unused declaration uses a name of the
; form the invariant expansion generates for its own variables, which must
; not collide with it.
(set-logic LIA)
(synth-inv inv ((x Int)))
(define-fun pre ((x Int)) Bool (= x 0))
(define-fun trans ((x Int) (xp Int)) Bool (= xp (+ x 1)))
(define-fun post ((x Int)) Bool (>= x 0))
(declare-var INV_1 Int)
(declare-var INV_2 Int)
(inv-constraint inv pre trans post)
(check-synth)
