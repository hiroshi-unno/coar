; y and b never change, so preprocessing may solve a copy of inv without them;
; the answer must still define inv alone, over its own three parameters.
(set-logic LIA)
(synth-inv inv ((y Int) (b Bool) (x Int)))
(define-fun pre ((y Int) (b Bool) (x Int)) Bool (and (= x 0) (= y 10) b))
(define-fun trans ((y Int) (b Bool) (x Int) (y! Int) (b! Bool) (x! Int)) Bool (and (< x 10) (= x! (+ x 1)) (= y! y) (= b! b)))
(define-fun post ((y Int) (b Bool) (x Int)) Bool (and (= y 10) (<= x 10) b))
(inv-constraint inv pre trans post)
(check-synth)
