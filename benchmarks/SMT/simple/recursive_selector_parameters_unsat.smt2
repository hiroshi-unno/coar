; Legal non-uniform recursion: three Bool selector results cannot be distinct. CoAR refuses this unsupported instance
; (it once read next : Tree(T) -> Tree(Bool) as Tree(T) -> Tree(T) and answered sat).
(declare-datatypes ((Tree 1)) ((par (T) ((leaf (value T)) (node (next (Tree Bool)))))))
(declare-const x0 (Tree Int))
(declare-const x1 (Tree Int))
(declare-const x2 (Tree Int))
(assert (distinct (value (next x0)) (value (next x1)) (value (next x2))))
(check-sat)
