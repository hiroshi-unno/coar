; Sixteen nested let-bindings, each doubling the previous one, so t16 = 65536*x.
; The whole assertion is 2^16 * x > 0, satisfiable by any positive x.
;
; This file exists to measure whether the tool keeps the sharing that `let` expresses.
; Written out in full the term has 65,536 leaves; kept shared it has 16 bindings of two
; variables each.  As of 2026-09-08 the tool expands it: the SMT-LIB frontend builds
; let-nodes and keeps them, but the pass that runs immediately afterwards drops any let
; whose definition mentions a variable it considers unknown, and on this path a
; `declare-fun` constant counts as unknown -- so t1's definition mentions x and is
; substituted, which makes t2's definition mention x, and so on down the chain.  Printing
; the parsed problem therefore yields about 328 KB from a 0.4 KB input.
;
; Compare with the forall-bound file beside this one, which is the same term over a
; quantified variable and stays small.  For scale, Z3 reads a depth-25 version of this in
; 0.03 s: its terms are hash-consed graphs, so it never materialises the copies.
(declare-fun x () Int)
(assert (> (let ((t1 (+ x x))) (let ((t2 (+ t1 t1))) (let ((t3 (+ t2 t2))) (let ((t4 (+ t3 t3))) (let ((t5 (+ t4 t4))) (let ((t6 (+ t5 t5))) (let ((t7 (+ t6 t6))) (let ((t8 (+ t7 t7))) (let ((t9 (+ t8 t8))) (let ((t10 (+ t9 t9))) (let ((t11 (+ t10 t10))) (let ((t12 (+ t11 t11))) (let ((t13 (+ t12 t12))) (let ((t14 (+ t13 t13))) (let ((t15 (+ t14 t14))) (let ((t16 (+ t15 t15))) t16)))))))))))))))) 0))
(check-sat)
