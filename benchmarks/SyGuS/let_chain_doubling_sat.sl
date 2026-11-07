;; A chain of 40 lets, each using the previous name twice: the trans relation is x' = x + a40 with a1 = x - x = 0
;; and a(k+1) = ak + ak, so x' = x, and with x = 0 initially the invariant x = 0 proves x = 0: realizable.
;; Substituting each definition into its uses gives a term of about 2^40 nodes; a reader that keeps the
;; bindings reads it at the size of the file.
(set-logic LIA)
(synth-inv inv ((x Int)))
(define-fun pre ((x Int)) Bool (= x 0))
(define-fun trans ((x Int) (x! Int)) Bool
  (let ((a0 x)) (let ((a1 (- a0 a0))) (let ((a2 (+ a1 a1))) (let ((a3 (+ a2 a2))) (let ((a4 (+ a3 a3))) (let ((a5 (+ a4 a4))) (let ((a6 (+ a5 a5))) (let ((a7 (+ a6 a6))) (let ((a8 (+ a7 a7))) (let ((a9 (+ a8 a8))) (let ((a10 (+ a9 a9))) (let ((a11 (+ a10 a10))) (let ((a12 (+ a11 a11))) (let ((a13 (+ a12 a12))) (let ((a14 (+ a13 a13))) (let ((a15 (+ a14 a14))) (let ((a16 (+ a15 a15))) (let ((a17 (+ a16 a16))) (let ((a18 (+ a17 a17))) (let ((a19 (+ a18 a18))) (let ((a20 (+ a19 a19))) (let ((a21 (+ a20 a20))) (let ((a22 (+ a21 a21))) (let ((a23 (+ a22 a22))) (let ((a24 (+ a23 a23))) (let ((a25 (+ a24 a24))) (let ((a26 (+ a25 a25))) (let ((a27 (+ a26 a26))) (let ((a28 (+ a27 a27))) (let ((a29 (+ a28 a28))) (let ((a30 (+ a29 a29))) (let ((a31 (+ a30 a30))) (let ((a32 (+ a31 a31))) (let ((a33 (+ a32 a32))) (let ((a34 (+ a33 a33))) (let ((a35 (+ a34 a34))) (let ((a36 (+ a35 a35))) (let ((a37 (+ a36 a36))) (let ((a38 (+ a37 a37))) (let ((a39 (+ a38 a38))) (let ((a40 (+ a39 a39))) (= x! (+ x a40))))))))))))))))))))))))))))))))))))))))))))
(define-fun post ((x Int)) Bool (= x 0))
(inv-constraint inv pre trans post)
(check-synth)
