(set-logic ALL)
(define-fun-rec s ((x Int)) (Seq Int) (seq.++ (seq.unit 0) (s x)))
(assert true)
(check-sat)
