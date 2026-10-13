; Z3 5.1.0 answers `unsat` to this SATISFIABLE (indeed valid, ground) formula (found 2026-10-13
; while repairing a wrong `unsat` of this tool's unfolding refuter).  `cnt x t a` counts the i < t with a[i] = x; with
; a = (lambda i. ite (i = 2) 15922 0) and t = 3 the cells 0 and 1 hold 0, so cnt 0 3 a = 2.
; The same with the array written (store ((as const (Array Int Int)) 0) 2 15922) is answered
; `sat`, and Z3 4.15.4 answers this file `sat`.  No workaround in the tree: whether a lambda
; reaches a recursive function's argument in a question the tool asks is not established (a
; model's array values are read back as lambdas).
(set-logic ALL)
(define-fun-rec cnt ((x Int) (t Int) (a (Array Int Int))) Int
  (ite (<= t 0) 0 (+ (cnt x (- t 1) a) (ite (= (select a (- t 1)) x) 1 0))))
(assert (>= (cnt 0 3 (lambda ((i Int)) (ite (= i 2) 15922 0))) 2))
(check-sat)
