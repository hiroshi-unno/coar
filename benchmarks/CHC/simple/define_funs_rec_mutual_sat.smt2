; define-funs-rec with genuine mutual recursion (SMT path, z3_smt.json -p smt).  The reader once
; refused define-funs-rec, and once it parsed the run never ended (the evaluator unfolded both
; branches of the ite in each body).  Expected: sat (ev 4 holds, od k for k = 3).
(set-logic ALL)
(define-funs-rec ((ev ((n Int)) Bool) (od ((n Int)) Bool))
  ((ite (<= n 0) (= n 0) (od (- n 1)))
   (ite (<= n 0) false (ev (- n 1)))))
(declare-const k Int)
(assert (and (ev 4) (od k) (> k 2) (< k 5)))
(check-sat)
