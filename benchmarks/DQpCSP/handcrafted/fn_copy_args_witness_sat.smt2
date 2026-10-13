; A universal in a clause body over an unknown, which the reader skolemises into a functional
; witness predicate taking every variable of the clause: here x and y, and the premise y = x makes
; y a copy of x at the witness's only occurrence.  p := (x >= 0) is a solution: the body
; universal "p z => p (z + x)" holds exactly when x >= 0, and then x + y = 2x >= 0.  The witness
; z := 0 refutes the body universal whenever x < 0.  expected: sat
(set-logic HORN)
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (=> (>= x 0) (p x))))
(assert (forall ((x Int)) (=> (p x) (>= x 0))))
(assert (forall ((x Int) (y Int))
  (=> (and (= y x) (forall ((z Int)) (=> (p z) (p (+ z x))))) (>= (+ x y) 0))))
(check-sat)
