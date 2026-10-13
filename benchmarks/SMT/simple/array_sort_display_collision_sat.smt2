; expected: sat; formerly CoAR returned unsat, identifying sorts by their printed names.
; (S Int) and (S int) are independent uninterpreted sort instances.
; The latter occurs inside an array; its distinct identity must survive.
(set-logic ALL)
(declare-sort S 1)
(declare-sort int 0)
(declare-const c (Array Bool (S int)))
(declare-const d (Array Bool (S int)))
(assert (forall ((x (S Int)) (y (S Int))) (= x y)))
(assert (distinct c d))
(check-sat)
