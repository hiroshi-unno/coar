; SMT-LIB 2.6 match (section 3.6.1): the FIRST case whose pattern matches
; applies.  P holds of the one-element list (cons 1 nil); the goal demands that
; a cons in P have a negative head and an empty tail (first case), and accepts
; nil by the catch-all second case, which a cons never reaches, so the problem
; is unsatisfiable.  A reading that let the catch-all apply to a
; cons, or that tried the cases in the other order, answers sat.  The recursive
; length is defined by match too.
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(define-fun-rec len ((l Lst)) Int
  (match l ((nil 0) ((cons h t) (+ 1 (len t))))))
(declare-fun P (Lst) Bool)
(assert (P (cons 1 nil)))
(assert (forall ((l Lst))
  (=> (P l)
      (match l (((cons h t) (and (< h 0) (= (len t) 0)))
                (y true))))))
(check-sat)
