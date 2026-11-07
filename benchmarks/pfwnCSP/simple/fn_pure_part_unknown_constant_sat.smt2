; Satisfiable.  A functional predicate P whose only clause has a pure part mentioning another
; unknown, the integer constant c to be synthesized:
;   P(x, y) => c = 0
; A solution: c := 0 and P(x, y) := (y = 0), total and single-valued.  So the verdict is sat.
;
; What the file is for: eliminating P before the CEGIS loop by deciding
; forall x. exists y. c = 0 is licensed only when that formula is the meaning of P's clauses,
; which it is not while c is an unknown (it is then quantified by nothing).  The elimination
; must keep such a predicate for the loop.  It once took it, and the game's solver met the free
; variable c and stopped the solve with an uncaught exception; with preprocessing on, the
; preprocessor handles P first, so the shape is reached with preprocessing off.
(set-logic HORN)
(declare-fun c () Int)
(declare-fnp P (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (P x y) (= c 0))))
(check-sat)
