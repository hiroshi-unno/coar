; Expected: sat,1.  This answered `sat,1` once the synthesizer stopped building its template holes
; from the function-variable APPLICATIONS a formula contains and started covering the unknowns it
; merely MENTIONS as well: a nullary unknown is never an application, so its holes went unbound
; while the template that refers to them was substituted in by name, and the run died with an
; uncaught Failure "hole is not bound" -- exit 1, and a four-line environment dump on stdout where
; the verdict belongs -- after synthesis had already succeeded.
;
; Under the Horn logic this tool reads a declare-fun that does not return Bool as a function to
; SYNTHESISE, not as an arbitrary one -- so `u` is existentially quantified here, and a solution
; may pick any value for it.  Picking a non-zero one makes the first clause vacuous and the second
; is then satisfied by the empty P, so the answer is `sat`.  The one-argument version of exactly
; this file answers `sat,1`, which is what shows the reading and shows that the crash is about
; arity zero rather than about the kind.
;
; Isolated: it crashed only when a clause USED the nullary declaration.  Declaring it and not using
; it answered `sat,0`; declaring it Bool instead, which makes it an ordinary predicate, answered
; `sat,0`; and the same shape with a one-argument function answered `sat,1` -- which is what said
; the arity and not the kind was the difference, and is the verdict this file now gives too.
;
; Note for anyone looking for an "arbitrary constant" encoding: plain SMT-LIB2 constrained Horn
; has no syntax for one.  A non-Bool declare-fun is a symbol to synthesise here, Eldarica refuses
; it by name, and hoice rejects it.  Quantifying a constant universally over a whole clause set is
; what this project's own declare-forall-fun extension exists to express.
(set-logic HORN)
(declare-fun u () Int)
(declare-fun P (Int) Bool)
(assert (=> (= u 0) (P 0)))
(assert (=> (P 0) false))
(check-sat)
