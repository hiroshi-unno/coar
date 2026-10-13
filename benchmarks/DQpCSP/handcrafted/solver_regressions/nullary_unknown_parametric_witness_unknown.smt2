; Expected: no verdict within a short budget -- this file is kept for the CRASH it used to
; produce, not for an answer.  It died with `Failure "[to_old_term] u is not bound"` about a
; second in, having printed four lines of environment on stdout where the verdict belongs.
;
; The shape: a NULLARY unknown (`u`, which under the Horn logic is a symbol to synthesise, not
; an arbitrary constant) mentioned in a clause whose example is PARAMETRIC -- the `distinct`
; premise over a quantified sort is what makes it so.  A parametric example carries a condition,
; and before asserting that the example applies at all the synthesizer asks whether some
; instantiation of the example's PARAMETERS satisfies that condition.  It converted the condition
; against the parameter environment alone, and a nullary unknown is in neither that environment
; nor any argument list -- it is a variable rather than an application -- so the conversion
; raised out of the synthesizer.
;
; Its sibling without the `distinct` premise answers `sat,1`: the example is then not parametric,
; no witness question is asked, and nothing converts the condition.  That pair is what says the
; parametric path and not the nullary declaration alone is the trigger.
(set-logic DQHORN)
(declare-forall-sort a)
(declare-fun u () Int)
(declare-fun P (a Int) Bool)
(assert (forall ((x a) (y a)) (=> (and (distinct x y) (= u 0)) (P x 0))))
(assert (forall ((x a)) (=> (P x 0) false)))
(check-sat)
