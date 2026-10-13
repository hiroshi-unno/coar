; The smallest known witness that PCSat's stratified CEGIS is NOT relatively complete on
; parametric examples: a parametric example is only ever instantiated at one default point, so
; the candidate is never built to satisfy the example as a whole.  The problem is satisfiable -- P(R,x,y) := (x = y) -- and that solution is
; expressible in the INITIAL template: the extracted qualifiers for P are exactly
; "(<false>) = x1[x2]" and "x2 = x3".  With preprocessing PCSat answers sat,0 (P is eliminated).
; Without preprocessing (pcsat_wopp_tbq_ar) it does not terminate: the same parametric negative
; example ($1 != $2 | P($3,$1,$2)) => is regenerated every round (270 rounds in 40 s), the
; candidate stays "true", and check_candidates reports a violation in 269 of them.  Once candidates are
; synthesised against parametric examples as a whole, this input must answer sat without preprocessing.  expected: sat (with preprocessing)
(set-logic DQHORN)
(declare-forall-sort a)
(declare-forall-fun R (a) Bool)
(declare-dep-exists-fun P (R) (a a) Bool)
(assert (forall ((x a)) (=> (R x) (P x x))))
(assert (forall ((x a) (y a)) (=> (and (P x y) (distinct x y)) false)))
(check-sat)
