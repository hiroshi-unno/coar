(* The filter [problem_clause_resolvents_parametric_only] applies to what the
   resolution phase's problem-clause site adds: of the examples that site
   added, the ground points are dropped and the parametric ones (statements for
   every value of some parameter) kept.

   Contract of [keep]: [before] is the example set just before the site ran and
   [after] the set just after it.  With [site_on] and [parametric_only] both
   true the result is the elements of [after] that are in [before] or satisfy
   [parametric]: an example present before the site ran is kept whatever it
   is, so the filter acts only on what the site's step added (the problem's
   unit clauses that unit propagation adds are resolved in that same step, so
   their resolvents are filtered with the site's).  Otherwise the result is
   [after] itself, physically: with the site off nothing the step adds is the
   site's -- only unit propagation's resolvents and what the acquisition
   decides -- and nothing is dropped. *)
let keep ~site_on ~parametric_only ~parametric ~before after =
  if not (site_on && parametric_only) then after
  else
    Core.Set.filter after ~f:(fun e -> Core.Set.mem before e || parametric e)
