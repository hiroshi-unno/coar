open Core
open Common.Ext

(* The true-precondition probe ([true_precondition_probe] of the PCSat
   configuration): the input is read again with some unknowns defined as
   [true] ([PCSP.Parser.define_true]), solved, and a [sat] of it, extended
   with the [true]s ([true_subst]), is the answer.

   The shape it is for.  A program verifier that leaves a closure's
   precondition to inference emits an unknown [p] that a generic adapter's
   invariant demands of every item the inner iterator can produce,
   [forall e i. produces(s, [e], i) => p(e)], and that the closure's body
   assumes.  [p := true] is then often a solution component: every demand
   holds, and the assumptions it weakens were not needed.  Left an unknown, [p]
   sits inside the disjunctions of the clauses that assume the invariant, and
   putting them in clausal form multiplies them out (83 clauses became 1167 on
   one such input, 85 s of a 120 s run), while the same input with [p] given as
   [true] answers in 41 s.

   Which unknowns qualify: those NAMED by the configuration and, when
   [true_precondition_probe_witness_causing] is set, those that occur beneath
   a quantifier existential in effect in the input -- a written [exists] at a
   positive position, a written [forall] at a negative one -- which are the
   unknowns that make the reader skolemise the quantifier into a functional
   predicate; in both cases among the unknowns of the input's signature that
   are of the ordinary kind and Boolean-valued.  [true] meets no
   well-foundedness, functionality or other kind demand, so a kinded unknown
   never qualifies, whatever its name.

   Why the existential test and not another.  The precondition above is
   assumed by the clauses that assume the adapter's invariant, that is beneath
   a [forall] in a body, and that is what makes the reader introduce a witness
   predicate per such quantifier and the clausal form multiply.  On the corpus
   it was measured on, the test selects the precondition alone on each such
   input and nothing on almost every other Thrust input.  The tests on the
   clauses that were tried before it do not separate the precondition from
   the problem's other unknowns:
   - "occurs only negatively" never holds of a precondition, which the caller
     demands (a positive occurrence) as well as the callee assumes; and an
     unknown that does occur only negatively is best set to [false], which the
     elimination of one-sided unknowns already does;
   - "every positive occurrence lies beneath an inner quantifier" describes
     the source, but the reader moves a universal at a positive position out
     to the constraint's prefix, so the demand above reaches the solver as a
     top-level head [p(e)];
   - "every positive occurrence is in a constraint with no other unknown", and
     "never assumed by a constraint that derives no unknown", each select a
     dozen of the input's fifty unknowns and not this one.
   The frontend that emitted the precondition knows which unknown it is, so a
   declaration it carries remains the exact form of the list; the existential
   test is the form that needs none.

   The qualification decides only what is tried, and so only what the probe
   costs; it plays no part in why its answer is sound (see the PCSat solver).

   Why the input is read again rather than the problem substituted.  The
   reader skolemises an existential into a functional predicate exactly when
   an unknown occurs under it, so substituting [true] into the problem it built
   leaves those witness predicates behind: 229 unknowns, against 53 when the
   same input defines the unknown as [true] itself, and a predicate
   elimination that left 129 of them where the other left none. *)

open Ast

(** the substitution [p := fun x1 .. xn -> true] for each of [ps], each [p]
    a key of [senv], the unknowns' sorts *)
let true_subst_senv senv ps =
  Map.Poly.of_alist_exn
  @@ List.map ps ~f:(fun p ->
      let sort = Map.Poly.find_exn senv p in
      let xs =
        List.map (Logic.Sort.args_of sort) ~f:(fun s ->
            (Ident.mk_fresh_tvar (), s))
      in
      (p, Logic.Term.mk_lambda xs (Logic.BoolTerm.mk_bool true)))

(** [true_subst_senv] over the signature of [pcsp] *)
let true_subst pcsp ps = true_subst_senv (PCSP.Problem.senv_of pcsp) ps

(** what the last probe did, for the tests: [`Not_tried] when nothing
    qualified or the probe is off, [`Answered] when its [sat] was the answer,
    [`Discarded] when its outcome was dropped and the problem solved as given *)
let last_probe : [ `Not_tried | `Answered | `Discarded ] ref = ref `Not_tried

(** what the last lower-bound probe did ([lower_bound_probe] of the PCSat
    configuration), for the tests: as [last_probe], [`Answered] when its
    [unsat] was the answer *)
let last_lower_bound_probe : [ `Not_tried | `Answered | `Discarded ] ref =
  ref `Not_tried

(* [only_forced ~forced defined]: whether every unknown in [defined] (names)
   is in [forced], the unknowns the forced-true reading defined as [true]
   before the probe.  When it holds, the probe re-reads the input with exactly
   the definitions the problem it races against was read with, so its problem
   is that problem and it can answer nothing the problem as given does not.
   [defined] empty is not this case: then the probe has nothing to try. *)
let only_forced ~forced defined =
  (not (List.is_empty defined))
  && List.for_all defined ~f:(fun x -> List.mem forced x ~equal:String.equal)
