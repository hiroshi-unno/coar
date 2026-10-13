open Core
open Ast
open Ast.LogicOld

(** Choosing the point at which a parametric example is instantiated.

    An example over parameters means [forall params. cond => +-P(t)], and
    grounding it means picking one point for those parameters.  Every point
    yields a consequence of the example, so the choice is sound whichever way
    it goes; what it decides is whether the instance says anything at all.

    The default point ignores [cond] entirely -- an integer parameter becomes
    0 -- so on an example whose condition constrains that parameter the point
    lands outside the region the example is about and the instance degenerates
    to [false => +-P(t)], which constrains nothing.  That is not a wrong
    answer, but it is not an example either, and it is not harmless: the
    numeric qualifier generators (interval, octagon, octahedron, polyhedron,
    and the two classifiers) build their half-spaces out of exactly these
    instantiated argument tuples, so every example that degenerates hands them
    the *same* tuple, and a vocabulary learned from a set of identical points
    can separate none of them.

    This module offers the alternative: a point the condition admits, read off
    a model of the condition.  It is handed to the term-level instantiation as
    a callback rather than called from inside it, because that module sits
    below the solver interface -- the same arrangement the three-valued
    evaluation of a qualifier at a parametric atom uses.

    Two things it must do and one it must not.  It must supply a value for a
    parameter the model leaves don't-care, since a substitution that misses one
    leaves the instance non-ground, which is the very thing instantiation is
    for; the dummy value is as good as any there, the condition having no
    opinion about it.  It must carry a budget, a best-effort call with none
    being able to hang a whole run.  And where the formula's sorts are ones
    this solver does not come back from it must not ask at all, which no budget
    covers. *)

(* How often a point was asked for, how often one was found, and how often the
   question was refused on the formula's shape.  These are what say whether the
   choice is worth making on a given input: with nothing asked, every parametric
   example has a condition the default point already satisfies. *)
let asked = ref 0
let found = ref 0
let refused = ref 0
let counts () = (!asked, !found, !refused)

let clear_counts () =
  asked := 0;
  found := 0;
  refused := 0

let str_of_counts () =
  sprintf "asked %d, found %d, refused by shape %d" !asked !found !refused

(** [chooser ~id fenv param_senv cond] is a point for [param_senv] at which
    [cond] holds, or [None] when there is none, the solver could not tell, or
    the question is one it may not come back from.  [None] is not a failure:
    the caller falls back to the point it would have taken anyway, so an
    unavailable answer costs only the generality it would have bought. *)
let chooser ~id ?(timeout = Some 1000) fenv param_senv cond =
  if Map.Poly.is_empty param_senv then None
  else if Z3Smt.Z3interface.may_not_return cond then (
    incr refused;
    None)
  else (
    incr asked;
    match Z3Smt.Z3interface.check_sat ~id ~timeout fenv [ cond ] with
    | `Sat model ->
        let from_model =
          try
            Map.Poly.filter_keys ~f:(Map.Poly.mem param_senv)
            @@ Map.Poly.of_alist_exn @@ LogicOld.remove_dontcare model
          with exn_ when not (Common.Timer.is_async exn_) -> Map.Poly.empty
        in
        let sub =
          Map.Poly.mapi param_senv ~f:(fun ~key ~data ->
              match Map.Poly.find from_model key with
              | Some t -> t
              | None -> T_dt.mk_dummy_for key data)
        in
        incr found;
        Some sub
    | _ -> None)
