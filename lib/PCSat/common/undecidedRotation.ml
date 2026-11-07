(* Moving the CEGIS loop off a candidate whose rejection taught it nothing.

   A validation question the solver decides neither way rejects the candidate
   with a vacuous counterexample: the example set does not grow, so the next
   synthesis query is the same question and returns the same candidate.  The
   synthesis phase may instead ask once more for a candidate that differs on the
   unknowns the undecided clauses apply, by adding to that one query a
   constraint that excludes the template-parameter assignment it has just
   found (a blocking constraint).

   Contract of the blocking constraint [block ~params ~keys model]: it is false
   under [model] restricted to [params], and true under any assignment that
   differs from [model] on a non-key parameter of [params] or on the SIGN of a
   key of [params]; an assignment that agrees on every non-key parameter and on
   every key's sign falsifies it.  Keys are compared by sign because a
   qualifier key [k] enters a template only as [k > 0 => q] and
   [k < 0 => not q]: two keys with one sign give the same template, so
   excluding one value of a key would let the solver return the same candidate
   with a larger key.

   Why this is sound, for both answers: the constraint is added to one
   synthesis question and never to the examples, so (a) a candidate it leads
   to is validated against every clause like any other and accepted only when
   every question is answered valid, and (b) nothing the refutation side reads
   changes -- an unsatisfiable blocked question is discarded, its core never
   used to learn qualifiers or to widen a template, and the unblocked candidate
   is kept. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* the literal fixing parameter [x] to [v] as the template reads it: a key by
   its sign, any other parameter by its value *)
let literal ~keys (x, s) v =
  let var = Term.mk_var x s in
  if Set.mem keys x && T_int.is_int v then
    let n = T_int.let_int v in
    if Z.equal n Z.zero then Formula.eq var (T_int.zero ())
    else if Z.gt n Z.zero then Formula.gt var (T_int.zero ())
    else Formula.lt var (T_int.zero ())
  else Formula.eq var v

(* [None] when the model assigns no parameter of [params]: there is then
   nothing to exclude, and a constraint [not true] would make the question
   unsatisfiable for no reason *)
let block ~(params : Ident.tvar Set.Poly.t) ~(keys : Ident.tvar Set.Poly.t)
    (model : ((Ident.tvar * Sort.t) * Term.t option) list) : Formula.t option =
  let lits =
    List.filter_map model ~f:(fun ((x, s), v) ->
        match v with
        | Some v when Set.mem params x -> Some (literal ~keys (x, s) v)
        | _ -> None)
  in
  if List.is_empty lits then None
  else Some (Formula.mk_neg (Formula.and_of lits))

(* the template parameters of the unknowns [pvars]: the free variables of
   their templates and the keys of their qualifiers that are parameters of
   the query, and the keys among them *)
let params_of ~(temp_params : Ident.tvar Set.Poly.t)
    ~(template_fvs : Ident.tvar -> Ident.tvar Set.Poly.t)
    ~(qualifier_keys : Ident.tvar -> Ident.tvar Set.Poly.t)
    (pvars : Ident.tvar Set.Poly.t) =
  let keys =
    Set.inter temp_params (Set.concat_map pvars ~f:qualifier_keys)
  in
  let params =
    Set.union keys
      (Set.inter temp_params (Set.concat_map pvars ~f:template_fvs))
  in
  (params, keys)

(* [agrees_on pvars c1 c2]: the two candidates define each unknown of [pvars]
   alike up to bound names (an unknown absent from both counts as alike) *)
let agrees_on (pvars : Ident.tvar Set.Poly.t) (c1 : Logic.cand_map)
    (c2 : Logic.cand_map) =
  let restrict c = Map.Poly.filter_keys c ~f:(Set.mem pvars) in
  CandidateEquiv.same_candidates (restrict c1) (restrict c2)
