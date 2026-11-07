(* A validation counterexample to a clause that demands a well-founded unknown,
   generalised from the model's point to a region before it becomes an example.

   The validator finds a model [M] of [not phi], where [phi] is a clause with
   the current candidate substituted for its unknowns.  Recorded as it is, the
   example is the clause's instance at [M]: a point.  A synthesiser that reads
   a well-founded unknown's examples as regions (a ranking built by linear
   programming, by Farkas' lemma over each region's rows) gains nothing from a
   point it does not gain from any other point, and on a loop whose ranking
   needs an invariant it slides: each point is excluded by moving a constant,
   and the next counterexample is the next point.

   The region taken here is the model-based cell of [not phi] at [M]: the
   negation normal form of [not phi], with every conditional term settled by
   its branch at [M], is read as the conjunction of the literals [M] makes true
   in it, choosing a true side of each disjunction (the literal-selection step
   of model-based projection: Komuravelli, Gurfinkel and Chaki, "SMT-based
   model checking for recursive programs", CAV 2014; Bjørner and Janota,
   "Playing with quantified satisfaction", LPAR-20 short papers, 2015).  No
   variable is projected out: every variable of the clause becomes a
   parameter of the example, so the cell is the region itself, and the reader
   of the example eliminates the parameters exactly, by zero columns in its
   Farkas statement.  A disequality the model satisfies becomes the strict
   comparison it satisfies, so the cell is convex.

   The example recorded is [forall p. cell(p) => atoms(p)], where [atoms] are
   the clause's atoms (unknown applications) and the clause is
   [pure \/ atoms].  It is a consequence of the clause exactly when
   [cell => not pure] is valid, and every point of the region refutes the
   candidate exactly when [cell => not phi] is valid.  Both are checked, by one
   validity question, before the example is returned: nothing about the
   literal selection is trusted, so a wrong selection costs the
   generalisation and never soundness.  The model's own point satisfies the
   cell, so the example contains the point example it generalises.

   Only clauses that have a positive atom on a well-founded unknown are
   generalised, and only when the cell is a conjunction of linear comparisons
   over integer and real variables -- the form a region must have to be read
   as rows; anything else is left to the point example. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* Counts printed to stderr at exit when COAR_WF_REGION_COUNT is set: the
   counterexamples asked about, the regions built, and each reason a region
   was not built.  They are what proves a run read the field. *)
let tried = ref 0
let built = ref 0
let refusals : (string, int) Hashtbl.t = Hashtbl.create (module String)

let trace =
  match Sys.getenv "COAR_WF_REGION_COUNT" with
  | None | Some "" -> false
  | Some _ -> true

let () =
  if trace then
    Stdlib.at_exit (fun () ->
        Stdlib.prerr_endline
        @@ sprintf "wf-region: tried %d, built %d%s" !tried !built
             (String.concat
                (List.map
                   (List.sort (Hashtbl.to_alist refusals) ~compare:Stdlib.compare)
                   ~f:(fun (r, n) -> sprintf ", %s %d" r n))))

let refuse reason =
  Hashtbl.update refusals reason ~f:(function None -> 1 | Some n -> n + 1);
  Error reason

(* The point examples a region was built for, by their printed form.  A
   region is recorded in place of nothing: the point stays beside it, because
   the template synthesiser grounds a parametric example at a few instances
   and a candidate can satisfy those and still violate the region, after which
   the validator returns the same region every round and the loop learns
   nothing (measured: the same region on every round of a 60 s run), while the
   point is new each round.  But a reader of regions must not read that point:
   a region that is only an optional offer (a pair the candidate may contain)
   and that no ranking contains is left out, and its point, rankable alone,
   would be kept and move the ranking's constant one step per round (measured
   on the same loop).  So the reader skips a point recorded here.

   The table is process-wide, so a point recorded in one solve is skipped in a
   later one of the same process; that costs a later solve's reader a point,
   never soundness, since what a reader proposes is validated as any
   candidate is.  Guarded by a mutex because validation can run in parallel
   domains. *)
let generalised_points : (string, unit) Hashtbl.t = Hashtbl.create (module String)
let generalised_lock = Stdlib.Mutex.create ()

let note_generalised_point (point : ExClause.t) =
  Stdlib.Mutex.protect generalised_lock (fun () ->
      Hashtbl.set generalised_points ~key:(ExClause.str_of point) ~data:())

(* [without_generalised_points examples]: [examples] less the ones a region
   was built for -- the point examples of the same model, which may still have
   a parameter where the model left a variable unassigned *)
let without_generalised_points (examples : ExClause.t Set.Poly.t) =
  let empty =
    Stdlib.Mutex.protect generalised_lock (fun () ->
        Hashtbl.is_empty generalised_points)
  in
  if empty then examples
  else
    Set.filter examples ~f:(fun ex ->
        let skip =
          Stdlib.Mutex.protect generalised_lock (fun () ->
              Hashtbl.mem generalised_points (ExClause.str_of ex))
        in
        not skip)

(* [completed_model model senv]: the model's value of each variable of [senv],
   found by name and sort; a variable the model left unassigned takes 0 when
   it is an integer or a real.  [None] when some other variable is
   unassigned. *)
let completed_model (model : model) (senv : sort_env_set) =
  Set.to_list senv
  |> List.map ~f:(fun (x, s) ->
         match LogicOld.model_find model (x, s) with
         | Some (Some v) -> Some (x, v)
         | _ ->
             if Term.is_int_sort s then Some (x, T_int.zero ())
             else if Term.is_real_sort s then Some (x, T_real.rzero ())
             else None)
  |> Option.all
  |> Option.map ~f:(Map.Poly.of_alist_reduce ~f:(fun first _ -> first))

let holds map atom =
  try Evaluator.eval_atom @@ Atom.subst map atom
  with exn when not (Common.Timer.is_async exn) -> false

let numeric t =
  let s = Term.sort_of t in
  Term.is_int_sort s || Term.is_real_sort s

(* a disequality [t1 <> t2] that [map] satisfies, as the strict comparison it
   satisfies; any other atom unchanged *)
let split_diseq map atom =
  match atom with
  | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _)
    when numeric t1 && numeric t2 ->
      let real = Term.is_real_sort (Term.sort_of t1) in
      let lt = if real then T_real.mk_rlt t1 t2 else T_int.mk_lt t1 t2 in
      let gt = if real then T_real.mk_rgt t1 t2 else T_int.mk_gt t1 t2 in
      if holds map lt then lt else gt
  | _ -> atom

(* [cell ~map neg]: the conjunction of the literals of [neg] that [map] makes
   true, choosing a true side of each disjunction, with conditional terms
   settled at [map] and disequalities split by [map]; [Error] when [neg] is not
   a quantifier-free combination of atoms or [map] does not satisfy it.
   Post: an [Ok cell] holds at [map] and implies [neg] -- by construction, and
   the caller checks the implication anyway. *)
let cell ~map neg =
  try
    let neg = Formula.nnf_of @@ Mbp.elim_ite_with_model map neg in
    let atoms =
      Mbp.atoms_of map neg |> Set.to_list
      |> List.map ~f:(fun atom ->
             split_diseq map (Normalizer.normalize_atom atom))
    in
    if List.for_all atoms ~f:(holds map) then
      Ok (Formula.and_of (List.map atoms ~f:Formula.mk_atom))
    else Error "a selected literal the model does not satisfy"
  with exn when not (Common.Timer.is_async exn) ->
    Error "not a combination of atoms at the model"

(* the clause as one triple of positive atoms, negative atoms and pure part *)
let clause_triple exi_senv clause =
  clause
  |> Normalizer.normalize_let ~rename:true
  |> Formula.nnf_of
  |> Formula.cnf_of (Logic.to_old_sort_env_map exi_senv)
  |> Set.to_list
  |> function
  | [ t ] -> Some t
  | _ -> None

let on_wf wfpvs = function
  | Atom.App (Predicate.Var (p, _), _, _) ->
      Set.mem wfpvs (Ident.pvar_to_tvar p)
  | _ -> false

(* [example ~id ~timeout_ms ~fenv ~discharge ~exi_senv ~wfpvs ~clause ~refuted
   model]: the region example of the counterexample [model] to [clause] under
   the candidate, [refuted] being [clause] with the candidate substituted (so
   [model] satisfies [not refuted]).

   Pre: [clause] has the clause's variables free and its unknowns applied;
   [refuted] is equivalent to [clause] under the candidate; [model] is a model
   of [not refuted].
   Post: an [Ok ex] is [forall p. cell(p) => atoms(p)] over every variable of
   the clause, where [cell] is a conjunction of linear comparisons over
   integer and real variables, holds at [model], and Z3 has proved
   [cell => not pure /\ not refuted] valid: so [ex] is implied by the clause
   and every point of its region refutes the candidate.  [Error reason] when
   the clause has no positive atom on a well-founded unknown, is not one
   clause, the model does not settle its literals, the cell is not linear, or
   the validity question is not answered [Valid].  Never raises except
   asynchronously.

   [mutate] and [verify] exist for the property test only: [mutate] rewrites
   the cell before it is checked, and [verify:false] skips the validity
   question, so that the test can show its own checks catch a wrong cell. *)
let example ?(id = None) ?(timeout_ms = 1000) ?(mutate = Fn.id) ?(verify = true)
    ?discharge ~fenv ~exi_senv ~wfpvs ~clause ~refuted (model : model) =
  try
    match clause_triple exi_senv clause with
    | None -> refuse "not one clause"
    | Some (ps, ns, pure) ->
        if not (Set.exists ps ~f:(on_wf wfpvs)) then refuse "no wf head"
        else (
          incr tried;
          let neg = Evaluator.simplify @@ Formula.mk_neg refuted in
          match completed_model model (Formula.term_sort_env_of neg) with
          | None -> refuse "a variable the model does not fix"
          | Some map -> (
              match cell ~map neg with
              | Error r -> refuse r
              | Ok cell -> (
                  let cell = mutate cell in
                  let cols = Set.to_list (Formula.term_sort_env_of cell) in
                  if
                    Option.is_none
                      (RankingCheck.region_rows_over cols cell)
                  then refuse "a cell that is not linear"
                  else
                    let goal =
                      Formula.mk_imply cell
                        (Formula.and_of [ Formula.mk_neg pure; neg ])
                    in
                    if verify && Z3Smt.Z3interface.may_not_return goal then
                      refuse "a question that may not return"
                    else
                      match
                        if verify then
                          Z3Smt.Z3interface.check_valid ~id
                            ~timeout:(Some timeout_ms) fenv goal
                        else `Valid
                      with
                      | `Valid -> (
                          match
                            ExClause.make ?discharge exi_senv ps ns
                              (Formula.mk_neg cell)
                          with
                          | None -> refuse "a vacuous example"
                          | Some ex ->
                              incr built;
                              let ex =
                                ExClause.normalize_params
                                  (Map.key_set exi_senv) ex
                              in
                              if trace then
                                Stdlib.prerr_endline
                                  ("wf-region: " ^ ExClause.str_of ex);
                              Ok ex)
                      | `Invalid _ -> refuse "a cell the solver refutes"
                      | _ -> refuse "an undecided cell")))
  with exn when not (Common.Timer.is_async exn) ->
    refuse ("raised " ^ Exn.to_string exn)
