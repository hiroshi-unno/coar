open Core
open Common.Ext
open Ast
open Ast.LogicOld

type table = {
  (* the matrix itself; named apart from the record so that an access does not
     read [table.cells], which says nothing about which is which *)
  mutable cells : (int, Bigarray.int_elt, Bigarray.c_layout) IncrBigArray2.t;
  mutable qarr : Formula.t IncrArray.t;
  mutable aarr : ExAtom.t IncrArray.t;
  qenv : (Formula.t, int) Hashtbl.Poly.t;
  aenv : (ExAtom.t, int) Hashtbl.Poly.t;
  mutable params : sort_env_list;
  mutable qconds :
    ((Formula.t, QualDep.t) Map.Poly.t * Formula.t * Formula.t) option
    IncrArray.t;
      (** per column, a remembered [qdep_cond qdeps qual]: the dependency map
          and the column's qualifier it was computed for (both kept to be
          compared physically) and the result; see [column_cond] *)
}
(** truth table *)

let res_valid = 1
let res_invalid = -1
let res_unknown = 0

let res_encode = function
  | Some true -> res_valid
  | Some false -> res_invalid
  | None -> res_unknown

let str_of_res r =
  if r = res_valid then "T"
  else if r = res_invalid then "F"
  else if r = res_unknown then "_"
  else failwith ""

let create_table ?(def_length = 16) () =
  {
    cells =
      IncrBigArray2.create Bigarray.int Bigarray.c_layout def_length def_length;
    qarr = Array.create ~len:def_length (Formula.mk_true ());
    aarr = Array.create ~len:def_length (ExAtom.mk_true ());
    qenv = Hashtbl.Poly.create ();
    aenv = Hashtbl.Poly.create ();
    params = [];
    qconds = Array.create ~len:def_length None;
  }

let clone_table t =
  {
    params = t.params;
    aenv = Hashtbl.Poly.copy t.aenv;
    qenv = Hashtbl.Poly.copy t.qenv;
    qarr = t.qarr;
    aarr = t.aarr;
    cells = t.cells;
    qconds = Array.copy t.qconds;
  }

let length_of_quals table = Hashtbl.Poly.length table.qenv
let length_of_atoms table = Hashtbl.Poly.length table.aenv

exception Undecided_in_time

(* A budget, in milliseconds, for each validity question [eval_pred_aux] asks
   while it is set ([with_valid_budget]); [None], the default, asks without
   one.  It is held per domain, so a phase that sets it cannot change what a
   parallel domain asks.  A question the solver does not decide within it
   leaves the cell undecided, exactly as an unanswered question does, and is
   not recorded as "not valid" (see [eval_pred_aux]), so a later question
   without a budget can still decide it: only answers can be lost, never a
   cell decided wrongly. *)
let valid_budget_key : int option Domain.DLS.key =
  Domain.DLS.new_key (fun () -> None)

let valid_budget_ms () = Domain.DLS.get valid_budget_key

(* Contract: runs [f] with the budget set to [ms] and restores the previous
   budget on every exit, raising included; [None] leaves the budget as it is. *)
let with_valid_budget ms f =
  match ms with
  | None -> f ()
  | Some _ ->
      let saved = Domain.DLS.get valid_budget_key in
      Domain.DLS.set valid_budget_key ms;
      Exn.protect ~f ~finally:(fun () -> Domain.DLS.set valid_budget_key saved)

(* Whether a cell whose validity question [Z3interface.may_not_return] refuses
   is left undecided instead of asked.  Such a question binds a sequence under
   a quantifier, and Z3's own budget does not hold on it: a labeling phase was
   observed asking one, with no budget, for minutes, when a guard carried a
   law over sequences from the clause it was derived from.  Leaving the cell
   undecided is what an unanswered question does, and the question is not
   recorded, as under a strict deadline.  Process-wide, set from the
   validator's configuration; off, nothing changes. *)
let leave_unreturnable_cells_undecided = ref false

(* Whether a cell whose qualifier applies a defined function (a
   [define-fun-rec], a datatype's size function) is first rewritten by
   [Evaluator.unfold_rec_apps]: every application is replaced by its
   definition's body at its arguments, the recursion following the guards,
   and the rewritten qualifier is used only when no defined function is left
   in it; otherwise the cell is evaluated as before.  The rewriting is an
   equivalence in every model (each step is an instance of the definition's
   equation, see [Evaluator.unfold_rec_apps]), so a cell is decided exactly
   as a solver that settled the question would decide it, never otherwise.
   What it changes is how: at a ground example a qualifier such as
   [length l > 0] or [add2(x, k) = r] needs as many unfoldings as the
   arguments are large, which evaluation does at once, while the validity
   question it replaces is a quantified one for the solver (the definition's
   equation), answered under the query's budget or not at all.  At a
   parametric example a guard reading a parameter stays undecided, the
   rewriting gives up and the cell goes the old way (a value there needs
   induction).  Process-wide, set from PCSat's
   [eval_recursive_qualifiers_ground]; off, nothing changes. *)
let eval_recursive_qualifiers_ground = Atomic.make false

(* Whether a cell that needs induction is left undecided without asking the
   solver.  A cell is skipped when it is parametric and its qualifier, with
   the row's arguments substituted, applies a defined function (a
   [define-fun-rec], a datatype's size function) whose unfolding
   ([Evaluator.unfold_rec_apps_why]) stops at a guard that reads one of the
   example's parameters: the guard decides whether the recursion goes on, so
   the value at every instance of the parameters is a statement about the
   whole recursion, which in general takes induction (for [add2(1, 2 + c0)],
   positive for every [c0 >= 0], it does: z3 and cvc5, the latter with
   [--quant-ind], both fail to decide it in 10 s, and with no budget on a
   cell the question never returns).  Every other cell is evaluated as
   before: a ground one, one whose unfolding completes, one whose unfolding
   gives up for another reason (an unknown function, the fuel, a guard
   reading only variables that are not parameters), and one whose qualifier
   applies no defined function.
   CONTRACT: a skipped cell is [None], which is exactly what an unanswered or
   timed-out question produces, and nothing is recorded for it; so soundness
   is that of a timeout.  What it costs is completeness: a skipped cell that
   the solver would have decided (some do, quickly) stays undecided.  The
   test is structural, not a budget.  Process-wide, set from PCSat's
   [skip_induction_cells]; off, nothing changes. *)
let skip_induction_cells = Atomic.make false

(* A COUNT, NOT A PASS: with [COAR_RECQUAL_CENSUS=1], every cell
   [eval_pred_aux] evaluates whose qualifier, once the row's arguments are
   substituted, applies a function of the function environment (a
   [define-fun-rec], a datatype's size function) is counted, split by whether
   the cell is ground (no free variable in the qualifier or the row's
   condition) or parametric, by whether evaluation alone decided it or the
   solver was asked, and by the outcome; the solver's wall time is summed.
   One line to stderr at exit, and a snapshot at most once a second (a run
   killed at its budget runs no [at_exit]); [COAR_RECQUAL_CENSUS=2] also
   prints every formula of such a cell handed to the solver.  Without the
   variable nothing is walked. *)
module RecQualCensus = struct
  (* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
  let on =
    Lazy.from_val
      (match Sys.getenv "COAR_RECQUAL_CENSUS" with
      | Some ("1" | "2" | "true" | "yes") -> true
      | _ -> false)

  (* per class (0 ground, 1 parametric), at [8 * class +]: 0 cells; 1 decided
     without the solver; 2 solver asked; 3 of those decided; 4 solver calls;
     5 solver microseconds; 6 cells whose qualifier [unfold_cell] rewrote
     into one applying no defined function; 7 cells left undecided by
     [skip_induction_cells] (counted under "decided without the solver" too,
     since no solver was asked) *)
  let counts = Array.init 16 ~f:(fun _ -> Atomic.make 0)
  let registered = Atomic.make false

  let report () =
    let g i = Atomic.get counts.(i) in
    let line c k =
      sprintf
        "%s cells=%d by_eval=%d solver_asked=%d solver_decided=%d \
         solver_calls=%d solver_ms=%d unfolded=%d skipped=%d"
        k (g (8 * c)) (g ((8 * c) + 1)) (g ((8 * c) + 2))
        (g ((8 * c) + 3)) (g ((8 * c) + 4)) (g ((8 * c) + 5) / 1000)
        (g ((8 * c) + 6)) (g ((8 * c) + 7))
    in
    Stdlib.Printf.eprintf "[recqual-census] pid=%d %s | %s\n%!"
      (Core_unix.getpid () |> Pid.to_int)
      (line 0 "ground") (line 1 "parametric")

  (* a run killed at its budget (or a forked copy killed by its parent) runs no
     [at_exit], so a snapshot is also printed after a cell whenever a second
     has passed since the last one; the last line of a process is its count *)
  let last = Atomic.make 0.

  let snapshot () =
    let now = Core_unix.gettimeofday () in
    let l = Atomic.get last in
    if Float.(now -. l >= 1.) && Atomic.compare_and_set last l now then report ()

  let register () =
    if not (Atomic.exchange registered true) then Stdlib.at_exit report

  (* [COAR_RECQUAL_CENSUS=2]: also print each formula handed to the solver *)
  (* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
  let verbose =
    Lazy.from_val (match Sys.getenv "COAR_RECQUAL_CENSUS" with Some "2" -> true | _ -> false)

  let add i n = ignore (Atomic.fetch_and_add counts.(i) n : int)
end

(* The condition a qualifier's dependencies put on its cells, over the
   predicate's parameters: [true] for a qualifier with no dependency, and the
   simplified dependency formula, with the qualifier's own literal set to
   [true], otherwise.  A function of [qdeps] and [qual] alone -- it does not
   read the atom -- given the process-wide environments and simplifier
   switches, which are set before solving starts. *)
let qdep_cond ~print qdeps qual =
  match Map.Poly.find qdeps qual with
  | None -> Formula.mk_true ()
  | Some qdep ->
      print
      @@ lazy (sprintf "[eval_pred_aux] eval_qdep: %s" (QualDep.str_of qdep));
      let qdep =
        QualDep.map_atom qdep ~f:(function
          | QualDep.LFormula (phi, _) when Stdlib.(phi = qual) ->
              QualDep.mk_atom QualDep.LTrue
          | lit -> QualDep.mk_atom lit)
      in
      Evaluator.simplify @@ QualDep.formula_of qdep

(* [qdep_cond qdeps table.qarr.(qi)], computed once per column rather than
   once per cell: every cell of a column used to recompute it, a dependency
   lookup keyed by a formula and a simplification, although it does not depend
   on the cell's atom.
   Exact: a remembered value is returned only for the same dependency map and
   the same qualifier, both compared physically (a new map or a column slot
   reused for another qualifier misses and recomputes), and a value is
   remembered only when computing it drew no fresh name (the global counter
   unmoved and no replay of names active), so it is the value the per-cell
   computation returns, not merely one equal up to names; when a fresh name
   was drawn every call recomputes, as before. *)
let column_cond ~print (table : table) qdeps qi =
  let qual = table.qarr.(qi) in
  match if qi < Array.length table.qconds then table.qconds.(qi) else None with
  | Some (qdeps', qual', c) when phys_equal qdeps' qdeps && phys_equal qual' qual
    ->
      c
  | _ ->
      let before = Atomic.get Ident.tvar_count in
      let c = qdep_cond ~print qdeps qual in
      if
        (not (Ident.replaying_fresh_names ()))
        && Atomic.get Ident.tvar_count = before
      then
        table.qconds <- IncrArray.auto_set table.qconds qi (Some (qdeps, qual, c));
      c

(* A cell's validity question.  With [SeqLengthForm.enabled] a question over
   free sequence variables is first asked over their lengths and arrays
   ([SeqLengthForm.decide_z3]), whose answer, when it gives one, is the
   answer to the same question; otherwise, and with the switch off, it is
   asked of Z3 as it always was. *)
let z3_is_valid ~id fenv phi =
  match
    if Atomic.get SeqLengthForm.enabled then
      SeqLengthForm.decide_z3 ~id fenv phi
    else None
  with
  | Some b -> b
  | None -> Z3Smt.Z3interface.is_valid ~id fenv phi

let z3_check_valid ~timeout ~id fenv phi =
  match
    if Atomic.get SeqLengthForm.enabled then
      SeqLengthForm.decide_z3 ~timeout ~id fenv phi
    else None
  with
  | Some true -> `Valid
  | Some false -> `Invalid []
  | None -> Z3Smt.Z3interface.check_valid ~timeout ~id fenv phi

(* [cond_of_qual], when given, must be [qdep_cond ~print qdeps qual]
   ([column_cond] supplies it), and is then used instead of recomputing it. *)
let eval_pred_aux ?cond_of_qual ~print ~id fenv qdeps (params, qual)
    (param_senv, cond, _sorts, args) =
  print
  @@ lazy
       (sprintf "[eval_pred_aux] evaluating %s with (%s => %s)"
          (Formula.str_of qual) (Formula.str_of cond)
          (String.concat_map_list ~sep:"," ~f:Term.str_of args));
  let cond' =
    match cond_of_qual with
    | Some c -> c
    | None -> qdep_cond ~print qdeps qual
  in
  (match Sys.getenv "COAR_TT" with
   | Some _ when List.length params <> List.length args ->
       Stdlib.prerr_endline
       @@ Printf.sprintf "[TT] params=%d (%s) args=%d (%s) qual=%s"
            (List.length params)
            (String.concat ~sep:"," (List.map ~f:(fun (x, _) -> Ident.name_of_tvar x) params))
            (List.length args)
            (String.concat_map_list ~sep:"," ~f:Term.str_of args)
            (Formula.str_of qual)
   | _ -> ());
  let sub =
    Map.Poly.of_alist_exn @@ List.zip_exn (List.map ~f:fst params) args
  in
  let phi = Formula.subst sub qual in
  let cond = Formula.mk_and cond @@ Formula.subst sub cond' in
  print @@ lazy (sprintf "[eval_pred_aux] cond: %s" (Formula.str_of cond));
  print @@ lazy (sprintf "[eval_pred_aux] phi: %s" (Formula.str_of phi));
  let census_class =
    if
      Lazy.force RecQualCensus.on
      && not (Set.is_empty (Formula.fvar_apps_of phi))
    then (
      RecQualCensus.register ();
      Some
        (if Set.is_empty (Formula.tvs_of phi) && Set.is_empty (Formula.tvs_of cond)
         then 0
         else 1))
    else None
  in
  let ground_on = Atomic.get eval_recursive_qualifiers_ground in
  let skip_on = Atomic.get skip_induction_cells in
  (* [`Skip]: the cell needs induction (see [skip_induction_cells]) *)
  let unfolded =
    if (ground_on || skip_on) && not (Set.is_empty (Formula.fvar_apps_of phi))
    then (
      let t0 = Time_ns.now () in
      let r = Evaluator.unfold_rec_apps_why phi in
      if Lazy.force RecQualCensus.verbose then
        Stdlib.Printf.eprintf "[recqual-census] unfold %.3f s %s -> %s\n%!"
          (Time_ns.Span.to_sec (Time_ns.diff (Time_ns.now ()) t0))
          (Formula.str_of phi)
          (match r with
          | Ok p -> Formula.str_of p
          | Error (Evaluator.Stop_at_guard c) -> "stop at guard " ^ Term.str_of c
          | Error Evaluator.Stop_other -> "none");
      match r with
      | Error (Evaluator.Stop_at_guard c)
        when skip_on
             && Set.exists (Term.tvs_of c) ~f:(Map.Poly.mem param_senv) ->
          `Skip
      | Ok phi' when ground_on -> `Unfolded phi'
      | _ -> `As_before)
    else `As_before
  in
  let phi, cond =
    match unfolded with
    | `Unfolded phi' ->
        Option.iter census_class ~f:(fun c -> RecQualCensus.add ((8 * c) + 6) 1);
        ( phi',
          if Set.is_empty (Formula.fvar_apps_of cond) then cond
          else Option.value (Evaluator.unfold_rec_apps cond) ~default:cond )
    | `Skip | `As_before -> (phi, cond)
  in
  let asked = ref false in
  (* With [COAR_TT_ASK_LOG=path] in the environment, each question a cell
     sends to the solver is written to [path] before it is asked (so a run
     stopped inside one leaves that question there) and its seconds are
     appended to [path.tsv] after; a question that took at least
     [COAR_TT_ASK_SLOW_S] seconds (default 1) is also appended whole to
     [path.slow], so a slow question that does return is kept beside the one
     a stopped run leaves in [path]; every solver check the question makes
     is written as SMT-LIB to [path.q_k.smt2] before it is asked, and kept
     as [path.slow_<digest>_k.smt2] when the question was slow; a
     diagnostic, inert without the variable *)
  let ask f phi =
    match Sys.getenv "COAR_TT_ASK_LOG" with
    | Some path when not (String.is_empty path) ->
        let text = Formula.str_of phi in
        let where = Common.PhaseTime.current_path () in
        Out_channel.write_all path ~data:(";; " ^ where ^ "\n" ^ text);
        let t0 = Time_ns.now () in
        let r =
          Z3Smt.Z3interface.with_query_dump (path ^ ".q") (fun () -> f phi)
        in
        let secs = Time_ns.Span.to_sec (Time_ns.diff (Time_ns.now ()) t0) in
        let digest = Md5.to_hex (Md5.digest_string text) in
        Out_channel.with_file (path ^ ".tsv") ~append:true ~f:(fun oc ->
            Out_channel.output_string oc
              (sprintf "%.3f\t%d\t%s\t%s\n" secs (String.length text) digest
                 where));
        let slow =
          match Sys.getenv "COAR_TT_ASK_SLOW_S" with
          | Some v -> Option.value (Float.of_string_opt v) ~default:1.
          | None -> 1.
        in
        if Float.(secs >= slow) then (
          Out_channel.with_file (path ^ ".slow") ~append:true ~f:(fun oc ->
              Out_channel.output_string oc
                (sprintf ";; %.3f s %s %s\n%s\n" secs digest where text));
          (* keep the solver's own form of each check it made *)
          List.iter (List.range 0 8) ~f:(fun k ->
              let q = sprintf "%s.q_%d.smt2" path k in
              if Stdlib.Sys.file_exists q then
                Stdlib.Sys.rename q
                  (sprintf "%s.slow_%s_%d.smt2" path digest k)));
        r
    | _ -> (
    match census_class with
    | None -> f phi
    | Some c ->
        asked := true;
        RecQualCensus.add ((8 * c) + 4) 1;
        RecQualCensus.snapshot ();
        if Lazy.force RecQualCensus.verbose then
          Stdlib.Printf.eprintf "[recqual-census] ask %s %s\n%!"
            (if c = 0 then "ground" else "parametric")
            (Formula.str_of phi);
        let t0 = Time_ns.now () in
        Exn.protect
          ~f:(fun () -> f phi)
          ~finally:(fun () ->
            RecQualCensus.add ((8 * c) + 5)
              (Int.of_float @@ Time_ns.Span.to_us
              @@ Time_ns.diff (Time_ns.now ()) t0)))
  in
  (* Inside a solve given a strict deadline ([SolveDeadline]) a validity
     question goes to the solver with the time left as its budget, and not at
     all once the deadline has passed: a row is evaluated against every
     qualifier, each question without a budget otherwise, and one labeling
     phase of a nested solve was observed running for minutes past its
     deadline.  A question not asked, or not decided in time, leaves the cell
     undecided ([None]), as an unanswered question does; a ground cell is
     still decided by evaluation.  It is signalled by an exception rather
     than answered "not valid" because the evaluator records every answer in
     a table that outlives the nested solve, and a recorded "not valid" would
     keep the cell undecided in the enclosing solve, which has no deadline.
     Without a strict deadline nothing changes.  A budget set by
     [with_valid_budget] is applied the same way, capped by the time left
     before a strict deadline when there is one; with neither, a question is
     asked as it always was. *)
  let res =
    match SolveDeadline.cap_ms_strict (valid_budget_ms ()) with
    | _ when (match unfolded with `Skip -> true | _ -> false) ->
        Option.iter census_class ~f:(fun c -> RecQualCensus.add ((8 * c) + 7) 1);
        None
    | None when !leave_unreturnable_cells_undecided -> (
        let is_valid phi =
          if Z3Smt.Z3interface.may_not_return phi then raise Undecided_in_time
          else ask (z3_is_valid ~id fenv) phi
        in
        try Evaluator.check ~cond is_valid phi with Undecided_in_time -> None)
    | None ->
        Evaluator.check ~cond (ask (z3_is_valid ~id fenv)) phi
    | Some _ -> (
        let is_valid phi =
          if
            SolveDeadline.expired_strict ()
            || !leave_unreturnable_cells_undecided
               && Z3Smt.Z3interface.may_not_return phi
          then raise Undecided_in_time
          else
            match
              ask
                (z3_check_valid
                   ~timeout:(SolveDeadline.cap_ms_strict (valid_budget_ms ()))
                   ~id fenv)
                phi
            with
            | `Valid -> true
            | `Invalid _ -> false
            | _ -> raise Undecided_in_time
        in
        try Evaluator.check ~cond is_valid phi with Undecided_in_time -> None)
  in
  (match census_class with
  | None -> ()
  | Some c ->
      RecQualCensus.add (8 * c) 1;
      if !asked then (
        RecQualCensus.add ((8 * c) + 2) 1;
        if Option.is_some res then RecQualCensus.add ((8 * c) + 3) 1)
      else RecQualCensus.add ((8 * c) + 1) 1;
      RecQualCensus.snapshot ());
  (match res with
  | Some true -> print @@ lazy "[eval_pred_aux] true"
  | Some false -> print @@ lazy "[eval_pred_aux] false"
  | None -> print @@ lazy "[eval_pred_aux] unknown");
  res

(* assume the ExAtom argument is papp or ppapp*)
let eval_pred ?cond_of_qual ~id fenv qdeps (params, qual) = function
  | ExAtom.PApp ((_pvar, sorts), args) ->
      eval_pred_aux ?cond_of_qual ~id fenv qdeps (params, qual)
        (Map.Poly.empty, Formula.mk_true (), sorts, args)
  | ExAtom.PPApp ((param_senv, cond), ((_pvar, sorts), args)) ->
      eval_pred_aux ?cond_of_qual ~id fenv qdeps (params, qual)
        (param_senv, cond, sorts, args)
  | _ -> assert false

let update_with_atom ~print ~id (table : table) fenv qdeps atom =
  (* two examples differing only by a bijection on their parameters are the same
     example, so they must be one row: otherwise they get two evaluations, two
     sets of undecided cells, and a refutation that needs them to be the same
     atom never gets it *)
  let atom = ExAtom.canon_key atom in
  if Hashtbl.Poly.mem table.aenv atom then ()
  else (
    (* What the synthesis phase receives.  There is no USE count beside it and
       that is a gap rather than an omission: a parametric argument makes a cell
       undecided, which the table records honestly, but nothing here says
       whether the candidate search then did anything a decided cell would not
       have let it do.  Until that exists, a mechanism upstream can be seen
       delivering generality to this phase and cannot be seen being paid for
       it. *)
    GeneralityMonitor.(
      if on () then
        arrive Synthesis
          ~ground:(if ExAtom.is_ppapp atom then 0 else 1)
          ~parametric:(if ExAtom.is_ppapp atom then 1 else 0)
          ~guarded:0);
    let ai = length_of_atoms table in
    table.aarr <- IncrArray.auto_set table.aarr ai atom;
    Hashtbl.Poly.add_exn table.aenv ~key:atom ~data:ai;
    for qi = 0 to length_of_quals table - 1 do
      table.cells <-
        IncrBigArray2.auto_set table.cells qi ai
          (res_encode
          @@ eval_pred
               ~cond_of_qual:(column_cond ~print table qdeps qi)
               ~print ~id fenv qdeps
               (table.params, table.qarr.(qi))
               atom)
    done)

let update_with_qualifier ~print ~id (table : table) fenv qdeps qual =
  if Hashtbl.Poly.mem table.qenv qual then ()
  else
    let qi = length_of_quals table in
    Hashtbl.Poly.add_exn table.qenv ~key:qual ~data:qi;
    table.qarr <- IncrArray.auto_set table.qarr qi qual;
    for ai = 0 to length_of_atoms table - 1 do
      table.cells <-
        IncrBigArray2.auto_set table.cells qi ai
          (res_encode
          @@ eval_pred
               ~cond_of_qual:(column_cond ~print table qdeps qi)
               ~print ~id fenv qdeps (table.params, qual)
          @@ table.aarr.(ai))
    done

type t = (Ident.pvar, table) Hashtbl.Poly.t
(** map from pvar to table *)

let create () = Hashtbl.Poly.create ()

let clone t =
  Hashtbl.Poly.fold t ~init:(create ()) ~f:(fun ~key ~data acc ->
      Hashtbl.Poly.add_exn ~key ~data:(clone_table data) acc;
      acc)

let update_map t pvar table = Hashtbl.Poly.set t ~key:pvar ~data:table

let get_table t pvar =
  match Hashtbl.Poly.find t pvar with
  | Some table -> table
  | None ->
      (*if no table for pvar exists, create and return a new one *)
      let table = create_table () in
      Hashtbl.Poly.add_exn ~key:pvar ~data:table t;
      update_map t pvar table;
      table

let update_map_with_atom ~print ~id t fenv hspaces atom =
  match ExAtom.pvar_of atom with
  | None -> ()
  | Some pvar ->
      let hspace = Hashtbl.Poly.find_exn hspaces (Ident.pvar_to_tvar pvar) in
      update_with_atom ~print ~id (get_table t pvar) fenv hspace.HypSpace.qdeps
        atom

let update_map_with_atoms ~print ~id t qdeps fenv =
  Set.iter ~f:(update_map_with_atom ~print ~id t fenv qdeps)

let update_map_with_example ~print ~id t fenv hspaces example =
  Set.iter example.ExClause.negative
    ~f:(update_map_with_atom ~print ~id t fenv hspaces);
  Set.iter example.ExClause.positive
    ~f:(update_map_with_atom ~print ~id t fenv hspaces)

let update_map_with_examples ~print ~id t fenv hspaces =
  Set.iter ~f:(update_map_with_example ~print ~id t fenv hspaces)

(* The parameter list every qualifier in this table is read against.  A table
   is a cache of "what is this qualifier's value at this atom", and the two are
   related by substituting the atom's arguments for these parameters, so a
   table whose parameters are the wrong length cannot evaluate anything: the
   substitution is built by zipping the two.  A caller that puts rows of an
   extended shape into a table -- an atom carrying (index, value) columns
   beside the predicate's own arguments -- must say so here first.

   A table serves ONE parameter list.  Every qualifier column already in it
   was evaluated at every row by substituting the row's arguments for the
   list that was current then, and every row added later is evaluated against
   the list current now; so a second caller with a list that names different
   variables would leave the first caller's qualifiers mentioning variables
   the substitution no longer binds.  Such a qualifier evaluates to nothing and
   its cells are recorded undecided -- a legal value, so nothing downstream
   would notice, and a synthesis query built from them silently loses the
   constraints those qualifiers stood for.  Hence: setting the list a table
   already has is a no-op, setting it on a table that has none is the first
   setting, and anything else is refused.  Callers that generate several
   templates over one table must therefore name the template's parameters
   identically in all of them.  Names are compared with their sorts; the
   empty list is "not yet set", which is indistinguishable from the list of a
   nullary predicate, and for such a predicate every setting is the empty
   list again. *)
let set_params table params =
  let same (x1, s1) (x2, s2) =
    Ident.tvar_equal x1 x2
    && String.equal (Term.str_of_sort s1) (Term.str_of_sort s2)
  in
  if List.is_empty table.params then table.params <- params
  else if List.equal same table.params params then ()
  else
    failwith
    @@ sprintf
         "[TruthTable.set_params] this table's qualifiers are read against \
          the parameters (%s), and a caller now asks for (%s).  A table holds \
          one parameter list, and every qualifier column in it is evaluated \
          by substituting a row's arguments for that list, so it cannot serve \
          both: the qualifiers built over one list would have their variables \
          left free under the other and be recorded undecided.  Every \
          template sharing this table must name its parameters identically."
         (str_of_sort_env_list Term.str_of_sort table.params)
         (str_of_sort_env_list Term.str_of_sort params)

(* Adds [qualifiers] as columns of [pvar]'s table, read against [params].
   The list goes through [set_params] like every other setting, so a caller
   whose list names different variables from the one the table already holds
   is refused rather than silently re-pointing every existing column.  Both
   callers pass a list that is the same on every call for one predicate: the
   hypothesis space's parameters, which every template module builds as
   [x1 .. xn] over the predicate's argument sorts, and the classification
   synthesizer's list, built the same way from the same sorts; a table is
   never shared between predicates, and cloning one copies its list. *)
let update_map_with_qualifiers ~print ~id t fenv qdeps pvar (params, qualifiers)
    =
  let table = get_table t pvar in
  set_params table params;
  Set.iter qualifiers ~f:(update_with_qualifier ~print ~id table fenv qdeps)

(* this may update truth table *)
let index_of_atom ~print ~id table fenv qdeps atom =
  (* the same key the insertion uses; a lookup that does not canonicalise finds
     nothing and adds a second row for an atom that is already there *)
  let atom = ExAtom.canon_key atom in
  match Hashtbl.Poly.find table.aenv atom with
  | Some ai -> ai
  | None ->
      print
      @@ lazy (sprintf "[index_of_atom] adding atom: %s" (ExAtom.str_of atom));
      let ai = length_of_atoms table in
      (* [COAR_NEWROW_TRACE=1]: a diagnostic, inert without the variable.
         Prints the atom a row is added for, its parameter count, the
         qualifier count, the seconds the row took, and the first existing
         row that is the same atom once every free variable is treated as a
         parameter (so unused parameters are dropped and all names numbered
         by first occurrence): a candidate duplicate up to renaming, not a
         proof that the two rows mean the same. *)
      let trace = Option.is_some (Sys.getenv "COAR_NEWROW_TRACE") in
      let t0 = Time_ns.now () in
      (* a row added on demand evaluates every qualifier at the atom; its own
         phase so that the account separates it from the rest of its caller *)
      Common.PhaseTime.with_phase "new-row" (fun () ->
          update_with_atom ~print ~id table fenv qdeps atom);
      (if trace then
         let shape = function
           | ExAtom.PPApp ((_, c), ((pv, ss), ts)) ->
               let senv =
                 Map.of_set_exn
                 @@ Set.Poly.union_list
                      (Formula.sort_env_of c :: List.map ts ~f:Term.sort_env_of)
               in
               ExAtom.str_of
                 (ExAtom.canon_key (ExAtom.PPApp ((senv, c), ((pv, ss), ts))))
           | a -> ExAtom.str_of a
         in
         let s = shape atom in
         let dup =
           List.find (List.range 0 ai) ~f:(fun i ->
               String.equal (shape table.aarr.(i)) s)
         in
         Stdlib.Printf.eprintf
           "[newrow] row=%d quals=%d params=%d secs=%.3f dup=%s atom=%s\n%!" ai
           (length_of_quals table)
           (Map.Poly.length (ExAtom.params_of atom))
           (Time_ns.Span.to_sec (Time_ns.diff (Time_ns.now ()) t0))
           (match dup with Some i -> string_of_int i | None -> "none")
           (ExAtom.str_of atom));
      ai

(* this may update truth table *)
let index_of_qual ~print ~id table fenv qdeps qual =
  match Hashtbl.Poly.find table.qenv qual with
  | Some qi -> qi
  | None ->
      print
      @@ lazy (sprintf "[index_of_qual] adding qual: %s" (Formula.str_of qual));
      let qi = length_of_quals table in
      update_with_qualifier ~print ~id table fenv qdeps qual;
      qi

(** qlist and alist *)

type qlist = int list
type alist = (int, int) Map.Poly.t
(* qlist = []; alist = Map.Poly.empty *)

let label_pos = 1
let label_neg = -1

let num_pos_neg_labeled_atoms alist =
  let pelist, nelist =
    Map.Poly.partition_tf alist ~f:(( = ) label_pos (*ToDo*))
  in
  (Map.Poly.length pelist, Map.Poly.length nelist)

let num_pos_labeled_atoms alist =
  Map.Poly.length @@ Map.Poly.filter alist ~f:(( = ) label_pos)

let num_neg_labeled_atoms alist =
  Map.Poly.length @@ Map.Poly.filter alist ~f:(( = ) label_neg)

let num_atoms alist = Map.Poly.length alist
let num_quals qlist = List.length qlist

(* return npapps, nppapps, ppapps, pppapps *)
let papps_of table alist =
  Map.Poly.fold alist
    ~init:(Set.Poly.empty, Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
    ~f:(fun ~key ~data (npapps, nppapps, ppapps, pppapps) ->
      match table.aarr.(key) with
      | ExAtom.PApp atom ->
          if data = label_pos then
            (npapps, nppapps, Set.add ppapps atom, pppapps)
          else if data = label_neg then
            (Set.add npapps atom, nppapps, ppapps, pppapps)
          else assert false
      | ExAtom.PPApp atom ->
          if data = label_pos then
            (npapps, nppapps, ppapps, Set.add pppapps atom)
          else if data = label_neg then
            (npapps, Set.add nppapps atom, ppapps, pppapps)
          else assert false
      | _ -> (npapps, nppapps, ppapps, pppapps))

let pos_neg_atoms_of table =
  Map.Poly.fold ~init:(Set.Poly.empty, Set.Poly.empty)
    ~f:(fun ~key ~data (pos, neg) ->
      let atom = table.aarr.(key) in
      if data = label_pos then (Set.add pos atom, neg)
      else if data = label_neg then (pos, Set.add neg atom)
      else assert false)

let labeled_atoms_of table =
  Map.Poly.fold ~init:Set.Poly.empty ~f:(fun ~key ~data atoms ->
      Set.add atoms (table.aarr.(key), data))

(** remove redundant atoms *)
let reduced_alist_of (t : table) (qlist, alist) =
  snd
  @@ Map.Poly.fold alist ~init:(Set.Poly.empty, Map.Poly.empty)
       ~f:(fun ~key:ai ~data:l (memo, alist) ->
         let example = (l, List.map qlist ~f:(fun qi -> t.cells.{qi, ai})) in
         if Set.mem memo example then (memo, alist)
         else (Set.add memo example, Map.Poly.add_exn alist ~key:ai ~data:l))

(** remove redundant qualifiers the prior qualifier in [qlist] is adopted if
    there are multiple indistinguishable qualifiers *)
let reduced_qlist_of ?(require_evidence = false) (t : table) (qlist, alist) =
  let atoms_length = length_of_atoms t in
  let alist = Map.Poly.to_alist alist in
  let neg_of qualifier =
    let neg_qualifier =
      Bigarray.Array1.create Bigarray.Int Bigarray.C_layout
        (Bigarray.Array1.dim qualifier)
    in
    Bigarray.Array1.blit qualifier neg_qualifier;
    for i = 0 to Bigarray.Array1.dim neg_qualifier - 1 do
      neg_qualifier.{i} <- 0 - neg_qualifier.{i}
    done;
    neg_qualifier
  in
  let rec inner memo = function
    | [] -> []
    | idx :: qlist ->
        let qualifier =
          if atoms_length = 0 then
            Bigarray.Array1.create Bigarray.Int Bigarray.C_layout 0
          else if List.is_empty alist then
            Bigarray.Array1.sub
              (Bigarray.Array2.slice_left t.cells idx)
              0 atoms_length
          else
            Bigarray.Array1.of_array Bigarray.Int Bigarray.c_layout
            @@ Array.of_list
            @@ List.map alist ~f:(fun (ai, _) -> t.cells.{idx, ai})
        in
        (* [require_evidence] is off by default so that the OTHER consumer of
           this function -- the decision-tree classifier, which calls it with no
           flag on every run -- keeps the behaviour it was measured with. The
           template path passes it.

           Two qualifiers may only be merged on EVIDENCE that they agree.  A
           column with no cells is not evidence of anything -- with no examples
           yet every column is empty, and merging on that collapses the whole
           space to one qualifier -- and neither is a cell whose value is
           undecided: [res_unknown] records that this example does not settle
           the qualifier, so two qualifiers undecided at the same place have not
           been shown to be the same, and an example that decides it later will
           tell them apart.  Merging them does not delete them, because the
           space is rebuilt each round, but it defers the distinction by a
           CEGIS round, which is paid for in refuted candidates. *)
        let has_evidence =
          (not require_evidence)
          || Bigarray.Array1.dim qualifier > 0
             &&
             let ok = ref true in
             for i = 0 to Bigarray.Array1.dim qualifier - 1 do
               if qualifier.{i} = res_unknown then ok := false
             done;
             !ok
        in
        if has_evidence && Set.mem memo qualifier then inner memo qlist
        else
          let memo' =
            if has_evidence then
              Set.add (Set.add memo qualifier) (neg_of qualifier)
            else memo
          in
          idx :: inner memo' qlist
  in
  inner Set.Poly.empty qlist

(** printers *)

let str_of_quals t qlist =
  let qlist = List.sort qlist ~compare:Int.compare in
  String.concat_map_list ~sep:"\n" qlist ~f:(fun qi ->
      let phi = t.qarr.(qi) in
      let rank = Rank.rank_of phi in
      sprintf "%d %s: %s" qi (Rank.str_of rank) (Formula.str_of phi))

let str_of_atoms t alist =
  let alist =
    List.sort (Map.Poly.to_alist alist) ~compare:(fun (x, _) (y, _) ->
        Int.compare x y)
  in
  String.concat_map_list ~sep:"\n" alist ~f:(fun (ai, label) ->
      let atom = t.aarr.(ai) in
      sprintf "%d (%d): %s" ai label (ExAtom.str_of atom))

let str_of_table t (qlist, alist) =
  let qlist = List.sort qlist ~compare:Int.compare in
  let alist =
    List.sort (Map.Poly.to_alist alist) ~compare:(fun (x, _) (y, _) ->
        Int.compare x y)
  in
  if List.is_empty alist then ""
  else
    String.concat_map_list ~sep:"\n" qlist ~f:(fun qi ->
        String.concat_map_list alist ~f:(fun (ai, _) ->
            str_of_res t.cells.{qi, ai}))

let str_of_table_transposed t (qlist, alist) =
  let qlist = List.sort qlist ~compare:Int.compare in
  let alist =
    List.sort (Map.Poly.to_alist alist) ~compare:(fun (x, _) (y, _) ->
        Int.compare x y)
  in
  if List.is_empty alist then ""
  else
    String.concat_map_list ~sep:"\n" alist ~f:(fun (ai, _) ->
        String.concat_map_list qlist ~f:(fun qi -> str_of_res t.cells.{qi, ai}))

let str_of (Ident.Pvar name, t) (qlist, alist) =
  let reduced_qlist = reduced_qlist_of t (qlist, alist) in
  sprintf "===== %s =====\n" name
  ^ sprintf "qualifiers (%d):\n%s\n" (List.length qlist) (str_of_quals t qlist)
  ^ sprintf "atoms (%d):\n%s\n" (Map.Poly.length alist) (str_of_atoms t alist)
  ^ sprintf "table:\n%s\n" (str_of_table t (qlist, alist))
  ^
  if List.length reduced_qlist = List.length qlist then ""
  else
    sprintf "reduced qualifiers (%d):\n%s\n"
      (List.length @@ reduced_qlist)
      (str_of_quals t reduced_qlist)

let str_of_map t (qlist, alist) =
  Hashtbl.Poly.fold t ~init:"" ~f:(fun ~key ~data ret ->
      ret ^ "\n" ^ str_of (key, data) (qlist, alist))
