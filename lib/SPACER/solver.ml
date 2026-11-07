(* Backend that solves a CHC problem with Spacer, Z3's fixedpoint engine, run
   in-process through the Z3 library.  The problem is preprocessed, refused
   unless every predicate has the ordinary kind and every clause has at most
   one positive literal, and registered as fixedpoint rules; the headless
   clauses become one query.  Z3's [unsat] for the query is the problem's
   [Sat]: the answer it prints is decoded into a predicate solution (a
   predicate the answer does not define gets [true]) and, with
   [check_validity] or when a conjunct of the answer could not be read,
   re-checked clause by clause.  Z3's [sat] is the problem's
   [Unsat], with the derivation Z3 prints as the refutation when it can be
   decoded.  A Z3 error becomes [Timeout] when it reports cancellation and
   [Unknown] otherwise, and is printed like any verdict. *)
open Core
open Common
open Common.Util
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open Preprocessing

module type SolverType = sig
  val solve :
    ?timeout:int option ->
    ?print_sol:bool ->
    PCSP.Problem.t ->
    PCSP.Problem.solution Or_error.t
end

(* With [COAR_SPACER_STATS] in the environment, every fixedpoint query prints
   one [spacer-stats:] line on stderr when it returns or raises: the wall
   clock spent before the query (preprocessing, context, rule conversion),
   the total, and Z3's fixedpoint statistics whose key names a count, a time
   or a depth (for instance [SPACER_num_lemmas]).  A caller solving many
   small problems (MuCyc's interpolation) can so count the inner solver's
   work per call.  Off, it is one boolean test per query. *)
let stats_on_stderr = Option.is_some (Sys.getenv "COAR_SPACER_STATS")

(* With [COAR_SPACER_DUMP=<dir>] in the environment, every fixedpoint query
   also writes the system exactly as Z3 receives it (Z3's fixedpoint syntax,
   as [Z3.Fixedpoint.to_string_q] prints it) to [<dir>/spacer_<pid>_<n>.smt2],
   [n] counting the queries of the process, so that the queries a caller
   asks (MuCyc's interpolation) can be replayed by the z3 binary with other
   options.  The solver's parameters are not written.  Observation only; off,
   it is one test per query. *)
let dump_dir = Sys.getenv "COAR_SPACER_DUMP"
let dump_count = Atomic.make 0

let dump_query text =
  match dump_dir with
  | None -> ()
  | Some dir ->
      let n = Atomic.fetch_and_add dump_count 1 in
      Out_channel.write_all
        (sprintf "%s/spacer_%d_%d.smt2" dir (Core_unix.getpid () |> Pid.to_int) n)
        ~data:text

let report_stats ~setup ~total solver =
  let ms span = Time_float.Span.to_ms span in
  let entries =
    List.filter_map
      (Z3.Statistics.get_entries (Z3.Fixedpoint.get_statistics solver))
      ~f:(fun e ->
        let k = Z3.Statistics.Entry.get_key e in
        if
          List.exists [ "num"; "time"; "max"; "lemma" ] ~f:(fun substring ->
              String.is_substring k ~substring)
        then
          Some
            (String.tr ~target:' ' ~replacement:'_' k
            ^ "="
            ^ Z3.Statistics.Entry.to_string_value e)
        else None)
  in
  prerr_endline
    (sprintf "spacer-stats: setup=%.1f total=%.1f %s" (ms setup) (ms total)
       (String.concat ~sep:" " entries))
(* A diagnostic, with COAR_SPACER_CENSUS set: one stderr line per query
   ([spacer-census:]) with the process id, the clause form's shape as handed
   to Z3 (clauses, goals, unknowns, tree nodes, and the same counts for the
   clauses a goal's derivability depends on), the seconds spent in this
   backend's preprocessing, its clausal form, the conversion to Z3 and the
   query (the query including the decoding of an answer), the outcome, and
   Z3's own timing statistics.  It reads nothing back into the solve: the
   statistics are read after the query returned or raised. *)
module Census = struct
  let on () = Option.is_some (Sys.getenv "COAR_SPACER_CENSUS")

  let nodes (cs : Ast.Clause.t list) =
    List.sum (module Int) cs ~f:(fun (_, ps, ns, phi) ->
        Ast.Logic.Term.ast_size phi
        + Set.sum (module Int) ps ~f:Ast.Logic.Term.ast_size
        + Set.sum (module Int) ns ~f:Ast.Logic.Term.ast_size)

  let shape cls =
    let cs = Set.to_list cls in
    match Ast.ChcCone.analyse cs with
    | None -> sprintf "clauses=%d nodes=%d non-horn" (List.length cs) (nodes cs)
    | Some (kept, _, _, st) ->
        sprintf "%s nodes=%d cone_nodes=%d" (Ast.ChcCone.str_of_stats st)
          (nodes cs) (nodes kept)

  let report ~shape ~times ~stats outcome =
    let zstats =
      try
        let st = stats () in
        Z3.Statistics.get_entries st
        |> List.filter_map ~f:(fun e ->
               let k = Z3.Statistics.Entry.get_key e in
               if
                 String.is_prefix k ~prefix:"time"
                 || String.is_substring k ~substring:"SPACER num queries"
                 || String.is_substring k ~substring:"SPACER max depth"
               then
                 Some
                   (sprintf "%s=%s"
                      (String.map k ~f:(fun c -> if Char.(c = ' ') then '_' else c))
                      (Z3.Statistics.Entry.to_string_value e))
               else None)
        |> String.concat ~sep:" "
      with e when not (Common.Timer.is_async e) -> "stats-unavailable"
    in
    eprintf "spacer-census: pid=%d %s %s outcome=%s z3: %s\n%!"
      (Core_unix.getpid () |> Pid.to_int)
      shape
      (String.concat ~sep:" "
         (List.map times ~f:(fun (k, v) -> sprintf "t_%s=%.2f" k v)))
      outcome zstats
end

(* Spacer's lemmas carried from one solve to the next solve of a
   STRENGTHENING of the same system: a system over the same predicates whose
   every clause instance is an instance of a clause of the first one (for
   example, the first system with some body atoms guarded by disequalities).

   Why it is sound.  A lemma Spacer holds for predicate [P] at level [k]
   over-approximates the [P]-facts derivable by derivations of height at most
   [k] (at the infinity level, by every derivation).  A strengthening derives
   no fact the original does not, at no smaller height, so each lemma remains
   an over-approximation for it, and seeding the new solve with it
   ([Z3.Fixedpoint.add_cover] before the first query of a fresh fixedpoint
   object, which Spacer inherits into the predicate transformers it builds
   for that query) excludes nothing the new system derives.  A counterexample
   the seeded solve returns is still a derivation Spacer has replayed
   concretely; the lemmas only prune the search, which is what the carry is
   for: asking the strengthened system from nothing re-learns them.  Z3
   itself keeps a fixedpoint object's lemmas across queries only when every
   rule of the new query is subsumed by an old one, which the fresh query
   predicate Z3 makes per query never is, so carrying them is done by hand.

   Contract: the caller turns capturing on ([capturing]), takes the last
   capture together with the problem it was made from ([take_for], by
   physical equality, so an intervening solve of anything else yields
   nothing), and seeds the next solve with it ([seed_next]) only when that
   solve's problem is a strengthening of the captured one.  Every solve
   consumes the seed and drops the previous capture, so a capture never
   outlives the next solve and a seed is never applied twice.  Process-global
   and not domain-safe: it serves a caller that asks one solve at a time. *)
module Carry = struct
  type t = {
    src : PCSP.Problem.t;
    (* per lemma: the predicate's declaration, the level (-1 for infinity),
       and the lemma over the predicate's arguments as de Bruijn variables,
       all in the context [ctx] they were read from *)
    covers : (Z3.FuncDecl.func_decl * int * Z3.Expr.expr) list;
    ctx : Z3.context;
  }

  let capturing = ref false
  let last : t option ref = ref None
  let seed : t option ref = ref None

  let take_for pcsp =
    match !last with
    | Some c when phys_equal c.src pcsp ->
        last := None;
        Some c
    | _ -> None

  let seed_next c = seed := c
  let size c = List.length c.covers

  (* diagnostics of the last solve: lemmas added from a seed, and the
     seconds the capture after it took (0 when none was made) *)
  let last_seeded = ref 0
  let last_capture_secs = ref 0.
end

(* [read_answer phi]: the predicate definitions read off the conjuncts of
   Spacer's answer [phi], and the conjuncts read as none, in the answer's
   order.  A conjunct is read as a definition when, under its universal
   quantifiers, it is [P(xs) = body] with every free variable of [body]
   among [xs], [P(xs)] or [not P(xs)] with [xs] variables (distinct for the
   last two); a conjunct that is [true] is dropped.  The map is not a
   solution: a predicate it leaves out, or one whose conjunct was
   unreadable, is constrained by nothing read here. *)
let read_answer phi =
  let unreadable = ref [] in
  (* [P(xs)] or [not P(xs)] over distinct variables [xs]: the
     definition of [P] is the constant [b] *)
  let constant_definition phi' =
    let atom, b =
      if Formula.is_neg phi' then
        (fst @@ Formula.let_neg phi', false)
      else (phi', true)
    in
    if not (Formula.is_atom atom) then None
    else
      let atom, _ = Formula.let_atom atom in
      if not (Atom.is_pvar_app atom) then None
      else
        let pvar, _, args, _ = Atom.let_pvar_app atom in
        if not (List.for_all args ~f:Term.is_var) then None
        else
          let params = List.map args ~f:(Term.let_var >> fst) in
          if
            List.contains_dup params ~compare:(fun (x, _) (y, _) ->
                Ident.tvar_compare x y)
          then None
          else
            Some
              ( Ident.pvar_to_tvar pvar,
                Logic.ExtTerm.mk_lambda
                  (Logic.of_old_sort_env_list params)
                  (Logic.BoolTerm.mk_bool b) )
  in
  let sol =
    Map.of_set_exn
    @@ Set.Poly.filter_map (Formula.conjuncts_of phi)
         ~f:(fun phi ->
           let _, phi' = Formula.rm_quant ~forall:true phi in
           if Formula.is_true phi' then None
           else
             match constant_definition phi' with
             | Some def -> Some def
             | None ->
             try
               let lhs, rhs, _ = Formula.let_eq phi' in
               let pvar, params =
                 let pvar, _, args, _ =
                   Atom.let_pvar_app @@ fst @@ Formula.let_atom
                   @@ T_bool.let_formula lhs
                 in
                 (pvar, List.map args ~f:(Term.let_var >> fst))
               in
               let body =
                 if Term.is_var rhs then
                   Formula.mk_atom
                   @@ Atom.mk_pvar_app
                        (Ident.tvar_to_pvar @@ fst @@ fst
                       @@ Term.let_var rhs)
                        [] []
                 else if T_bool.is_formula rhs then
                   Formula.aconv_tvar @@ T_bool.let_formula rhs
                 else failwith @@ Term.str_of rhs
               in
               (* A body variable other than the parameters is a constant
                  Spacer made itself: it grounds every variable of a rule
                  that occurs only in the rule's constraint as a fresh
                  [aux!N] constant of the head's transformer, and a lemma
                  learnt from that rule can keep it, so the answer prints it
                  free ([aux!N_0]) with no interpretation in the model.  It
                  stands for the rule's witness, which is existential: for
                  [I(y) <= y = x*x], [bot <= I(y) /\ y < 0] Spacer answers
                  [I(y) = y - aux*aux > -1], a solution read as
                  [exists aux] ([y >= 0]) and a non-solution read as
                  [forall aux] (false for every [y]), which was returned as
                  [sat].  Such a definition is read as none, so the caller
                  checks the solution completed with [true].  It is not
                  returned closed existentially, although that reading is a
                  solution here: the existential is Spacer's exact
                  (strongest) answer, an interpolating caller that accepts it
                  stores frames that grow by one step a round, and one
                  that otherwise interpolated a counterexample bound lost
                  its answer that way. *)
               if
                 not
                   (Set.is_subset (Formula.term_sort_env_of body)
                      ~of_:(Set.Poly.of_list params))
               then failwith "a free constant of Spacer's own";
               Option.return
                 ( Ident.pvar_to_tvar pvar,
                   Logic.ExtTerm.mk_lambda
                     (Logic.of_old_sort_env_list params)
                     (Logic.ExtTerm.of_old_formula body) )
             with exn_ when not (Common.Timer.is_async exn_) ->
               unreadable := phi :: !unreadable;
               None)
  in
  (sol, List.rev !unreadable)

(* [complete_with_true exi_senv sol]: [sol] with every predicate of
   [exi_senv] it does not define mapped to [true].  The result is a solution
   only if those predicates are unconstrained enough for [true]; nothing here
   checks it. *)
let complete_with_true exi_senv sol =
  Map.force_merge sol
  @@ Map.Poly.filter_mapi exi_senv ~f:(fun ~key ~data ->
         if Map.Poly.mem sol key then None
         else
           let args, _ = Logic.Sort.args_ret_of data in
           Some
             (Logic.ExtTerm.mk_lambda
                (Logic.sort_env_list_of_sorts args)
             @@ Logic.BoolTerm.mk_bool true))

(* [solution_valid ~timeout ~undecided_valid ~on_undecided pcsp sol]: whether
   every clause of [pcsp] with [sol] substituted is valid, asked of Z3 one
   clause at a time with [timeout] (milliseconds, [None] for none).  A clause
   Z3 does not decide (it answers unknown or runs out of time) calls
   [on_undecided] and counts as valid exactly when [undecided_valid]; with
   [undecided_valid = false], [true] is a proof that [sol] is a solution.  A
   timeout of the caller's own budget propagates. *)
let solution_valid ~timeout ~undecided_valid ~on_undecided pcsp sol =
  PCSP.Problem.check_valid
    (fun uni_senv t ->
      let phi =
        Logic.ExtTerm.to_old_fml (PCSP.Problem.senv_of pcsp) uni_senv t
      in
      try
        Z3Smt.Z3interface.is_valid_exn ~timeout ~id:None (FunEnv.mk_empty ())
          phi
      with Z3Smt.Z3interface.Unknown ->
        on_undecided ();
        undecided_valid)
    pcsp sol

module Make (Cfg : Config.ConfigType) : SolverType = struct
  let config = Cfg.config

  let preprocessor =
    let open Or_error in
    ExtFile.unwrap config.preprocessor >>= fun cfg -> Ok (Preprocessor.make cfg)

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let mk_solver ?timeout_ms ctx =
    let solver = Z3.Fixedpoint.mk_fixedpoint ctx in
    let params = Z3.Params.mk_params ctx in
    (* a query in a reused context ([Carry]) carries its own budget, which
       Z3 reads before the context's *)
    Option.iter timeout_ms ~f:(fun ms ->
        Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") ms);
    Z3.Params.add_symbol params
      (Z3.Symbol.mk_string ctx "engine")
      (Z3.Symbol.mk_string ctx "spacer");
    (*Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "spacer.use_inductive_generalizer") false;*)
    if config.cex_needed then
      Z3.Params.add_bool params
        (Z3.Symbol.mk_string ctx "xform.subsumption_checker")
        false;
    if config.solution_needed || config.cex_needed then (
      Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "print_answer") true;
      (* xform.slice, xform.inline_linear, and xform.inline_eager need to be disabled to obtain a sound solution from SPACER *)
      Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "xform.slice") false;
      Z3.Params.add_bool params
        (Z3.Symbol.mk_string ctx "xform.inline_linear")
        false;
      Z3.Params.add_bool params
        (Z3.Symbol.mk_string ctx "xform.inline_eager")
        false);
    Z3.Params.add_bool params
      (Z3.Symbol.mk_string ctx "spacer.native_mbp")
      config.use_z3_native_mbp;
    (* With global guidance off nothing is set, so Z3's own default applies,
       which is [spacer.global = false].  The last arm is kept compiled but
       never runs, on purpose: it was a commented-out block before it was
       turned into code, and it has never been active.  Running it would set
       [spacer.global] to the value it already has and switch off the three
       [spacer.gg.*] options, which Z3's parameter list describes as parts of
       global guidance, so it is expected to change nothing while guidance is
       off; that expectation is not measured, which is why the arm stays
       unreachable rather than being switched on. *)
    (* With guidance on, [gg_concretize = false] switches off its
       concretizing step alone (conjecture and subsume stay at Z3's default,
       on); [true] adds nothing, so Z3's default (on) applies as it did
       before the field existed. *)
    if config.enable_global_guidance then (
      Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "spacer.global") true;
      if not config.gg_concretize then
        Z3.Params.add_bool params
          (Z3.Symbol.mk_string ctx "spacer.gg.concretize")
          false)
    else if true then ()
    else (
      Z3.Params.add_bool params
        (Z3.Symbol.mk_string ctx "spacer.gg.concretize")
        false;
      Z3.Params.add_bool params
        (Z3.Symbol.mk_string ctx "spacer.gg.conjecture")
        false;
      Z3.Params.add_bool params
        (Z3.Symbol.mk_string ctx "spacer.gg.subsume")
        false;
      Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "spacer.global") false);
    Option.iter config.blast_term_ite_inflation ~f:(fun n ->
        Z3.Params.add_int params
          (Z3.Symbol.mk_string ctx "spacer.blast_term_ite_inflation")
          n);
    (* A non-empty [xform_options] says exactly which transformations run:
       the named ones on, the other known ones off (Z3's defaults turn all
       four on whenever nothing above turned them off).  [Config.check_xforms]
       has refused the field unless nothing is read back ([verdict_only]). *)
    if not (List.is_empty config.xform_options) then
      List.iter Config.known_xforms ~f:(fun x ->
          Z3.Params.add_bool params
            (Z3.Symbol.mk_string ctx ("xform." ^ x))
            (List.mem config.xform_options x ~equal:String.equal));
    (*Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "xform.elim_term_ite") true;*)
    if config.enable_z3_validation then
      Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "validate") true;
    (*Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "print_fixedpoint_extensions") false;*)
    Debug.print
    @@ lazy ("Z3 fixedpoint parameters: " ^ Z3.Params.to_string params);
    Z3.Fixedpoint.set_parameters solver params;
    solver

  let solve ?(timeout = None) ?(print_sol = false) pcsp =
    (* let module Printer = Printer.Solver.Make (struct
           let config =
             {
               Printer.Config.preprocessor =
                 Instance (Preprocessor.Config.make false false 4 0 true);
               Printer.Config.homc_sat =
                 HOMCSat.
                   {
                     verbose = false;
                     solver = Filename "./config/solver/horsat2.json";
                     encode_bool_ops = false;
                   };
               Printer.Config.sat_format = Printer.Config.String;
               Printer.Config.smt_format = Printer.Config.SMT2;
               Printer.Config.lts_format = Printer.Config.PCSP;
               add_missing_forall = false;
             }
         end)
       in
       print_endline @@ Printer.string_of_pcsp pcsp; *)
    let open Or_error in
    let started = Time_float.now () in
    preprocessor >>= fun (module Preprocessor) ->
    let census = Census.on () in
    (* [Carry]: this solve consumes the seed and drops the last capture *)
    let pcsp_in = pcsp in
    let seed = !Carry.seed in
    Carry.seed := None;
    Carry.last := None;
    Carry.last_seeded := 0;
    Carry.last_capture_secs := 0.;
    let t_start = Common.PhaseTime.now () in
    let _, pcsp =
      Preprocessor.preprocess ~purpose:Preprocessing.Preprocessor.Purpose.decide
        pcsp
    in
    let t_pre = Common.PhaseTime.now () in
    let timeout_ms =
      match (config.timeout_ms, timeout) with
      | None, None -> None
      | Some ms, _ -> Some ms
      | None, Some timeout ->
          (* the caller's budget is in seconds *)
          Some (timeout * 1000)
    in
    let ctx =
      match seed with
      | Some (c : Carry.t) ->
          (* [Carry]: the seed's lemmas are expressions of the context they
             were read from, so the seeded query is asked in that context
             rather than translating them into a fresh one *)
          c.ctx
      | None ->
      let options =
        match timeout_ms with
        | None -> []
        | Some ms -> [ ("timeout", string_of_int ms) ]
      in
      (* Each call makes a context of its own and drops it on return, and a
         dropped context's native memory -- the whole Spacer state of a query
         that ran out of its budget among it -- is released only when the
         collector finalises the OCaml value, which a small OCaml heap delays.
         A caller that asks check after check (MuStrat's strategy checks, their
         copy-blind and doubled-budget retries) then holds every earlier
         query's memory at once: one game reached 3.5 GB of Z3 allocation
         over four queries, and a collection at its end brought it back to
         0.2 GB.  So collect before making a context once the native part of
         the resident set (the OCaml heap excluded) has grown by the
         synthesizer's threshold since the last collection;
         the queries are the same, only the collector's timing changes. *)
      Z3Smt.Z3interface.full_major_if_resident_grew ();
      Z3.mk_context options
    in
    let solver =
      if Option.is_some seed then mk_solver ?timeout_ms ctx else mk_solver ctx
    in
    (* This backend solves CHC only, and `-p chc`, `-p pfwcsp`, `-p dqchc` … are
       all the *same* problem constructor (the name documents the input, nothing
       checks it), so the compatibility table cannot refuse the pairing: the
       check has to happen here.  It used to be a bare [assert], which told the
       operator nothing but a file and a line. *)
    (* Every kind but [Ord] states an obligation the clauses do not: a
       non-empty predicate may not be false everywhere, a disjunctively
       well-founded one may not contain a self loop, and so on.  This engine
       reads the clauses and nothing else, so it can only honour [Ord].
       Listing the kinds to REFUSE, which is what this used to do, left the
       ones nobody thought of accepted: only well-founded and functional were
       named, so a disjunctively well-founded or non-empty predicate was
       converted to an ordinary Horn relation with its obligation dropped, and
       both fixtures that violate it came back sat.  Naming the one kind that
       IS supported cannot go stale that way. *)
    PCSP.Problem.refuse_non_ord_kinds ~backend:"SPACER" pcsp;
    let pcsp = PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf pcsp in
    let t_cnf = Common.PhaseTime.now () in
    let census_shape =
      if census then Census.shape (PCSP.Problem.clauses_of pcsp) else ""
    in
    (* [lift_sol]: the identity, or under [cone_of_influence] the extension
       of a solution of the cone to every unknown of [pcsp] *)
    let pcsp, lift_sol =
      if not config.cone_of_influence then (pcsp, Fn.id)
      else
        match
          Ast.ChcCone.analyse (Set.to_list (PCSP.Problem.clauses_of pcsp))
        with
        | None -> (pcsp, Fn.id)
        | Some (kept, derivable, _, st) ->
            Debug.print
            @@ lazy ("cone of influence: " ^ Ast.ChcCone.str_of_stats st);
            let kept_pvs =
              List.fold kept ~init:Set.Poly.empty ~f:(fun s c ->
                  Set.union s
                    (Set.union (Ast.ChcCone.heads c) (Ast.ChcCone.bodies c)))
            in
            let senv =
              Map.Poly.filter (PCSP.Problem.senv_of pcsp) ~f:(fun s ->
                  Logic.BoolTerm.is_bool_sort (Logic.Sort.ret_of s))
            in
            ( PCSP.Problem.of_clauses
                ~params:
                  {
                    (PCSP.Problem.params_of pcsp) with
                    PCSP.Params.stable_clauses = Set.Poly.empty;
                  }
                (Set.Poly.of_list kept),
              fun sol ->
                Map.force_merge
                  (Map.Poly.filter_keys sol ~f:(fun k -> not (Map.Poly.mem senv k)))
                  (Ast.ChcCone.lift ~derivable ~kept_pvs ~senv sol) )
    in
    (* The same refusal for a clause with more than one positive literal: a
       Horn engine has no rule for a disjunctive head.  Decided here, once,
       with the count, rather than by a [failwith] inside the conversion of
       the offending clause, which surfaced as a backtrace six clauses into
       the input on six of the 41 tracked ADT files. *)
    (let disjunctive =
       Set.count (PCSP.Problem.clauses_of pcsp) ~f:(fun (_, ps, _, _) ->
           Set.length ps > 1)
     in
     if disjunctive > 0 then
       failwith
       @@ sprintf
            "Spacer solves Horn clauses only, but %d clause(s) of this problem \
             have a disjunctive head (more than one positive literal).  Use \
             PCSat."
            disjunctive);
    Debug.print @@ lazy ("input:\n" ^ PCSP.Problem.str_of pcsp);
    let fenv = PCSP.Problem.fenv_of pcsp in
    let exi_senv = PCSP.Problem.senv_of pcsp in
    let dtenv =
      (* Register every datatype the clauses mention, not only the declared
         ones, the way the SMT path does ([z3_dtenv_of_formula]).  A declared
         [List T] and its instance [List X] in the clauses are different
         names; a sort the converter does not find in this environment it
         mints on the fly and forgets, so the variables of the rules ended up
         in one Z3 datatype and the selectors' accessors in another, and Z3's
         Horn engine rejected the rule with "Uninterpreted 'tl'": 20 of the 41
         tracked ADT inputs answered nothing. *)
      Set.fold
        (PCSP.Problem.formulas_of pcsp)
        ~init:
          (Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx @@ PCSP.Problem.dtenv_of pcsp)
        ~f:(fun dtenv (uni_senv, term) ->
          Z3Smt.Z3interface.z3_dtenv_of_formula ~init:dtenv ctx
          @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv term)
    in
    (*let query_name = "__query__" in
      let exi_senv =
      Map.Poly.add_exn exi_senv ~key:(Ident.Tvar query_name) ~data:Logic.BoolTerm.SBool
      in*)
    let penv =
      List.map (Map.Poly.to_alist @@ exi_senv)
        ~f:(fun (Ident.Tvar name, sort) ->
          ( Ident.Pvar name,
            let arg_sorts =
              List.map (Logic.Sort.args_of sort)
                ~f:
                  (Logic.ExtTerm.to_old_sort
                  >> Z3Smt.Z3interface.of_sort ctx dtenv)
            in
            let symbol = Z3.Symbol.mk_string ctx name in
            Z3.FuncDecl.mk_func_decl ctx symbol arg_sorts
              (Z3.Boolean.mk_sort ctx) ))
    in
    (* With [query_as_relation], the goal clauses become rules into one
       fresh nullary relation, which is then the query.  The name differs
       from every unknown, so the relation never meets the answer's
       consumers: it is removed from the solution below. *)
    let query_rel =
      if not config.query_as_relation then None
      else
        let rec fresh i =
          let name = if i = 0 then "__query__" else sprintf "__query__%d" i in
          if Map.Poly.mem exi_senv (Ident.Tvar name) then fresh (i + 1)
          else name
        in
        let name = fresh 0 in
        Some
          ( name,
            Z3.FuncDecl.mk_func_decl ctx (Z3.Symbol.mk_string ctx name) []
              (Z3.Boolean.mk_sort ctx) )
    in
    let penv =
      match query_rel with
      | None -> penv
      | Some (name, decl) -> (Ident.Pvar name, decl) :: penv
    in
    List.iter penv ~f:(snd >> Z3.Fixedpoint.register_relation solver);
    (* One converter for every clause, so the recursive functions of [fenv]
       (among them the size function of each datatype the problem mentions)
       are declared in [ctx] once.  Converting each clause with its own
       [of_formula] declared them again per clause, which Z3 5.x refuses with
       "recursive function ... already defined" and 4.x let pass. *)
    let of_formula =
      Z3Smt.Z3interface.formula_converter ~id:None (*ToDo*) ctx penv fenv dtenv
    in
    let convert_all f =
      if config.flat_and_or then Z3Smt.Z3interface.with_flat_and_or f else f ()
    in
    (* the decoding of an answer (a solution, or a refutation's derivation),
       sharing what Z3 shares when [share_answer_decoding] is set *)
    let decode f =
      Common.PhaseTime.with_phase "spacer-decode" @@ fun () ->
      if config.share_answer_decoding then
        Z3Smt.Z3interface.with_shared_decoding f
      else f ()
    in
    let qs =
      convert_all @@ fun () ->
      PCSP.Problem.clauses_of pcsp
      |> Set.Poly.filter_map ~f:(fun (uni_senv, ps, ns, phi) ->
             let phi =
               Formula.aconv_tvar
               @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi
             in
             (*print_endline @@ "a: " ^ Formula.str_of phi;*)
             let senv, phi =
               (* assume that [phi] is alpha-renamed *)
               Formula.elim_let_equivalid
               @@ Normalizer.normalize_let ~rename:true phi
             in
             (*print_endline @@ "b: " ^ Formula.str_of phi;*)
             let uni_senv =
               Map.force_merge uni_senv @@ Logic.of_old_sort_env_map senv
             in
             let body =
               Formula.and_of
               @@ Formula.mk_neg phi
                  :: (Set.to_list
                     @@ Set.Poly.map ns
                          ~f:
                            (Logic.ExtTerm.to_old_atm exi_senv uni_senv
                            >> Formula.mk_atom))
             in
             let head =
               Formula.or_of @@ Set.to_list
               @@
               match Set.length ps with
               | 0 -> (
                   match query_rel with
                   | None -> Set.Poly.empty
                   | Some (name, _) ->
                       Set.Poly.singleton @@ Formula.mk_atom
                       @@ Atom.mk_pvar_app (Ident.Pvar name) [] [])
               (*Set.Poly.singleton @@ Atom.mk_pvar_app query_name [] []*)
               | 1 ->
                   Set.Poly.map ps
                     ~f:
                       (Logic.ExtTerm.to_old_atm exi_senv uni_senv
                       >> Formula.mk_atom)
               | _ -> failwith "head disjunction not supported"
             in
             (*print_endline @@ "c: " ^ Formula.str_of @@ Formula.mk_imply body head;*)
             let quantified_senv, phi' =
               Formula.rm_quant ~forall:true @@ Formula.mk_imply body head
             in
             (*print_endline @@ "d: " ^ Formula.str_of phi';*)
             let senv =
               Map.Poly.to_alist
               @@ Map.force_merge_list
                    [
                      Logic.to_old_sort_env_map uni_senv;
                      Map.of_set_exn quantified_senv;
                    ]
             in
             if Set.is_empty ps && Option.is_none query_rel then (
               (*print_endline @@ LogicOld.str_of_sort_env_map LogicOld.Term.str_of_sort @@ Map.Poly.of_alist_exn senv;*)
               let phi' =
                 (*Formula.aconv_tvar @@*)
                 Formula.forall senv phi'
               in
               let c =
                 of_formula [] (*senv*) phi'
               in
               Debug.print
               @@ lazy
                    ("adding query: "
                    ^ Formula.str_of (Evaluator.simplify_neg phi'));
               (*print_endline @@ Z3.Expr.to_string c;*)
               Some (Z3.Boolean.mk_not ctx c))
             else
               let phi' =
                 (*Formula.aconv_tvar @@*)
                 Formula.forall senv phi'
               in
               let c =
                 of_formula [] (*senv*) phi'
               in
               Debug.print
               @@ lazy
                    ("adding rule: " ^ Formula.str_of (Evaluator.simplify phi'));
               (*print_endline @@ Z3.Expr.to_string c;*)
               Z3.Fixedpoint.add_rule solver c None;
               None)
    in
    (if false then
       (* make smt string *)
       let prefix = ref "" in
       let inputs =
         let reg_assert = Str.regexp "^(assert \\(.*\\)$" in
         let reg_forall = Str.regexp "^(forall " in
         Z3.Fixedpoint.to_string solver
         |> String.split_on_chars ~on:[ '\n' ]
         |> List.map ~f:(fun line ->
                if Str.string_match reg_assert line 0 then
                  let matched_str = Str.matched_group 1 line in
                  let line' = !prefix in
                  line'
                  ^
                  if not @@ Str.string_match reg_forall matched_str 0 then (
                    prefix := ")\n";
                    "(assert (forall () " ^ matched_str)
                  else (
                    prefix := "";
                    line)
                else line)
       in
       let reg_anno = Str.regexp "(! \\| :weight.*[0-9])" in
       let inputs =
         List.map inputs ~f:(fun s -> Str.global_replace reg_anno "" s)
       in
       let inputs = inputs @ [ !prefix ] in
       (* let inputs = inputs @ if !exists_query then [ sprintf "(assert (forall ((M Bool)) (not (%s))))" query_name ] else [] in *)
       let inputs = inputs @ [ "(check-sat)" ] in
       (* let inputs = if config.produce_proofs then
           "(set-option :produce-proofs true)" :: inputs @ ["(get-proof)"]
          else inputs in *)
       let inputs = inputs @ [ "(exit)" ] in
       print_endline @@ String.concat ~sep:"\n" inputs);
    (* [Carry]: the seed's lemmas, each on a predicate this solve declares
       identically (the same Z3 declaration in the shared context; a sort
       declared anew, such as a datatype, makes another declaration, and its
       lemmas are skipped); a lemma Z3 refuses is skipped too, which only
       leaves the search less pruned *)
    Option.iter seed ~f:(fun (c : Carry.t) ->
        List.iter c.covers ~f:(fun (decl, level, lemma) ->
            if List.exists penv ~f:(fun (_, d) -> Z3.FuncDecl.equal d decl)
            then
              try
                Z3.Fixedpoint.add_cover solver level decl lemma;
                incr Carry.last_seeded
              with Z3.Error _ -> ()));
    let capture () =
      let t0 = Common.PhaseTime.now () in
      (try
         let covers =
           List.concat_map penv ~f:(fun (_, decl) ->
               let at level =
                 match Z3.Fixedpoint.get_cover_delta solver level decl with
                 | Some e when not (Z3.Boolean.is_true e) -> [ (decl, level, e) ]
                 | _ -> []
               in
               at (-1)
               @ List.concat_map
                   (List.init (Z3.Fixedpoint.get_num_levels solver decl)
                      ~f:Fn.id)
                   ~f:at)
         in
         Carry.last := Some { Carry.src = pcsp_in; covers; ctx }
       with Z3.Error _ -> Carry.last := None);
      Carry.last_capture_secs := Common.PhaseTime.now () -. t0
    in
    let t_conv = Common.PhaseTime.now () in
    let report outcome =
      if census then
        Census.report ~shape:census_shape
          ~times:
            [
              ("pre", t_pre -. t_start);
              ("cnf", t_cnf -. t_pre);
              ("conv", t_conv -. t_cnf);
              ("query", Common.PhaseTime.now () -. t_conv);
            ]
          ~stats:(fun () -> Z3.Fixedpoint.get_statistics solver)
          outcome
    in
    try
      Debug.print @@ lazy "********************";
      if Option.is_some dump_dir then
        dump_query (Z3.Fixedpoint.to_string_q solver (Set.to_list qs));
      (* The system exactly as Z3 receives it, in Z3's fixedpoint syntax, so
         that a run of the z3 binary on it can be set beside this answer. *)
      Debug.print
      @@ lazy
           ("Z3 fixedpoint input:\n"
           ^ Z3.Fixedpoint.to_string_q solver (Set.to_list qs));
      let solution =
        let rec loop () =
          let res =
            try
              (if not stats_on_stderr then fun query -> query ()
               else fun query ->
                 let setup = Time_float.diff (Time_float.now ()) started in
                 Stdlib.Fun.protect query ~finally:(fun () ->
                     report_stats ~setup
                       ~total:(Time_float.diff (Time_float.now ()) started)
                       solver))
              @@ fun () ->
              match query_rel with
              | Some (_, decl) ->
                  (* the relation query with the runtime lock released, so
                     that a termination signal is handled while Spacer runs *)
                  Z3Released.fixedpoint_query_r solver [ decl ]
              | None ->
                  (* the query with the runtime lock released, so that a
                     termination signal is handled while Spacer runs *)
                  Z3Released.fixedpoint_query solver
                    (if Set.is_singleton qs then Set.choose_exn qs
                     else Z3.Boolean.mk_or ctx @@ Set.to_list qs)
              (*Z3.Fixedpoint.query_r solver
                      [List.Assoc.find_exn penv ~equal:Stdlib.(=) (Ident.Pvar query_name)]*)
            with Z3.Error reason -> raise (Z3.Error reason)
          in
          match res with
          | Z3.Solver.UNSATISFIABLE when config.verdict_only ->
              (* No answer is read: the empty map is no solution, and a
                 caller of a verdict-only solver uses only the verdict. *)
              Debug.print @@ lazy "Unsatisfiable! (verdict only)";
              PCSP.Problem.Sat Map.Poly.empty
          | Z3.Solver.SATISFIABLE when config.verdict_only ->
              Debug.print @@ lazy "Satisfiable! (verdict only)";
              PCSP.Problem.Unsat None
          | Z3.Solver.UNSATISFIABLE -> (
              Debug.print @@ lazy "Unsatisfiable!";
              match Z3.Fixedpoint.get_answer solver with
              | Some expr ->
                  (*let expr = Z3.Expr.simplify expr None in*)
                  Debug.print
                  @@ lazy ("Z3 solution: " ^ Z3.Expr.to_string expr);
                  (* Spacer's solution may use an operator this tree has no
                     term for: Z3 writes a sequence read as [seq.nth_i] (the
                     read at an in-range index) or [seq.nth_u] (the
                     uninterpreted value of a read out of range), and neither
                     is [seq.nth] at every index, so no exact decoding exists.
                     A solution that cannot be read back is no solution here,
                     and the answer is [unknown]: reporting [sat] without a
                     solution would be unchecked, and an exception would lose
                     the verdict.  A timeout raised while the answer is
                     converted belongs to the caller's budget and propagates;
                     turned into a failure it once ended a MuStrat run as an
                     uncaught exception. *)
                  begin match
                    try
                      Ok
                        (decode (fun () ->
                             Z3Smt.Z3interface.formula_of ctx [] penv dtenv
                               expr))
                    with
                    | Failure err -> Error err
                    | Z3.Error err -> Error ("Z3: " ^ err)
                    | e when not (Common.Timer.is_async e) ->
                        Error (Exn.to_string e)
                  with
                  | Error err ->
                      Debug.print
                      @@ lazy
                           ("Spacer's solution cannot be read back (answering \
                             unknown): " ^ err);
                      PCSP.Problem.Unknown
                  | Ok phi ->
                  (*Debug.print @@ lazy ("answer: " ^ Formula.str_of phi);*)
                  (* The conjuncts of the answer that could not be read as a
                     predicate's definition.  A predicate left without a
                     definition is filled with [true] below, which is a
                     solution only if [true] happens to be one -- a predicate
                     Spacer defined as [false] (written [forall xs. not P(xs)])
                     became [true], and the problem was answered [sat] with a
                     model violating its clauses.  So when any conjunct is
                     unreadable the completed solution is checked against every
                     clause whatever [check_validity] says, a clause whose
                     validity is undecided counts as violated whatever
                     [conservative_check] says, and a failed check answers
                     [unknown]: the answer is [sat] only with a solution proved
                     valid. *)
                  let sol, unreadable = read_answer phi in
                  let partial = not (List.is_empty unreadable) in
                  if partial then
                    Debug.print
                    @@ lazy
                         ("unreadable conjuncts in Spacer's solution (checking \
                           the solution completed with true): "
                         ^ String.concat ~sep:"; "
                             (List.map unreadable ~f:Formula.str_of));
                  let sol =
                    match query_rel with
                    | None -> sol
                    | Some (name, _) -> Map.Poly.remove sol (Ident.Tvar name)
                  in
                  let sol = complete_with_true exi_senv sol in
                  (*Debug.print @@ lazy ("SyGuS solution: " ^ PCSP.Problem.str_of_sygus_solution @@ PCSP.Problem.Sat sol);*)
                  Debug.print
                  @@ lazy
                       (CandSol.str_of @@ CandSol.make
                       @@ Map.Poly.mapi sol ~f:(fun ~key ~data ->
                              (Map.Poly.find_exn exi_senv key, data)));
                  if
                    (config.check_validity || partial)
                    && not
                       @@ solution_valid
                            (* a completed partial solution can carry the
                               quantified bodies Spacer wrote, so its check is
                               bounded, 5 s per clause *)
                            ~timeout:(if partial then Some 5000 else None)
                            ~undecided_valid:
                              ((not partial) && not config.conservative_check)
                            ~on_undecided:(fun () ->
                              Debug.print
                              @@ lazy
                                   "a solution returned by Spacer could be \
                                    wrong")
                            pcsp sol
                  then
                    if partial then (
                      (* Spacer's own answer may be right in the conjuncts
                         that were dropped; solving again would read it the
                         same way *)
                      Debug.print
                      @@ lazy
                           "the solution completed with true is not a \
                            solution (answering unknown)";
                      PCSP.Problem.Unknown)
                    else if config.solve_again_if_invalid then (
                      Debug.print
                      @@ lazy "the solution returned by Spacer is wrong";
                      loop ())
                    else (
                      (* Spacer's [unsat] stands, but without a checked
                         solution this backend cannot certify [sat]; an
                         exception here ended the run with no verdict *)
                      Debug.print
                      @@ lazy
                           "the solution returned by Spacer is wrong \
                            (answering unknown)";
                      PCSP.Problem.Unknown)
                  else (
                    if partial then
                      Debug.print
                      @@ lazy "the solution completed with true is valid";
                    PCSP.Problem.Sat (lift_sol sol))
                  end
              | None ->
                  (* the same reading as an unreadable solution: no solution,
                     no [sat] *)
                  Debug.print
                  @@ lazy "no solution returned by Spacer (answering unknown)";
                  PCSP.Problem.Unknown)
          | Z3.Solver.SATISFIABLE -> (
              Debug.print @@ lazy "Satisfiable!";
              if !Carry.capturing then capture ();
              match Z3.Fixedpoint.get_answer solver with
              | Some expr ->
                  Debug.print @@ lazy ("Spacer model: " ^ Z3.Expr.to_string expr);
                  let phi =
                    try
                      let phi =
                        decode (fun () ->
                            Z3Smt.Z3interface.formula_of ctx
                              (Map.Poly.to_alist
                              @@ Logic.to_old_sort_env_map exi_senv)
                              penv dtenv expr)
                      in
                      Debug.print @@ lazy ("model: " ^ Formula.str_of phi);
                      Ok phi
                    with
                    | Failure err ->
                        Error err
                    | Z3.Error reason -> Error ("Z3: " ^ reason)
                    | e when not (Common.Timer.is_async e) ->
                        Error (Exn.to_string e)
                  in
                  (* The verdict is Spacer's derivation of the query; the
                     formula only describes that derivation.  Where it uses an
                     operator this tree cannot read (Z3's [seq.nth_i] and
                     [seq.nth_u] for sequence reads), the verdict stands and the
                     description is dropped, as when Spacer gives none. *)
                  begin match phi with
                  | Ok phi -> PCSP.Problem.Unsat (Some (PCSP.Problem.Formula phi))
                  | Error err ->
                      Debug.print
                      @@ lazy
                           ("Spacer's counterexample cannot be read back \
                             (kept the verdict, dropped the counterexample): "
                          ^ err);
                      PCSP.Problem.Unsat None
                  end
              | None -> PCSP.Problem.Unsat None)
          | Z3.Solver.UNKNOWN -> PCSP.Problem.Unknown
        in
        loop ()
      in
      Debug.print @@ lazy "********************";
      report
        (match solution with
        | PCSP.Problem.Sat _ -> "sat"
        | Unsat _ -> "unsat"
        | Unknown -> "unknown"
        | Timeout -> "timeout"
        | _ -> "other");
      if print_sol then print_endline (PCSP.Problem.str_of_solution solution);
      Or_error.return solution
    with Z3.Error reason ->
      report ("z3error:" ^ reason);
      (* The -p pcsp dispatch relies on this function to print the verdict
         ([~print_sol:true]) and discards the value it returns, so a verdict
         decided here and not printed reaches nobody: the process exits 0
         with nothing on stdout, indistinguishable from a crash or a timeout
         to every sweep that reads the first line.  Print it, the way the
         success path does. *)
      let solution =
        if String.(reason = "spacer canceled" || reason = "canceled") then
          PCSP.Problem.Timeout
        else (
          Debug.print @@ lazy (sprintf "Z3 Error: %s" reason);
          PCSP.Problem.Unknown (* Or_error.error_string reason*))
      in
      if print_sol then print_endline (PCSP.Problem.str_of_solution solution);
      Or_error.return solution
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
