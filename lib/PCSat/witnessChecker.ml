open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open PCSatCommon

(* Re-verification of PCSat's answer, run when [PCSat.Config.check_solution]
   is set (the dbg_ configs do; the default configs do not, because the cost
   is one Z3 call per clause on [sat] and one per recorded example on
   [unsat]).  A [sat] answer is checked against the *original* problem, an
   [unsat] witness against the preprocessed clauses it refers to.  Nothing here
   trusts the solver: instances are re-derived from the recorded substitution
   with the pipeline the validator used, unit propagation is re-run, the
   labeling problem is re-encoded propositionally and given to Z3, kind lemmas
   are checked against their side condition. *)

type outcome = Passed | Failed of string | Unchecked of string

type report = {
  passed : int;
  failed : string list;
  unchecked : (string * int) list;  (** reason, count *)
  kinds : (string * int) list;
      (** kind constraints re-verified, by kind name (a passed check of a kind
          or of a certificate family), so that a summary shows which kinds a run
          actually exercised *)
}

let empty = { passed = 0; failed = []; unchecked = []; kinds = [] }

let add r = function
  | Passed -> { r with passed = r.passed + 1 }
  | Failed msg -> { r with failed = msg :: r.failed }
  | Unchecked why ->
      let n =
        Option.value ~default:0
          (List.Assoc.find r.unchecked ~equal:String.equal why)
      in
      {
        r with
        unchecked = List.Assoc.add r.unchecked ~equal:String.equal why (n + 1);
      }

(* a passed kind check, tallied under [kind] as well *)
let passed_kind r kind =
  let n =
    Option.value ~default:0 (List.Assoc.find r.kinds ~equal:String.equal kind)
  in
  let r = add r Passed in
  { r with kinds = List.Assoc.add r.kinds ~equal:String.equal kind (n + 1) }

let str_of_report what r =
  sprintf "(%s-check (passed %d) (unchecked %d) (failed %d)%s%s%s)" what
    r.passed
    (List.sum (module Int) r.unchecked ~f:snd)
    (List.length r.failed)
    (if List.is_empty r.kinds then ""
     else
       sprintf "\n (kinds%s)"
         (String.concat_map_list (List.rev r.kinds) ~sep:"" ~f:(fun (k, n) ->
              sprintf " (%s %d)" k n)))
    (String.concat_map_list r.unchecked ~sep:"" ~f:(fun (why, n) ->
         sprintf "\n (unchecked %S %d)" why n))
    (String.concat_map_list r.failed ~sep:"" ~f:(fun msg ->
         sprintf "\n (FAILED %S)" msg))

let timeout = Some 5000

(* Every read of a sequence concatenation is split by index before a formula
   is handed to Z3 here: [nth (a ++ b) j] becomes an [ite] over whether [j]
   falls in [a], in [b], or in neither, and the third branch keeps the original
   read, so the rewritten formula is equivalent to the original in EVERY model
   of the sequence theory, including the value the theory leaves open for an
   out-of-range read.  The question asked is therefore the same question, and
   the rewrite is applied unconditionally rather than following the switch that
   makes the validator do the same: a checker that asks the validator's
   question in a form the solver decides less often reports "undecided" on a
   step it could have confirmed, and with the switch off the rewrite changes
   no answer either -- only whether one is found.  Z3 was observed to answer
   neither way about a read of a concatenation under a quantified hypothesis
   over the parts, where the split form is decided at once.  Formulas that
   read no sequence are returned untouched, so no other query changes shape.
   One query is deliberately left as it is: the guard decision in
   [check_instance] re-makes, on the unrewritten guard, the decision a sound
   derivation makes, and it has to come out the same way for the re-derivation
   to match, which includes coming out undecided where the derivation's did. *)
let split_seq_reads phi =
  if
    Set.exists (Formula.funsyms_of phi) ~f:(function
      | T_seq.SqNth _ -> true
      | _ -> false)
  then Evaluator.rewrite_seq_read_over_concat phi
  else phi

(* ---- sat: the model satisfies every original constraint ---- *)

(* A second attempt at a constraint the solver left undecided, used only to
   PASS it: when it reads a sequence under a quantifier -- a solution read back
   from sequence cells is a universal over a sequence's positions, one per
   sequence, and a constraint composing three of them was left undecided by
   the unrewritten query -- it is asked through its instantiated forms
   ([SeqInstantiation.prove_valid_deep]), each quantifier-free and each
   implying the constraint.  An unsatisfiable negated form proves the
   constraint valid; anything else leaves it unchecked, since a countermodel of
   a form is not one of the constraint.  So this can turn "undecided" into
   "passed" and never into "failed".  A form that states a whole sequence in
   a premise ([t != seq.store s i 0] as a disjunct) is also asked with that
   sequence substituted and its reads split by index
   ([SeqInstantiation.frame_forms]), each implying the form: the frame
   constraint of a write, read back so, was left undecided at 10 s as the
   plain form.  Each form gets [instance_timeout]
   rather than the checker's own budget: a form the validator proved in 3.4 s
   on a loaded machine was left undecided here at 5 s.  The instances each
   form is built from are bounded by [instance_max_nodes] nodes per
   instantiation step: the budgets above bound the solver, not the building,
   and nested sequence existentials multiply their instances, so on a
   Rust-derived map clause one form grew past ten million nodes and the check
   exhausted memory before asking anything.  A bounded form is still a
   strengthening, so the bound can only leave a constraint unchecked.  The
   number is a choice, not a measurement: on that input, forms far larger were
   built and each was left undecided by the solver at its budget, so a larger
   form mostly buys a longer wait.

   The attempt as a whole stops asking once [instance_stage_budget_s] seconds
   of wall clock have passed since it began: the budgets above bound each
   question, not how many are asked, and a constraint with several pieces and
   several forms per piece can be asked a dozen forms of a million nodes each,
   every one taking its full budget and more on a loaded machine (one
   constraint of a Rust-derived map clause spent 76 s here and was proved by
   none of its forms).  The check is made before each question, so a question
   already asked runs to its own budget.  Stopping early only leaves the
   constraint to the next attempt or unchecked; it never passes or fails
   anything.  The number is a choice: it admits three such forms.

   Nor is a constraint of more than [instance_large_nodes] nodes attempted:
   its forms are built from copies of its pieces, so with the constraint
   itself at half of [instance_max_nodes] the node budget leaves room for
   little more than one instance per binder, and building such a form is
   itself unbounded in time -- on a Rust-derived map clause of about 200,000
   and 390,000 nodes one form took 82 s and 153 s to build, before the stage
   budget above could be consulted, and no form of any constraint of that
   input was proved.  The threshold is a choice; skipping leaves the
   constraint to the next attempt.

   [matched], when [Some (aligned, hyp_budget)], also asks the pieces'
   matched-instance forms ([SeqInstantiation.matched_forms]; with [aligned],
   the forms that take the constraint's other, already proved pieces as
   hypotheses aligned with the piece), in the rounds
   [SeqInstantiation.prove_valid_deep] describes: the forms by which the
   zero-unknown verdict proves a clause when its matched-instance switch is
   on.  Without them a constraint the verdict proved that way stayed
   undecided here whatever budget the stage was given (600 s instead of
   30 s, 30 s a form instead of 10), since none of the deep forms is the
   question the verdict answered.  To be the verdict's question in shape
   too, the constraint is first rewritten as the verdict rewrites a clause
   -- the equations defining a variable substituted
   ([Evaluator.subst_var_definitions]), which a preprocessor would have
   removed, the sequence definitions and the reads of concatenations split,
   then the one-point and splitting rewrites -- each preserving validity, so
   the question is the same one; and each form is asked as the verdict asks
   one: in a context of its own told only the definitions the form reaches
   (Z3 falls back to a weaker tactic in a context holding any recursive
   definition, and the pooled one holds every definition), a form refused
   for its shape or left undecided being handed to the sequence-axiom
   fallback, which can only prove it.  The first round asks each form for
   [matched_first_timeout], the later ones for [instance_timeout], all
   within the stage budget above.  Only a proof is read, and a piece used
   as a hypothesis has itself been proved before the constraint passes.

   [ladder], the coordinator configuration of the solve being checked, sets
   the instantiation's process-wide switches before any form is built.
   Their module defaults are [false] while several configuration defaults
   are [true], so without it the stage built the forms of whatever setter
   last ran in the process: a different set of forms, and a different
   verdict on a constraint only those forms prove, depending on whether a
   zero-unknown verdict or the Houdini pre-pass had run before the check.
   Absent, the switches are left as they are (the callers that set them
   themselves). *)
let instance_timeout = Some 10000
let matched_first_timeout = Some 2000
let instance_max_nodes = 200_000
let instance_stage_budget_s = 30.
let instance_large_nodes = instance_max_nodes / 2

exception Instance_budget_spent

let valid_by_instances ?(seq_as_array = false) ?matched ?ladder
    ?(budget_s = instance_stage_budget_s) ~id phi =
  (not (Formula.is_quantifier_free phi))
  && Set.exists (Formula.funsyms_of phi) ~f:(function
       | T_seq.SqNth _ -> true
       | _ -> false)
  && Formula.ast_size phi <= instance_large_nodes
  &&
  let () =
    Option.iter ladder ~f:(fun c ->
        Coordination.Coordinator.LadderSwitches.set c)
  in
  let fenv = get_fenv () in
  let deadline = Common.Clock.now_s () +. budget_s in
  let check_deadline () =
    if Float.(Common.Clock.now_s () >= deadline) then
      raise Instance_budget_spent
  in
  let ask form =
    check_deadline ();
    if Z3Smt.Z3interface.may_not_return form then `Undecided
    else
      match
        try
          (if seq_as_array then Z3Smt.Z3interface.check_sat_seq_as_array
           else Z3Smt.Z3interface.check_sat)
            ~timeout:instance_timeout ~id fenv
            [ Formula.nnf_of (Formula.negate form) ]
        with e when not (Common.Timer.is_interrupt e) -> `Unknown (Exn.to_string e)
      with
      | `Unsat -> `Valid
      | `Sat m -> `Invalid m
      | _ -> `Undecided
  in
  (* a form asked as the zero-unknown verdict asks one (see above) *)
  let ask_as_verdict timeout form =
    check_deadline ();
    let fenv' = Z3Smt.Z3interface.fenv_reached_by fenv form in
    let answer =
      if Z3Smt.Z3interface.may_not_return form then
        `Unknown "not asked: the solver may not return on this shape"
      else
        try
          match
            (if seq_as_array then Z3Smt.Z3interface.check_sat_seq_as_array
             else Z3Smt.Z3interface.check_sat)
              ~timeout ~fresh_solver:true ~id fenv'
              [ Formula.nnf_of (Formula.negate form) ]
          with
          | `Unsat -> `Valid
          | `Sat m -> `Invalid m
          | res -> res
        with e when not (Common.Timer.is_interrupt e) -> `Unknown (Exn.to_string e)
    in
    match
      try
        Z3Smt.Z3interface.with_seq_axiom_fallback ~caller_timeout:timeout ~id
          fenv' form answer
      with e when not (Common.Timer.is_interrupt e) -> answer
    with
    | `Valid -> `Valid
    | `Invalid m -> `Invalid m
    | _ -> `Undecided
  in
  (* a range question for the read-over-write split of [frame_forms]: linear
     arithmetic over lengths, decided at once or not worth waiting for *)
  let check_valid goal =
    match
      try
        Z3Smt.Z3interface.check_valid ~timeout:(Some 1000) ~id fenv goal
      with e when not (Common.Timer.is_interrupt e) -> `Unknown (Exn.to_string e)
    with
    | `Valid -> true
    | _ -> false
  in
  let also =
    SeqInstantiation.frame_forms
      ~entails:(SeqInstantiation.range_entails ~check_valid)
  in
  match
    match matched with
    | None ->
        SeqInstantiation.prove_valid_deep ~max_nodes:instance_max_nodes ~also
          ~ask phi
    | Some _ ->
        SeqInstantiation.prove_valid_deep ~max_nodes:instance_max_nodes ~also
          ?matched ~rewrite_matched:Evaluator.elim_onepoint_and_split_binders
          ~ask:(ask_as_verdict matched_first_timeout)
          ~ask_long:(ask_as_verdict instance_timeout)
          (Evaluator.elim_onepoint_and_split_binders
          @@ Evaluator.split_seq_reads_for_validity
          @@ Evaluator.subst_var_definitions phi)
  with
  | `Valid -> true
  | `Unproved _ -> false
  | exception Instance_budget_spent -> false

(* A third attempt at a constraint the solver left undecided, used only to
   PASS it, after [valid_by_instances]; [PCSat.Config.retry_undecided_check_solution]
   selects it.  The negated constraint -- the very formula the first attempt
   asked, after the same substitution, simplification and read split, with no
   term the theory leaves open treated differently, so that the question is
   still whether the constraint holds in every model -- is asked
   - of Z3 under the tactic [(then simplify der qe-light simplify smt)]
     ([Z3interface.check_sat_by_elimination]), which eliminates a quantified
     variable an equation fixes and so decides constraints whose premise names
     the value of a quantified position.  In this process, in a context of its
     own, unless [Z3interface.may_not_return] refuses the shape (a quantifier
     over a sequence, whose call a budget does not bound); then as a separate
     [z3] process ([./z3] or [z3] on PATH), whose wall clock does bound it; and
   - of cvc5 ([./cvc5] or [cvc5] on PATH) with enumerative instantiation
     ([--enum-inst]).
   The two processes read Z3's own SMT-LIB2 printing of these assertions with
   reached definitions only. This is not generally the complete original
   defining context: omitted equations need not admit a model extension.
   Refutation of the relaxed context suffices to prove validity in the full
   context; Sat of the retry is never accepted as a full-context countermodel.
   Native recursive-definition enforcement remains a separate obligation.
   Each route is given [retry_budget_ms] (5 s) of its solver's own clock --
   Z3's [timeout] parameter, [z3 -T], cvc5's [--tlimit] -- and a process is
   also sent SIGTERM by the process clock two seconds later and SIGKILL one
   second after that.  An [unsat] proves the
   constraint valid: an SMT solver's [unsat] means no model of its theory
   satisfies the negation, whatever the theory leaves open (an out-of-range
   read, a division by zero, a selector off its constructor) being part of the
   model. That rests on faithful printing of the retained query in standard
   SMT-LIB2 (integers, reals, datatypes, arrays, sequences), followed by the
   refutation implication from the retained to the full context. It does not
   require the two contexts to have the same models. A symbol cvc5 does not
   know is a parse error, which
   reads as no answer.  [sat], [unknown], a timeout, a parse error or a crash
   leaves the constraint unchecked, never failed: a countermodel from a second
   solver is not checked against this tree's reading of the constraint.  On a
   satisfiable Rust-derived counter input every constraint the default query
   left undecided at 5 s was valid, one of them decided only by the tactic, in
   0.1 s. *)
let retry_budget_ms = 5000
let retry_file_count = Atomic.make 0

(* [true] iff [tool args FILE], FILE holding [text], prints [unsat] first *)
let unsat_by_process tool args text =
  let file =
    sprintf "temp_check_%s_p%d_%d.smt2" tool
      (Pid.to_int @@ Core_unix.getpid ())
      (Atomic.fetch_and_add retry_file_count 1)
  in
  Exn.protect
    ~finally:(fun () ->
      try Core_unix.unlink file
      with e when not (Common.Timer.is_async e) -> ())
    ~f:(fun () ->
      Out_channel.write_all file ~data:text;
      match
        Common.Util.Command.sync_command "timeout"
          ([
             (* SIGTERM alone did not stop cvc5 on a 4 MB question: the
                route took 35 s against the 7 s of this clock *)
             "-k";
             "1";
             Int.to_string ((retry_budget_ms / 1000) + 2);
             Common.Util.Command.resolve_tool tool;
           ]
          @ args @ [ file ])
          []
      with
      | first :: _ -> String.equal (String.strip first) "unsat"
      | [] -> false
      | exception e when not (Common.Timer.is_interrupt e) -> false)

let unsat_by_cvc5 text =
  unsat_by_process "cvc5"
    [ "--enum-inst"; sprintf "--tlimit=%d" retry_budget_ms ]
    (text ^ "(check-sat)\n")

let unsat_by_z3_process text =
  unsat_by_process "z3"
    [ sprintf "-T:%d" (retry_budget_ms / 1000) ]
    (text ^ "(check-sat-using (then simplify der qe-light simplify smt))\n")

let valid_by_stronger_routes ~id phi =
  let text = ref "" in
  let fenv = get_fenv () in
  let printed () = not (String.is_empty !text) in
  let by_cvc5 () = printed () && unsat_by_cvc5 !text in
  match
    Z3Smt.Z3interface.check_sat_by_elimination ~timeout:retry_budget_ms
      ~smtlib2_out:text ~id fenv
      [ split_seq_reads @@ Formula.negate phi ]
  with
  | `Unsat -> true
  | `Refused -> (printed () && unsat_by_z3_process !text) || by_cvc5 ()
  | _ -> by_cvc5 ()
  | exception e when not (Common.Timer.is_interrupt e) -> by_cvc5 ()

(* The kind constraints of [pcsp]'s predicates, checked on the solution [sol]
   and added to the report [r].  [certs] holds the kind certificates the
   template recorded for the accepted candidate; a WF/DWF/NWF/Parity predicate
   without one is reported unchecked, never failed.  Contract: raises nothing
   but an asynchronous exception, and decides nothing -- it only reports.
   Split out of [check_sat_solution] so that a caller holding a solution whose
   constraints it has already checked in its own way (a mid-level solver that
   accepts a PCSat answer) can ask for the kinds alone. *)
let check_kind_constraints ~id ?(certs = Map.Poly.empty) pcsp
    (sol : Logic.term_subst_map) r =
  let senv = PCSP.Problem.senv_of pcsp in
  let fenv = get_fenv () in
  (* kind constraints on the model: FN — functionality and totality, Tot —
     totality over its universal positions, decided by Z3 on the printed formula; WF/DWF need the
     ranking function the template used (a [KindCert.t]) and are reported as
     unchecked until one is recorded *)
  (* a kind check must never crash the run: a conversion failure (e.g. a
     term Z3's encoder does not support) is reported, not raised *)
  let valid phi =
    match
      try
        Ok
          (Z3Smt.Z3interface.check_sat ~timeout ~id fenv
             [ split_seq_reads @@ Formula.negate phi ])
      with e when not (Common.Timer.is_interrupt e) -> Error (Exn.to_string e)
    with
    | Ok `Unsat -> `Valid
    | Ok (`Sat _) -> `Invalid
    | Ok _ -> `Unknown
    | Error msg -> `Failed_to_check msg
  in
  let body_of pv =
    match Map.Poly.find sol pv with
    | None -> None
    | Some term -> (
        try
          let params, body = Logic.ExtTerm.let_lam term in
          let params =
            List.map params ~f:(fun (x, s) -> (x, Logic.ExtTerm.to_old_sort s))
          in
          Some
            ( params,
              (* the internal term may still hold the template's piecewise
                 [case] selectors; the evaluator folds them (the printer does
                 the same), Z3's encoder does not accept them *)
              Evaluator.simplify
              @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
                   (Map.Poly.of_alist_exn
                      (List.map params ~f:(fun (x, s) ->
                           (x, Logic.ExtTerm.of_old_sort s))))
                   body )
        with exn_ when not (Common.Timer.is_async exn_) -> None)
  in
  (* A side must be a function of its own arguments and the shared prefix.
     Containment in a comparison between expressions depending on both
     states does not establish well-foundedness, even if that comparison
     has the expected number of levels. *)
  let ranking_support_error (cert : KindCert.ranking) =
    let params = KindCert.params_of cert in
    if
      Set.length (Set.Poly.of_list (List.map params ~f:fst))
      <> List.length params
    then Some "duplicate ranking parameters"
    else
      let check_side which params pieces =
        let allowed = Set.Poly.of_list (List.map params ~f:fst) in
        let used =
          Set.Poly.union_list
            (List.concat_map pieces ~f:(fun (disc, rs) ->
                 Formula.fvs_of disc :: List.map rs ~f:Term.fvs_of))
        in
        if Set.is_subset used ~of_:allowed then None
        else
          Some
            (sprintf "%s ranking uses variables outside its shared and side parameters"
               which)
      in
      List.find_map cert.levels ~f:(fun (px, py) ->
          match check_side "left" (cert.params_shared @ cert.params_x) px with
          | Some why -> Some why
          | None -> check_side "right" (cert.params_shared @ cert.params_y) py)
  in
  (* the meta-theorem behind the decrease check needs one ranking
     function per tag — the left side of every certificate of a P_{t,_} and
     the right side of every certificate of a P_{_,t} must be the same
     function of the tag's arguments (for WF/DWF, the two sides of the one
     certificate).  Each side is renamed to canonical arguments and the
     candidates of a tag are compared semantically, piece by piece. *)
  let check_families r =
    (* The same fresh name denotes an argument position on every side.
       Avoid bound names too: [Formula.rename] does not avoid capture under
       a discriminator's binders. *)
    let max_arity, taken =
      Map.Poly.fold certs ~init:(0, Set.Poly.empty)
        ~f:(fun ~key:_ ~data:cert (max_arity, taken) ->
          List.fold cert ~init:(max_arity, taken)
            ~f:(fun (max_arity, taken) (rk : KindCert.ranking) ->
              let max_arity =
                max max_arity
                  (List.length rk.params_shared
                  + max (List.length rk.params_x) (List.length rk.params_y))
              in
              let taken =
                Set.union taken
                  (Set.Poly.of_list (List.map (KindCert.params_of rk) ~f:fst))
              in
              let taken =
                List.fold rk.levels ~init:taken ~f:(fun taken (px, py) ->
                    List.fold (px @ py) ~init:taken ~f:(fun taken (disc, rs) ->
                        Set.Poly.union_list
                          (taken :: Formula.tvs_of disc
                          :: List.map rs ~f:Term.tvs_of)))
              in
              (max_arity, taken)))
    in
    let taken = ref taken in
    let canonical =
      List.init max_arity ~f:(fun _ ->
          let x =
            Ident.mk_fresh_tvar_avoiding ~prefix:"#arg"
              ~taken:(Set.mem !taken) ()
          in
          taken := Set.add !taken x;
          x)
    in
    let side_of (cert : KindCert.ranking) which =
      let ps =
        match which with
        | `X -> cert.params_shared @ cert.params_x
        | `Y -> cert.params_shared @ cert.params_y
      in
      let arg k = List.nth_exn canonical k in
      let ren =
        Map.Poly.of_alist_exn (List.mapi ps ~f:(fun k (x, _) -> (x, arg k)))
      in
      let canon = List.mapi ps ~f:(fun k (_, s) -> (arg k, s)) in
      ( canon,
        List.map cert.levels ~f:(fun (px, py) ->
            List.map
              (match which with `X -> px | `Y -> py)
              ~f:(fun (d, rs) ->
                (Formula.rename ren d, List.map rs ~f:(Term.rename ren)))) )
    in
    let groups =
      Map.Poly.fold certs ~init:Map.Poly.empty
        ~f:(fun ~key:pv ~data:(cert : KindCert.t) groups ->
          if List.exists cert ~f:(fun rk -> Option.is_some (ranking_support_error rk))
          then groups
          else
          let name = Ident.name_of_tvar in
          (* each ranking of a union is its own family of one; a member of an
             NWF/Parity family must be a single ranking (checked above) *)
          List.foldi cert ~init:groups ~f:(fun idx groups rk ->
              let keys =
                match PCSP.Problem.kind_of pcsp pv with
                | (Kind.NWF (nwf, (l, rr)) | Kind.Parity (nwf, (l, rr)))
                  when List.length cert = 1 ->
                    [
                      (name nwf.Kind.name ^ "/" ^ name l, `X);
                      (name nwf.Kind.name ^ "/" ^ name rr, `Y);
                    ]
                | Kind.WF | Kind.DWF ->
                    let k = sprintf "%s#%d" (name pv) idx in
                    [ (k, `X); (k, `Y) ]
                | _ -> []
              in
              List.fold keys ~init:groups ~f:(fun groups (key, which) ->
                  Map.Poly.add_multi groups ~key
                    ~data:(pv, which, side_of rk which))))
    in
    let same_pieces p0 p1 =
      if List.length p0 <> List.length p1 then Formula.mk_false ()
      else
        Formula.and_of
        @@ List.map2_exn p0 p1 ~f:(fun (d0, r0) (d1, r1) ->
            Formula.and_of
              (Formula.mk_imply d0 d1 :: Formula.mk_imply d1 d0
              ::
              (if List.length r0 <> List.length r1 then [ Formula.mk_false () ]
               else List.map2_exn r0 r1 ~f:Formula.eq)))
    in
    Map.Poly.fold groups ~init:r ~f:(fun ~key:tag ~data:sides r ->
        match List.rev sides with
        | [] | [ _ ] -> r
        | (pv0, w0, (canon0, lv0)) :: rest ->
            let side w = match w with `X -> "left" | `Y -> "right" in
            List.fold rest ~init:r ~f:(fun r (pv1, w1, (canon1, lv1)) ->
                let where =
                  sprintf "the %s side of %s and the %s side of %s" (side w0)
                    (Ident.name_of_tvar pv0) (side w1) (Ident.name_of_tvar pv1)
                in
                if List.length canon0 <> List.length canon1 then
                  add r
                    (Unchecked
                       (sprintf
                          "ranking functions of tag %s have different arities \
                           (%s)"
                          tag where))
                else
                  (* a member records the levels its own left tag's priority
                     compares, so two members of a family may record
                     different numbers of levels; the tag's ranking function
                     must agree on the levels both record *)
                  let k = min (List.length lv0) (List.length lv1) in
                  let same =
                    Formula.and_of
                      (List.map2_exn (List.take lv0 k) (List.take lv1 k)
                         ~f:same_pieces)
                  in
                  match valid (Formula.forall canon0 same) with
                  | `Valid -> passed_kind r "family"
                  | `Invalid ->
                      add r
                        (Failed
                           (sprintf
                              "ranking functions of tag %s differ between %s: \
                               the certificates do not form one family"
                              tag where))
                  | `Unknown ->
                      add r
                        (Unchecked
                           (sprintf
                              "Z3 undecided on the equality of the ranking \
                               functions of tag %s"
                              tag))
                  | `Failed_to_check msg ->
                      add r
                        (Unchecked
                           (sprintf
                              "Z3 could not compare the ranking functions of \
                               tag %s: %s"
                              tag msg))))
  in
  (* Functionality compares the relation with a copy whose distinguished
     output is independent.  The copy is a binder, so it must avoid every
     name in the body (including nested binders) and every parameter: a
     textual [y#2] can already be a legal input name. *)
  let fresh_output_copy params phi (y, ys) =
    let taken =
      Set.union (Formula.tvs_of phi)
        (Set.Poly.of_list (List.map params ~f:fst))
    in
    let y2 =
      Ident.mk_fresh_tvar_avoiding
        ~prefix:(Ident.name_of_tvar y ^ "#") ~taken:(Set.mem taken) ()
    in
    ((y2, ys), Formula.rename (Map.Poly.singleton y y2) phi)
  in
  Map.Poly.fold senv ~init:r ~f:(fun ~key:pv ~data:_ r ->
      match PCSP.Problem.kind_of pcsp pv with
      | Kind.Ord -> r
      | Kind.FN -> (
          match body_of pv with
          | None ->
              add r
                (Unchecked
                   (sprintf "FN predicate %s without a solution"
                      (Ident.name_of_tvar pv)))
          | Some (params, phi) -> (
              let ins = List.drop_last_exn params in
              let y, ys = List.last_exn params in
              let y2, phi2 = fresh_output_copy params phi (y, ys) in
              let functional =
                Formula.forall (params @ [ y2 ])
                  (Formula.mk_imply (Formula.mk_and phi phi2)
                     (Formula.eq (Term.mk_var y ys) (Term.mk_var (fst y2) ys)))
              in
              let total = Formula.forall ins (Formula.exists [ (y, ys) ] phi) in
              let r =
                match valid functional with
                | `Valid -> passed_kind r "FN"
                | `Invalid ->
                    add r
                      (Failed
                         (sprintf "FN solution of %s is not functional: %s"
                            (Ident.name_of_tvar pv) (Formula.str_of phi)))
                | `Unknown ->
                    add r (Unchecked "Z3 undecided on FN functionality")
                | `Failed_to_check msg ->
                    add r
                      (Unchecked ("Z3 could not check FN functionality: " ^ msg))
              in
              match valid total with
              | `Valid -> passed_kind r "FN"
              | `Invalid ->
                  add r
                    (Failed
                       (sprintf "FN solution of %s is not total: %s"
                          (Ident.name_of_tvar pv) (Formula.str_of phi)))
              | `Unknown -> add r (Unchecked "Z3 undecided on FN totality")
              | `Failed_to_check msg ->
                  add r (Unchecked ("Z3 could not check FN totality: " ^ msg))))
      | Kind.Uniq (j, _) -> (
          (* single-valuedness at position [j] only; a Uniq predicate owes no
             totality *)
          match body_of pv with
          | None ->
              add r
                (Unchecked
                   (sprintf "Uniq predicate %s without a solution"
                      (Ident.name_of_tvar pv)))
          | Some (params, phi) -> (
              let y, ys = List.nth_exn params j in
              let y2, phi2 = fresh_output_copy params phi (y, ys) in
              let functional =
                Formula.forall (params @ [ y2 ])
                  (Formula.mk_imply (Formula.mk_and phi phi2)
                     (Formula.eq (Term.mk_var y ys) (Term.mk_var (fst y2) ys)))
              in
              match valid functional with
              | `Valid -> passed_kind r "Uniq"
              | `Invalid ->
                  add r
                    (Failed
                       (sprintf "Uniq solution of %s is not single-valued at %d: %s"
                          (Ident.name_of_tvar pv) j (Formula.str_of phi)))
              | `Unknown -> add r (Unchecked "Z3 undecided on Uniq single-valuedness")
              | `Failed_to_check msg ->
                  add r
                    (Unchecked ("Z3 could not check Uniq single-valuedness: " ^ msg))))
      | Kind.Tot u -> (
          match body_of pv with
          | None ->
              add r
                (Unchecked
                   (sprintf "Tot predicate %s without a solution"
                      (Ident.name_of_tvar pv)))
          | Some (params, phi) -> (
              (* forall (positions in u). exists (the others). phi: with no
                 universal position this is the closed non-emptiness query and
                 has no alternation *)
              let us, vs =
                List.partition_tf (List.mapi params ~f:(fun i p -> (i, p)))
                  ~f:(fun (i, _) -> List.mem u i ~equal:Int.equal)
              in
              let obligation =
                Formula.forall (List.map us ~f:snd)
                  (Formula.exists (List.map vs ~f:snd) phi)
              in
              match valid obligation with
              | `Valid -> passed_kind r "Tot"
              | `Invalid ->
                  add r
                    (Failed
                       (sprintf "Tot solution of %s is not total: %s"
                          (Ident.name_of_tvar pv) (Formula.str_of phi)))
              | `Unknown -> add r (Unchecked "Z3 undecided on totality")
              | `Failed_to_check msg ->
                  add r (Unchecked ("Z3 could not check totality: " ^ msg))))
      | (Kind.WF | Kind.DWF | Kind.NWF _ | Kind.Parity _) as kind -> (
          (* the solution must be contained in the decrease relation of the
             recorded ranking certificate.  The shape the
             certificate must have follows from the kind, not from the
             certificate: one level for WF/DWF/NWF; for Parity as many levels
             as the truncation of the left tag's priority, accepting iff the
             priority itself -- not its truncation -- is in the accepting set
             (Kura & Unno, Def. 7.8) *)
          let kind_name = Kind.short_str_of kind in
          let expected =
            match kind with
            | Kind.Parity (nwf, (tag_l, _)) -> (
                match Map.Poly.find nwf.Kind.sigma tag_l with
                | Some p ->
                    Some (nwf.Kind.trunc p, Set.mem nwf.Kind.acc_set p)
                | None -> None)
            | _ -> Some (1, false)
          in
          match (body_of pv, Map.Poly.find certs pv, expected) with
          | None, _, _ ->
              add r
                (Unchecked
                   (sprintf "%s predicate %s without a solution" kind_name
                      (Ident.name_of_tvar pv)))
          | Some (_, phi), None, _ when Formula.is_false phi ->
              (* the empty relation satisfies every one of these kinds *)
              passed_kind r (kind_name ^ " (empty)")
          | Some _, None, _ ->
              add r
                (Unchecked
                   (sprintf
                      "%s predicate %s: no ranking-function certificate \
                       recorded (solution not produced by its template?)"
                      kind_name (Ident.name_of_tvar pv)))
          | Some _, Some _, None ->
              add r
                (Unchecked
                   (sprintf
                      "%s predicate %s: the priority of its left tag is unknown"
                      kind_name (Ident.name_of_tvar pv)))
          | Some (params, phi), Some cert, Some (nlevels, accepting) -> (
              let shape (n, acc) =
                sprintf "%d level(s), %saccepting" n
                  (if acc then "" else "non-")
              in
              let bad_shape =
                List.find_map cert ~f:(fun (rk : KindCert.ranking) ->
                    match ranking_support_error rk with
                    | Some why ->
                        Some
                          (sprintf "%s predicate %s: malformed ranking certificate: %s"
                             kind_name (Ident.name_of_tvar pv) why)
                    | None ->
                    if
                      List.length rk.levels <> nlevels
                      || Bool.(rk.accepting <> accepting)
                    then
                      Some
                        (sprintf
                           "%s predicate %s: certificate has %s but the kind \
                            requires %s"
                           kind_name (Ident.name_of_tvar pv)
                           (shape (List.length rk.levels, rk.accepting))
                           (shape (nlevels, accepting)))
                    else if
                      List.length (KindCert.params_of rk) <> List.length params
                    then
                      Some
                        (sprintf
                           "%s predicate %s: certificate arity %d, solution \
                            arity %d"
                           kind_name (Ident.name_of_tvar pv)
                           (List.length (KindCert.params_of rk))
                           (List.length params))
                    else None)
              in
              (* a union of rankings certifies only DWF: a finite union of
                 well-founded relations is disjunctively well-founded, not
                 well-founded *)
              let union_ok =
                match kind with
                | Kind.DWF -> not (List.is_empty cert)
                | _ -> List.length cert = 1
              in
              if not union_ok then
                add r
                  (Unchecked
                     (sprintf
                        "%s predicate %s: certificate is a union of %d \
                         rankings, which certifies only DWF"
                        kind_name (Ident.name_of_tvar pv) (List.length cert)))
              else
                match bad_shape with
                | Some msg -> add r (Unchecked msg)
                | None -> (
                    let dec =
                      Formula.or_of
                      @@ List.map cert ~f:(fun rk ->
                          let ren =
                            Map.Poly.of_alist_exn
                              (List.map2_exn (KindCert.params_of rk) params
                                 ~f:(fun (c, _) (p, _) -> (c, p)))
                          in
                          Formula.rename ren (KindCert.dec_of_ranking rk))
                    in
                    match
                      valid (Formula.forall params (Formula.mk_imply phi dec))
                    with
                    | `Valid -> passed_kind r kind_name
                    | `Invalid ->
                        add r
                          (Failed
                             (sprintf
                                "%s solution of %s is not contained in the \
                                 decrease relation of its certificate: %s / %s"
                                kind_name (Ident.name_of_tvar pv)
                                (Formula.str_of phi) (KindCert.str_of cert)))
                    | `Unknown ->
                        add r
                          (Unchecked
                             (sprintf "Z3 undecided on the %s decrease"
                                kind_name))
                    | `Failed_to_check msg ->
                        add r
                          (Unchecked
                             (sprintf "Z3 could not check the %s decrease: %s"
                                kind_name msg)))))
      | _ -> add r (Unchecked "kind constraint not re-checked (other kind)"))
  |> check_families

(* The wall clock the constraints of one solution are checked within.  Each
   question the checker asks has a budget of its own, but a solution with a
   hundred constraints, each left undecided by the first query and then asked
   through its instantiated forms and two further solvers, adds those budgets
   up: on a Rust-derived map clause of 98 assertions the check ran past
   twenty minutes on a loaded machine, so the run printed its answer and no
   report.  Once the budget is spent, the constraints not yet asked are
   reported unchecked with the reason "checker budget spent", and a
   constraint whose first query is undecided is not asked again; nothing is
   passed or failed on that account.  The kind constraints are still checked
   afterwards.  The number is a choice. *)
let sat_check_budget_s = 240.

(* The size, counted as a tree, past which a constraint is not substituted
   and asked but reported unchecked.  A solution recovered by predicate
   elimination is built by substituting one recorded definition into the
   next, which shares the substituted term physically wherever its predicate
   occurred: small in memory, while its tree -- which the substitution, the
   conversion to the first-order representation, the simplifier and the
   solver all walk -- doubles with each link of a chain of such definitions.
   On a Rust-derived problem whose 220 eliminated predicates form chains of
   that kind, one definition took minutes to convert and the next ones twice
   as long each, so the check printed nothing within ten minutes; a constraint
   mentioning such a definition cannot be checked in any budget.  The bound
   is a choice, set well above the largest constraint the checker has been
   seen to pass after substitution (a few hundred thousand nodes). *)
let sat_check_max_nodes = 2_000_000

(* [substituted_size_up_to cap sizes phi] is the size, as a tree, that [phi]
   has once each variable [x] of [sizes]'s domain is replaced by a term of
   [sizes x] nodes, counted up to [cap] and [cap + 1] beyond it.  It is an
   estimate of the substituted constraint and not its exact size: a
   parameter of a definition is replaced by its argument, which it counts
   once, and a binder shadowing a key is not looked at.  It costs time in
   proportion to its result, never to the substituted term's. *)
let substituted_size_up_to cap (sizes : (Ident.tvar, int) Map.Poly.t) phi =
  let exception Over in
  let n = ref 0 in
  let bump k =
    n := !n + k;
    if !n > cap then raise Over
  in
  let rec go = function
    | Logic.Var (x, _) ->
        bump (match Map.Poly.find sizes x with Some k -> k | None -> 1)
    | Logic.Con _ -> bump 1
    | Logic.App (t1, t2, _) | Logic.Let (_, _, t1, t2, _) ->
        bump 1;
        go t1;
        go t2
    | Logic.Bin (_, _, _, t, _) | Logic.TyApp (t, _, _) | Logic.TyLam (_, t, _)
      ->
        bump 1;
        go t
  in
  try
    go phi;
    !n
  with Over -> cap + 1

(* [seq_as_array]: each constraint, and each instantiated form of one, is
   asked first as arrays plus a length when its sequences are concat-free and
   its reads range-guarded ([Z3interface.check_sat_seq_as_array], an
   equisatisfiable translation, so a pass or a failure means what it means
   untranslated); off, the questions are asked as they are. *)
let check_sat_solution ?(seq_as_array = false) ?(retry = false) ?matched
    ?ladder ?(budget_s = sat_check_budget_s) ?(max_nodes = sat_check_max_nodes) ~id
    ?(certs = Map.Poly.empty) pcsp (sol : Logic.term_subst_map) =
  let senv = PCSP.Problem.senv_of pcsp in
  let fenv = get_fenv () in
  let deadline = Common.Clock.now_s () +. budget_s in
  let spent () = Float.(Common.Clock.now_s () >= deadline) in
  (* each definition's size, counted up to the bound; one past the bound is
     never substituted, not even to collect its free variables, since every
     walk of it costs what its tree costs *)
  let sizes = Map.Poly.map sol ~f:(Logic.Term.ast_size_up_to max_nodes) in
  let within =
    Map.Poly.filteri sol ~f:(fun ~key ~data:_ ->
        Map.Poly.find_exn sizes key <= max_nodes)
  in
  (* one substitution for every constraint: the free variables of the
     solution's terms are collected once, not once per constraint *)
  let subst = Logic.Term.subst_rename_on_capture within in
  let r =
    Set.fold (PCSP.Problem.formulas_of pcsp) ~init:empty
      ~f:(fun r (uni_senv, phi) ->
        let phi0 = phi in
        (* not [Logic.Term.subst]: a solution recovered by predicate
           elimination can be a lambda whose body nests binders hundreds
           deep, and [subst] renames each binder with a traversal of its
           body, once per argument; one constraint took one to two minutes
           that way, the substitution below well under a second *)
        let phi' = lazy (subst phi) in
        if spent () then add r (Unchecked "checker budget spent")
        else if substituted_size_up_to max_nodes sizes phi > max_nodes then
          add r (Unchecked "constraint too large once the solution is substituted")
        else
        let phi' = Lazy.force phi' in
        if Set.exists (Logic.ExtTerm.fvs_of phi') ~f:(Map.Poly.mem senv) then
          add r (Unchecked "constraint mentions a predicate without a solution")
        else
          match
            try
              Ok
                (Evaluator.simplify
                @@ Logic.ExtTerm.to_old_fml Map.Poly.empty uni_senv phi')
            with e when not (Common.Timer.is_interrupt e) -> Error (Exn.to_string e)
          with
          | Error msg -> add r (Unchecked ("conversion failed: " ^ msg))
          | Ok phi -> (
              if Formula.is_true phi then add r Passed
              else
                (* every constraint is checked the same way, including one
                   with an interpretation-dependent term ([tl nil], an
                   uninterpreted function, a division): a solution has to
                   satisfy the constraints whatever the background theory
                   left open, so the question is validity for all of them *)
                match
                  try
                    Ok
                      ((if seq_as_array then
                          Z3Smt.Z3interface.check_sat_seq_as_array
                        else Z3Smt.Z3interface.check_sat)
                         ~timeout ~id fenv
                         [ split_seq_reads @@ Formula.negate phi ])
                  with e when not (Common.Timer.is_interrupt e) -> Error (Exn.to_string e)
                with
                | Ok `Unsat -> add r Passed
                | Ok (`Sat _) ->
                    let pvs =
                      Set.filter
                        (Logic.ExtTerm.fvs_of phi0)
                        ~f:(Map.Poly.mem senv)
                    in
                    add r
                      (Failed
                         (sprintf
                            "constraint violated by the model: %s; original: \
                             %s; model entries: %s"
                            (Formula.str_of phi)
                            (Logic.ExtTerm.str_of_formula senv uni_senv phi0)
                            (String.concat_map_set pvs ~sep:"; " ~f:(fun pv ->
                                 sprintf "%s := %s" (Ident.name_of_tvar pv)
                                   (match Map.Poly.find sol pv with
                                   | Some t -> Logic.ExtTerm.str_of t
                                   | None -> "<none>")))))
                | Ok _ when spent () -> add r (Unchecked "Z3 undecided")
                | Ok _ when valid_by_instances ~seq_as_array ?matched ?ladder ~id phi ->
                    add r Passed
                | Ok _
                  when retry && (not (spent ()))
                       && valid_by_stronger_routes ~id phi ->
                    add r Passed
                | Ok _ -> add r (Unchecked "Z3 undecided")
                | Error msg ->
                    (* a checker must not crash the run; the formula is
                       printed so that the cause can be found *)
                    add r
                      (Unchecked
                         (sprintf
                            "Z3 failed on the substituted constraint (%s): %s"
                            msg (Formula.str_of phi)))))
  in
  check_kind_constraints ~id ~certs pcsp sol r

(* ---- unsat: the witness ---- *)

let atoms_of_uclauses exs =
  ExClauseSet.exatoms_of_uclauses @@ ExClauseSet.instantiate
  @@ Set.Poly.of_list exs

let clauses_of (exs : UnsatWitness.example list) =
  List.map exs ~f:(fun e -> e.UnsatWitness.clause)

(* [instance_of ~id senv general target] decides instantiation between a
   recorded example [target] and the example [general] re-derived from the
   source clause under the recorded substitution: every instance of [target]
   must be an instance of [general],

     forall (params and dummies of target).
       cond_target  =>  exists (params and dummies of general only).
                          cond_general /\ atoms_general = atoms_target

   [target] may itself be parametric (don't-cares of Z3's partial assignment
   with a side condition), so its parameters are universally quantified and
   its side condition is a hypothesis; [general]'s parameters are the
   variables the validator's simplified piece had eliminated, hence
   existential.  The parameters of the two are renamed apart first (both use
   the canonical [$k] names).  A dummy shared by both sides is one constant,
   quantified once, universally.  Atoms are paired by predicate; every pairing
   is tried.  The query is one quantified Z3 validity check per pairing and is
   reached only when structural and string equality have failed. *)
let instance_of ~id senv (general : ExClause.t) (target : ExClause.t) =
  let fenv = get_fenv () in
  let unknowns = Map.key_set senv in
  let target = ExClause.refresh_params (Map.Poly.map senv ~f:Fn.id) target in
  let split ex =
    List.map (Set.to_list ex) ~f:(fun a ->
        match ExAtom.to_old_atom_with_phi a with
        | phi, Some (_, atm) -> `Atom (phi, atm)
        | phi, None -> `Pure phi)
  in
  let gp = split general.positive and gn = split general.negative in
  let tp = split target.positive and tn = split target.negative in
  let has_pure = List.exists ~f:(function `Pure _ -> true | _ -> false) in
  if has_pure gp || has_pure gn || has_pure tp || has_pure tn then
    Unchecked "instance check with a pure literal in the example"
  else
    let atoms =
      List.filter_map ~f:(function `Atom a -> Some a | `Pure _ -> None)
    in
    let gp, gn, tp, tn = (atoms gp, atoms gn, atoms tp, atoms tn) in
    let eqs_of gatm tatm =
      match (gatm, tatm) with
      | Atom.App (p1, ts1, _), Atom.App (p2, ts2, _)
        when Stdlib.(p1 = p2) && List.length ts1 = List.length ts2 ->
          Some (List.map2_exn ts1 ts2 ~f:Formula.eq)
      | _ -> None
    in
    (* every literal of [general] must become some literal of [target] of the
       same predicate and the same polarity; several may become the same one
       (an instantiation can merge literals: [Q(x) \/ Q(y)] under [x = y]),
       and [target] may have literals nothing maps to (a weaker clause still
       follows).  So the instance's literal set is a subset of the target's,
       which is what "the target follows from the instance" needs.  The first
       version paired literals one to one and required equal counts — it
       reported a merged instance as "not an instance" — and paired
       across polarities. *)
    let maps gs ts =
      List.fold_right gs ~init:[ [] ] ~f:(fun (_, gatm) acc ->
          List.concat_map ts ~f:(fun (_, tatm) ->
              match eqs_of gatm tatm with
              | None -> []
              | Some eqs -> List.map acc ~f:(fun rest -> eqs @ rest)))
    in
    let pairings () =
      List.concat_map (maps gp tp) ~f:(fun p ->
          List.map (maps gn tn) ~f:(fun n -> p @ n))
    in
    let too_many =
      let count gs ts = Int.pow (max 1 (List.length ts)) (List.length gs) in
      count gp tp * count gn tn > 4096
    in
    if too_many then
      Unchecked "instance check with too many literal pairings to enumerate"
    else
      let cond_t = Formula.and_of (List.map (tp @ tn) ~f:fst) in
      let cond_g = Formula.and_of (List.map (gp @ gn) ~f:fst) in
      let senv_of phis atms =
        Set.to_list
        @@ Set.filter
             (Set.Poly.union_list
                (List.map phis ~f:(Formula.term_sort_env_of ~bvs:unknowns)
                @ List.map atms ~f:(fun (_, atm) ->
                    Atom.term_sort_env_of ~bvs:unknowns atm)))
             ~f:(fun (x, _) -> not (Set.mem unknowns x))
      in
      let vars_t = senv_of [ cond_t ] (tp @ tn) in
      let vars_g =
        List.filter
          (senv_of [ cond_g ] (gp @ gn))
          ~f:(fun (x, _) ->
            not (List.exists vars_t ~f:(fun (y, _) -> Stdlib.(x = y))))
      in
      let results =
        List.map (pairings ()) ~f:(fun eqs ->
            let phi =
              Formula.forall vars_t @@ Formula.mk_imply cond_t
              @@ Formula.exists vars_g
              @@ Formula.and_of (cond_g :: eqs)
            in
            let phi = Evaluator.simplify phi in
            if Formula.is_true phi then `Valid
            else
              match
                Z3Smt.Z3interface.check_sat ~timeout ~id fenv
                  [ split_seq_reads @@ Formula.negate phi ]
              with
              | `Unsat -> `Valid
              | `Sat _ -> `Invalid
              | _ -> `Undecided)
      in
      if List.exists results ~f:(function `Valid -> true | _ -> false) then
        Passed
      else if
        List.exists results ~f:(function `Undecided -> true | _ -> false)
      then Unchecked "Z3 undecided on an instance check"
      else
        Failed "no instance relation between the example and the re-derivation"

(* [entails ~id senv premises target]: do the example clauses [premises]
   entail the example clause [target]?  Each clause's parameters are its own
   universally quantified variables (two parents both written with [$1] mean
   two different variables), so every clause is renamed apart and closed
   before the query, whose unknowns are Z3 uninterpreted predicates:

     premises_1 /\ ... /\ premises_n /\ not target   unsatisfiable

   This is the semantic form of resolution followed by instantiation; the
   syntactic closure in [derived_from] misses a derivation that instantiates a *non-unit* parent
   before resolving it (a parent [P(1,$1) => Q(1,$1)] against a unit
   [not Q($1,0)]: the two [$1] are unrelated, unification fails), which is
   what made `pldi2013_industrial_50` report a spurious FAILED in about 3
   runs out of 50. *)
let entails ~id senv (premises : ExClause.t list) (target : ExClause.t) =
  let fenv = get_fenv () in
  let unknowns = Map.key_set senv in
  let counter = ref 0 in
  let closed (ex : ExClause.t) =
    let lits pol =
      List.map (Set.to_list pol) ~f:(fun a ->
          match ExAtom.to_old_atom_with_phi a with
          | phi, Some (_, atm) -> (phi, Some (Formula.mk_atom atm))
          | phi, None -> (phi, None))
    in
    let pos = lits ex.positive and neg = lits ex.negative in
    (* an example clause [cond => (\/ pos) \/ (\/ not neg)]: the side
       conditions of its atoms are hypotheses *)
    let cond = Formula.and_of (List.map (pos @ neg) ~f:fst) in
    let body =
      Formula.or_of
        (List.filter_map pos ~f:snd
        @ List.filter_map neg ~f:(fun (_, a) -> Option.map a ~f:Formula.negate)
        )
    in
    let phi = Formula.mk_imply cond body in
    let vars =
      Set.to_list
      @@ Set.filter (Formula.term_sort_env_of ~bvs:unknowns phi)
           ~f:(fun (x, _) -> not (Set.mem unknowns x))
    in
    incr counter;
    let ren =
      Map.Poly.of_alist_exn
        (List.map vars ~f:(fun (x, _) ->
             (x, Ident.Tvar (sprintf "%s#c%d" (Ident.name_of_tvar x) !counter))))
    in
    let vars = List.map vars ~f:(fun (x, s) -> (Map.Poly.find_exn ren x, s)) in
    Formula.forall vars (Formula.rename ren phi)
  in
  try
    let phis =
      List.map ~f:split_seq_reads
      @@ List.map premises ~f:closed
      @ [ Formula.negate (closed target) ]
    in
    match Z3Smt.Z3interface.check_sat_with_preds ~timeout ~id fenv phis with
    | `Unsat -> Passed
    | `Sat -> Failed ""
    | `Unknown ->
        Unchecked "Z3 undecided on the entailment of a derived example"
  with e when not (Common.Timer.is_interrupt e) ->
    Unchecked
      ("Z3 could not check the entailment of a derived example: "
     ^ Exn.to_string e)

(* an [instance] example must come out of its source clause under the
   recorded substitution; a [unit-propagation] example out of its parents *)
let check_instance ?(context = []) ~id ~wfpvs senv (e : UnsatWitness.example) =
  let unknowns = Map.key_set senv in
  let fenv = get_fenv () in
  (* The decision on a ground guard the clause instance's pure part left, made
     the sound way and NOT copied from whatever the derivation did: a checker
     that repeats the step it checks certifies that step's mistakes.  A
     solution must make [cond => +-P(t)] hold in every model of the theory, so
     the guard may be dropped (`Sat, the atoms become unconditional) only when
     [cond] is VALID -- satisfiable, and its negation unsatisfiable.  A guard
     that is merely satisfiable forces the atom only where it holds: two
     examples whose guards are each satisfiable and jointly impossible, both
     dropped, collide into a refutation of a satisfiable problem.  An
     unsatisfiable guard makes the instance say nothing (`Unsat, dropped), and
     anything undecided keeps the guard, which is always sound; a recorded
     example that dropped a guard the check could not prove valid is then no
     instance of the re-derivation, and [instance_of] reports it failed or
     undecided.  The budget is the one the solver's own decision uses, so the
     two are decided alike wherever the solver decided soundly. *)
  let discharge cond =
    match
      Z3Smt.Z3interface.check_sat ~id ~timeout:(Some 1000) fenv [ cond ]
    with
    | `Unsat -> `Unsat
    | `Sat _ -> (
        match
          Z3Smt.Z3interface.check_sat ~id ~timeout:(Some 1000) fenv
            [ Formula.mk_neg cond ]
        with
        | `Unsat -> `Sat
        | _ -> `Unknown)
    | _ -> `Unknown
  in
  (* the clause instance [via][subst], as the validator would have
     produced it *)
  let instances_of via sub =
    List.filter_map via ~f:(fun c ->
        let uni_senv, term = Clause.to_senv_formula c in
        try
          Some
            (ExClauseSet.of_subst ~discharge senv
               (Logic.ExtTerm.to_old_fml senv uni_senv term)
               sub
            |> Set.Poly.map ~f:(ExClause.simplify_wfpvs wfpvs))
        with exn_ when not (Common.Timer.is_async exn_) -> None)
  in
  let same ex =
    ExClause.equal ex e.clause
    || String.equal (ExClause.str_of ex) (ExClause.str_of e.clause)
  in
  (* is [e.clause] among [exs], structurally or as an instance (Inst)? *)
  let covered_by exs =
    if Set.exists exs ~f:same then Passed
    else
      let rs =
        List.map (Set.to_list exs) ~f:(fun ex ->
            instance_of ~id senv ex e.clause)
      in
      if List.exists rs ~f:(function Passed -> true | _ -> false) then Passed
      else if List.exists rs ~f:(function Unchecked _ -> true | _ -> false)
      then Unchecked "Z3 undecided on an instance check"
      else Failed ""
  in
  (* [e.clause] must follow from the clause instances [base] and the
     recorded parents by unit propagation (the recorded sources are
     transitive, so the closure is taken), up to instantiation of
     parameters *)
  let derived_from ~what (base : ExClause.t list) =
    let units, nonunits = List.partition_tf e.parents ~f:ExClause.is_unit in
    let tag exs = Set.Poly.of_list @@ List.map exs ~f:(fun ex -> (ex, [])) in
    let und = base @ nonunits in
    let und_base = und in
    if List.is_empty und then
      Unchecked
        (sprintf "%s example without a clause instance or a non-unit parent"
           what)
    else
      match
        ExClauseSet.unit_propagation unknowns
          (tag (List.filter units ~f:ExClause.is_unit_positive))
          (tag (List.filter units ~f:ExClause.is_unit_negative))
          (tag und)
      with
      | `Unsat _ -> Passed (* the premises already conflict *)
      | `Result (dpos, dneg, und) -> (
          let results =
            Set.Poly.map ~f:fst (Set.Poly.union_list [ dpos; dneg; und ])
          in
          (* the syntactic closure removes a literal only when a unit
             subsumes it by pattern matching; a parametric unit whose
             arguments relate to the literal's through arithmetic
             ([¬P(-1 * $1, $1)] against [P(0, 0)]) is missed, so remove
             semantically as well: a literal goes when some unit of the
             opposite polarity covers it as an instance ((Res) with (Inst)) *)
          let pos_units =
            List.filter units ~f:ExClause.is_unit_positive
            |> List.map ~f:ExClause.exatom_of_uclause
          and neg_units =
            List.filter units ~f:ExClause.is_unit_negative
            |> List.map ~f:ExClause.exatom_of_uclause
          in
          let covers unit lit =
            match
              instance_of ~id senv
                (ExClause.mk_unit_pos unit)
                (ExClause.mk_unit_pos lit)
            with
            | Passed -> true
            | _ -> false
          in
          let reduce (ex : ExClause.t) =
            ExClause.
              {
                positive =
                  Set.filter ex.positive ~f:(fun l ->
                      not (List.exists neg_units ~f:(fun u -> covers u l)));
                negative =
                  Set.filter ex.negative ~f:(fun l ->
                      not (List.exists pos_units ~f:(fun u -> covers u l)));
              }
          in
          let results =
            Set.union results
              (Set.Poly.map ~f:reduce
                 (Set.Poly.union_list [ Set.Poly.of_list und_base; results ]))
          in
          match covered_by results with
          | Failed _ -> (
              (* the syntactic closure missed it; the semantic check finds a
                 derivation that instantiates a non-unit parent before
                 resolving it ((Inst) before (Res)) *)
              match entails ~id senv (base @ e.parents) e.clause with
              | Passed -> Passed
              | Unchecked why -> Unchecked why
              | Failed _ ->
                  let pvs =
                    Set.Poly.union_list (List.map base ~f:ExClause.pvs_of)
                  in
                  Failed
                    (sprintf
                       "%s example %s does not follow from its clause instance \
                        and parents; instances: %s; parents: %s; decided units \
                        of the witness over the same predicates: %s"
                       what (ExClause.str_of e.clause)
                       (String.concat_map_list base ~sep:"; " ~f:ExClause.str_of)
                       (String.concat_map_list e.parents ~sep:"; "
                          ~f:ExClause.str_of)
                       (String.concat_map_list ~sep:"; " ~f:ExClause.str_of
                       @@ List.filter context ~f:(fun u ->
                           ExClause.is_unit u
                           && not (Set.are_disjoint (ExClause.pvs_of u) pvs)))))
          | r -> r)
  in
  match e.derivation with
  | None -> Unchecked "example without a recorded derivation"
  | Some ("instance", None, _) ->
      Unchecked "instance without a recorded substitution"
  | Some ("instance", Some sub, _) -> (
      let clauses =
        List.filter_map e.sources ~f:(function
          | UnsatWitness.Clause c | UnsatWitness.Assumed c -> Some c
          | UnsatWitness.Untracked -> None)
      in
      if List.is_empty clauses then Unchecked "instance without a source clause"
      else
        let rederived = instances_of clauses sub in
        match covered_by (Set.Poly.union_list rederived) with
        | Failed _ ->
            Failed
              (sprintf
                 "example %s is not an instance of its source clause under %s; \
                  re-derived: %s"
                 (ExClause.str_of e.clause) (TermSubst.str_of sub)
                 (String.concat_map_list rederived ~sep:" | " ~f:(fun exs ->
                      String.concat_map_set exs ~sep:"; " ~f:ExClause.str_of)))
        | r -> r)
  | Some ("unit-propagation", _, _) -> derived_from ~what:"unit-propagation" []
  | Some ("resolution", sub, via) -> (
      match (via, sub) with
      | Some c, Some sub ->
          derived_from ~what:"resolution"
            (Set.to_list @@ Set.Poly.union_list @@ instances_of [ c ] sub)
      | None, _ ->
          (* acquired from an undecided example: the parents carry it *)
          derived_from ~what:"resolution" []
      | Some _, None ->
          Unchecked "resolution example without a recorded substitution")
  | Some (rule, _, via) when String.equal rule PCSatCommon.FactGoal.validity_rule
    -> (
      (* an atom decided by a fact or goal clause through the validity of
         [c => exists x. Phi /\ a = t]: re-ask that question of the source
         clause, independently of the run that derived it *)
      let clause =
        match via with
        | Some c -> Some c
        | None ->
            List.find_map e.sources ~f:(function
              | UnsatWitness.Clause c | UnsatWitness.Assumed c -> Some c
              | UnsatWitness.Untracked -> None)
      in
      let atom =
        match
          (Set.to_list e.clause.ExClause.positive,
           Set.to_list e.clause.ExClause.negative)
        with
        | [ a ], [] -> Some (PCSatCommon.FactGoal.Fact, a)
        | [], [ a ] -> Some (PCSatCommon.FactGoal.Goal, a)
        | _ -> None
      in
      match (clause, atom) with
      | None, _ -> Unchecked "fact/goal example without a source clause"
      | _, None -> Unchecked "fact/goal example that is not a unit"
      | Some c, Some (role, a) -> (
          match PCSatCommon.FactGoal.entry_of_clause senv c with
          | None -> Failed "the source clause is neither a fact nor a goal clause"
          | Some ent when not (Stdlib.( = ) ent.PCSatCommon.FactGoal.role role) ->
              Failed "the example's polarity does not match its source clause"
          | Some ent -> (
              match PCSatCommon.FactGoal.validity_query ent a with
              | None -> Failed "the example's atom does not match its source clause"
              | Some phi ->
                  if Z3Smt.Z3interface.may_not_return phi then
                    Unchecked "fact/goal question the solver may not return on"
                  else (
                    match
                      Z3Smt.Z3interface.check_valid ~id ~timeout:(Some 5000)
                        fenv phi
                    with
                    | `Valid -> Passed
                    | `Invalid _ ->
                        Failed
                          (sprintf "fact/goal question is not valid: %s"
                             (Formula.str_of phi))
                    | _ -> Unchecked "Z3 undecided on a fact/goal question"))))
  | Some (rule, _, _) -> Unchecked (sprintf "unknown rule %s" rule)

(* The side condition of a lemma over a non-well-founded or parity FAMILY.  A
   family has one tag per predicate of a mutual recursion and one predicate per
   ordered pair of tags, [(tag_l, tag_r)]; an atom of the pair predicate, with
   arguments [shared @ left @ right], is an edge from the node
   [(tag_l, shared @ left)] to the node [(tag_r, shared @ right)].  Positive
   atoms that close a loop describe a run that can be repeated forever, so they
   cannot all hold:
   - NWF: any cycle among the lemma's edges is a violation;
   - Parity: a cycle is a violation only when the least priority of the tags
     it visits is NOT in the family's accepting set -- a cycle whose least
     priority is accepting may repeat forever.
   The learner emits exactly one cycle (or one self-loop, where the two nodes
   of a single atom are equal), but the lemma is sound as soon as its edges
   CONTAIN such a cycle, since a clause saying that a set of atoms cannot all
   hold is implied by the same statement about a subset; that weaker, exact
   condition is what is checked.  Priorities are the untruncated [sigma], as
   the learner reads them.  Nodes are compared structurally, which is how the
   learner keys them. *)
let check_family_lemma pcsp atoms =
  let kind_of pvar =
    Map.Poly.find (PCSP.Problem.kind_map_of pcsp) (Ident.pvar_to_tvar pvar)
  in
  let family pvar =
    match kind_of pvar with
    | Some (Kind.NWF (nwf, tags)) -> Some (`NWF, nwf, tags)
    | Some (Kind.Parity (nwf, tags)) -> Some (`Parity, nwf, tags)
    | _ -> None
  in
  let fams = List.map atoms ~f:(fun (pvar, args) -> (family pvar, args)) in
  match fams with
  | [] -> Unchecked "lemma without predicate atoms"
  | (None, _) :: _ -> Unchecked "not a family lemma"
  | (Some (k0, nwf0, _), _) :: _ -> (
      let what = match k0 with `NWF -> "NWF" | `Parity -> "Parity" in
      if
        not
          (List.for_all fams ~f:(function
            | Some (k, nwf, _), _ ->
                Stdlib.(k = k0) && Kind.equal_nwf nwf nwf0
            | None, _ -> false))
      then Unchecked (what ^ " lemma over several families or kinds")
      else
        let n_shared = List.length nwf0.Kind.sorts_shared in
        let edge = function
          | Some (_, (nwf : Kind.nwf), (idl, idr)), args -> (
              match
                ( Hashtbl.Poly.find nwf.sorts_map idl,
                  Hashtbl.Poly.find nwf.sorts_map idr )
              with
              | Some sorts_l, Some sorts_r
                when List.length args
                     = n_shared + List.length sorts_l + List.length sorts_r ->
                  let shared, rest = List.split_n args n_shared in
                  let l, r = List.split_n rest (List.length sorts_l) in
                  Ok ((idl, shared @ l), (idr, shared @ r))
              | Some _, Some _ ->
                  Error
                    (Failed
                       (sprintf "%s lemma atom has %d arguments, not the                                  family's arity for its tags"
                          what (List.length args)))
              | _ -> Error (Unchecked (what ^ " lemma tag without sorts")))
          | None, _ -> Error (Unchecked "not a family lemma")
        in
        match Result.all (List.map fams ~f:edge) with
        | Error o -> o
        | Ok edges -> (
            let node_eq (t1, a1) (t2, a2) =
              Ident.tvar_equal t1 t2 && List.equal Stdlib.( = ) a1 a2
            in
            let nodes =
              List.fold edges ~init:[] ~f:(fun acc (s, d) ->
                  let add acc n =
                    if List.mem acc n ~equal:node_eq then acc else n :: acc
                  in
                  add (add acc s) d)
            in
            (* is [v] on a cycle of at least one edge that visits only nodes
               satisfying [allowed]? *)
            let on_cycle ~allowed v =
              let succs u =
                List.filter_map edges ~f:(fun (s, d) ->
                    if node_eq s u && allowed d then Some d else None)
              in
              let rec reach visited = function
                | [] -> false
                | u :: todo ->
                    if node_eq u v then true
                    else if List.mem visited u ~equal:node_eq then
                      reach visited todo
                    else reach (u :: visited) (succs u @ todo)
              in
              allowed v && reach [] (succs v)
            in
            match k0 with
            | `NWF ->
                if List.exists nodes ~f:(on_cycle ~allowed:(Fn.const true))
                then Passed
                else Failed "NWF lemma contains no cycle"
            | `Parity -> (
                let pri (tag, _) = Map.Poly.find nwf0.Kind.sigma tag in
                match Option.all (List.map nodes ~f:pri) with
                | None -> Unchecked "Parity lemma tag without a priority"
                | Some _ ->
                    (* a cycle whose least priority is [p] visits a node of
                       priority [p] and only nodes of priority at least [p] *)
                    let violating v =
                      match pri v with
                      | Some p when not (Set.mem nwf0.Kind.acc_set p) ->
                          on_cycle
                            ~allowed:(fun u ->
                              match pri u with
                              | Some q -> q >= p
                              | None -> false)
                            v
                      | _ -> false
                    in
                    if List.exists nodes ~f:violating then Passed
                    else if
                      List.exists nodes ~f:(on_cycle ~allowed:(Fn.const true))
                    then
                      Failed
                        "Parity lemma: every cycle among its atoms has an \
                         accepting least priority"
                    else Failed "Parity lemma contains no cycle")))

(* a WF lemma names the atoms of a cycle, a DWF lemma one self-loop (a longer
   cycle can lie in a finite union of well-founded relations); an FN lemma two
   outputs for one input; an NWF or Parity lemma a cycle over a family, see
   [check_family_lemma] *)
let check_lemma pcsp (lemma : ExClause.t) =
  if not (Set.is_empty lemma.positive) then
    Unchecked "lemma with a positive literal"
  else
    let atoms =
      List.filter_map (Set.to_list lemma.negative) ~f:(fun a ->
          Option.bind (ExAtom.to_old_atom a) ~f:(fun (_, atm) ->
              try
                let pvar, _, args, _ = Atom.let_pvar_app atm in
                Some (pvar, args)
              with exn_ when not (Common.Timer.is_async exn_) -> None))
    in
    let is_family pvar =
      match
        Map.Poly.find (PCSP.Problem.kind_map_of pcsp) (Ident.pvar_to_tvar pvar)
      with
      | Some (Kind.NWF _ | Kind.Parity _) -> true
      | _ -> false
    in
    match atoms with
    | [] -> Unchecked "lemma without predicate atoms"
    | (pvar, _) :: _ when is_family pvar -> check_family_lemma pcsp atoms
    | (pvar, _) :: _ when not (List.for_all atoms ~f:(fst >> Stdlib.( = ) pvar))
      ->
        Unchecked "lemma over several predicates"
    | (pvar, _) :: _ ->
        let tv = Ident.pvar_to_tvar pvar in
        if PCSP.Problem.is_wf_pred pcsp tv || PCSP.Problem.is_dwf_pred pcsp tv
        then
          let edges =
            List.map atoms ~f:(fun (_, args) ->
                let n = List.length args / 2 in
                let l, r = List.split_n args n in
                ( List.map l ~f:(Evaluator.simplify_term >> Term.str_of),
                  List.map r ~f:(Evaluator.simplify_term >> Term.str_of) ))
          in
          let lhs = List.map edges ~f:fst and rhs = List.map edges ~f:snd in
          let eq = List.equal String.equal in
          if PCSP.Problem.is_dwf_pred pcsp tv then
            match edges with
            | [ (l, r) ] when eq l r -> Passed
            | _ -> Failed "DWF lemma is not a self-loop"
          else if
            List.for_all edges ~f:(fun (l, r) ->
                List.mem rhs l ~equal:eq && List.mem lhs r ~equal:eq)
          then Passed
          else Failed "WF lemma is not a cycle"
        else if PCSP.Problem.is_fn_pred pcsp tv then
          match atoms with
          | [ (_, a1); (_, a2) ] -> (
              match (List.rev a1, List.rev a2) with
              | o1 :: in1, o2 :: in2
                when List.equal Stdlib.( = ) in1 in2 && Stdlib.(o1 <> o2) ->
                  Passed
              | _ -> Failed "FN lemma does not name two outputs for one input")
          | _ -> Unchecked "FN lemma with other than two atoms"
        else if PCSP.Problem.is_uniq_pred pcsp tv then
          match (atoms, PCSP.Problem.kind_of pcsp tv) with
          | [ (_, a1); (_, a2) ], Kind.Uniq (j, _)
            when List.length a1 > j && List.length a2 > j ->
              let drop a = List.take a j @ List.drop a (j + 1) in
              if
                List.equal Stdlib.( = ) (drop a1) (drop a2)
                &&
                let v1 = List.nth_exn a1 j and v2 = List.nth_exn a2 j in
                Stdlib.(v1 <> v2)
              then Passed
              else Failed "Uniq lemma does not name two values at its position for one rest"
          | _ -> Unchecked "Uniq lemma with other than two atoms"
        else Unchecked "lemma over a predicate of no kind a lemma is learned for"

let prop_of_exclause ~bool_var_of (ex : ExClause.t) =
  Formula.or_of
  @@ List.map (Set.to_list ex.positive) ~f:bool_var_of
  @ List.map (Set.to_list ex.negative) ~f:(bool_var_of >> Formula.mk_neg)

(* Syntactic membership decides "the atom is a positive and a negative example"
   only for ground examples.  A parametric example denotes every ground instance
   satisfying its guard, and the labeler may instantiate it at more than one of
   them (its [pex_instances]), so the conflicting atom can be a legitimate
   instance of an example without being the one [ExClauseSet.instantiate]
   picks.  Then ask what the conflict actually claims: for a positive
   [cond_p | P(t̄)] and a negative [cond_n | P(ū)], is [cond_p ∧ cond_n ∧ t̄ = ū]
   satisfiable?  A point satisfying it makes [P] both true and false, which is
   the refutation.  Dummy constants are left free: choosing the elements of an
   uninterpreted carrier is exactly what a refutation may do (a forall-sort is
   *every* non-empty type). *)
let conflicting_pair
    ?(check = fun ~id ~timeout fenv phis ->
      Z3Smt.Z3interface.check_sat ~id ~timeout fenv phis)
    ~id fenv poss negs =
  (* the two sides use the same canonical parameter names ([$1], [$2], ...), so
     the negative side is renamed apart first -- without it the conjunction of
     the two guards is trivially unsatisfiable.  Only the parameters are
     renamed: a dummy constant names an element of the carrier and is shared
     between the examples, and renaming it apart would accept conflicts that do
     not exist. *)
  let apart cl =
    ExClause.rename
      (Map.Poly.map (ExClause.params_of cl) ~f:(fun _ ->
           Ident.mk_fresh_dontcare ""))
      cl
  in
  let guarded e =
    if not (ExClause.is_unit e) then None
    else
      let atm = ExClause.exatom_of_uclause e in
      match (ExAtom.pvar_of atm, ExAtom.args_of atm) with
      | Some pvar, Some ts ->
          let _, cond, _ = ExAtom.to_old_formula_and_cond atm in
          Some (pvar, ts, cond)
      | _ -> None
  in
  let ps = List.filter_map (clauses_of poss) ~f:guarded in
  let ns = List.filter_map (List.map ~f:apart (clauses_of negs)) ~f:guarded in
  (* A conflict is existential over pairs. Only a proved overlap may stop the
     search; undecided pairs must survive later disjoint pairs in the summary. *)
  List.fold_until ps ~init:None
    ~finish:(Option.value ~default:(Unchecked "no comparable example pair"))
    ~f:(fun acc (pv, ts, cp) ->
      let acc =
        List.fold_until ns ~init:acc ~finish:Fn.id
          ~f:(fun acc (pv', us, cn) ->
            if not (Ident.pvar_equal pv pv' && List.length ts = List.length us)
            then Continue acc
            else
              let phi =
                Formula.and_of (cp :: cn :: List.map2_exn ts us ~f:Formula.eq)
              in
              match check ~id ~timeout:(Some 5000) fenv [ split_seq_reads phi ] with
              | `Sat _ -> Stop (Some Passed)
              | `Unsat ->
                  Continue
                    (match acc with
                    | Some _ -> acc
                    | None -> Some (Failed "no instance makes the conflicting atom both"))
              | _ -> Continue (Some (Unchecked "Z3 undecided on a conflicting pair")))
      in
      match acc with
      | Some Passed -> Stop Passed
      | _ -> Continue acc)

(* Is this atom a claim with no condition -- an application without a guard,
   or with the guard [true]?  Only such an atom conflicts with its own negation
   by syntax alone. *)
let unguarded_key = function
  | ExAtom.PApp _ -> true
  | ExAtom.PPApp ((_, cond), _) -> Formula.is_true cond
  | ExAtom.FCon _ -> false

(* The second attempt at a countermodel the solver left undecided, used
   only to PASS it: it never reports a failure, since each step below is a
   strengthening of the question and a strengthening that cannot be shown
   true says nothing about the original.

   [formula] is the conjunction of the clauses with no unknown, each read
   under the universal closure of its own free variables, and [model] a
   conjunction of equations [x = t] with [t] closed.  The formula is not
   valid as soon as ONE clause is false under a closed assignment of its
   free variables, so each clause whose free variables [model] all assigns,
   at the sorts the clause uses (two clauses may use one name at two sorts),
   is tried on its own:
   - under the assignment, the clause's negation in negation normal form is
     a closed formula, true exactly when each of its conjuncts is;
   - an existential binder of it (a universal binder of the clause) for
     which a closed term of its sort is recorded is replaced by that term,
     which can only make the conjunct stronger;
   - a conjunct is shown true by the solver answering [unsat] on its
     negation, whose quantifiers left over from the clause's existentials are
     existential and so are Skolemised away.
   Everything the pass rests on is done here, on the formula as recorded;
   the terms come from the refuting side, which found them by rewrites of
   the clause, but no rewrite is trusted: a wrong term makes a conjunct fail
   to be shown true, nothing more.  What it buys: a Rust-derived call-site
   clause that binds a history sequence universally under a pinned tuple,
   whose negation under the countermodel the solver leaves undecided whole,
   is decided conjunct by conjunct once the history is given. *)
let countermodel_falsifies_a_clause ~timeout ~id fenv formula model witnesses =
  let asg =
    List.fold (Formula.conjuncts_list_of model) ~init:Map.Poly.empty
      ~f:(fun acc -> function
      | Formula.Atom
          (Atom.App (Predicate.Psym T_bool.Eq, [ Term.Var (x, s, _); t ], _), _)
        when Set.is_empty (Term.tvs_of t) && not (Map.Poly.mem acc x) ->
          Map.Poly.set acc ~key:x ~data:(s, t)
      | _ -> acc)
  in
  let witness_of x s =
    List.find_map witnesses ~f:(fun (y, s', t) ->
        if
          Ident.tvar_equal x y
          && Stdlib.(s = s')
          && Stdlib.(Term.sort_of t = s)
          && Set.is_empty (Term.tvs_of t)
        then Some t
        else None)
  in
  (* existential introduction at every binder that has a closed term; a
     closed term cannot be captured, so plain substitution is exact *)
  let rec instantiate phi =
    match phi with
    | Formula.Bind (Formula.Exists, senv, body, _) ->
        let given, kept =
          List.partition_map senv ~f:(fun (x, s) ->
              match witness_of x s with
              | Some t -> First (x, t)
              | None -> Second (x, s))
        in
        let body =
          if List.is_empty given then body
          else Formula.subst (Map.Poly.of_alist_reduce given ~f:(fun a _ -> a)) body
        in
        Formula.mk_exists_if_bounded kept (instantiate body)
    | Formula.Bind (b, senv, body, _) -> Formula.mk_bind b senv (instantiate body)
    | Formula.BinaryOp (op, p, q, _) ->
        Formula.mk_binop op (instantiate p) (instantiate q)
    | Formula.UnaryOp (op, p, _) -> Formula.mk_unop op (instantiate p)
    | phi -> phi
  in
  let true_conjunct d =
    match
      Z3Smt.Z3interface.check_sat ~timeout ~fresh_solver:true ~id
        (Z3Smt.Z3interface.fenv_reached_by fenv d)
        [ Formula.nnf_of (Formula.negate d) ]
    with
    | `Unsat -> true
    | _ -> false
    | exception exn when not (Common.Timer.is_async exn) -> false
  in
  (not (Map.Poly.is_empty asg))
  && List.exists (Formula.conjuncts_list_of formula) ~f:(fun c ->
         let env = Formula.term_sort_env_of c in
         Set.for_all env ~f:(fun (x, s) ->
             match Map.Poly.find asg x with
             | Some (s', _) -> Stdlib.(s = s')
             | None -> false)
         &&
         let c =
           Formula.subst
             (Map.Poly.of_alist_exn
             @@ List.map (Set.to_list env) ~f:(fun (x, _) ->
                    (x, snd @@ Map.Poly.find_exn asg x)))
             c
         in
         match Formula.nnf_of (Formula.negate c) with
         | exception exn when not (Common.Timer.is_async exn) -> false
         | neg ->
             Set.is_empty (Formula.tvs_of neg)
             && List.for_all (Formula.conjuncts_list_of neg) ~f:(fun d ->
                    true_conjunct (instantiate d)))

let rec check_unsat_witness ~id pcsp (w : UnsatWitness.t) =
  let senv = w.senv in
  let fenv = get_fenv () in
  let wfpvs = PCSP.Problem.wfpvs_of pcsp in
  let context =
    match w.body with
    | UnsatWitness.Conflict { positives; negatives; _ } ->
        clauses_of positives @ clauses_of negatives
    | UnsatWitness.Propagation { positives; negatives; _ }
    | UnsatWitness.Labeling { positives; negatives; _ } ->
        clauses_of positives @ clauses_of negatives
    | _ -> []
  in
  let check_examples r exs =
    List.fold exs ~init:r ~f:(fun r e ->
        add r (check_instance ~context ~id ~wfpvs senv e))
  in
  match w.body with
  | UnsatWitness.Conflict { atom; positives; negatives } ->
      let r = check_examples (check_examples empty positives) negatives in
      let pos = atoms_of_uclauses (clauses_of positives) in
      let neg = atoms_of_uclauses (clauses_of negatives) in
      add r
        (if
           Set.mem pos atom && Set.mem neg atom
           (* one key on both sides is a conflict by itself only when the key
              carries no guard: [cond => P(t)] and [cond => not P(t)] conflict
              exactly when [cond] is satisfiable, and a guard can be
              unsatisfiable without simplifying to [false] (two equations
              giving one open term two values).  Any other guard is left to
              the semantic check below, which asks that satisfiability *)
           && unguarded_key atom
         then Passed
         else
           (* not the instance [instantiate] picks: check what the conflict
              claims instead of rejecting it *)
           match conflicting_pair ~id fenv positives negatives with
           | Passed -> Passed
           | Unchecked _ as o -> o
           | Failed _ ->
               Failed
                 "conflicting atom is not both a positive and a negative \
                  example")
  | UnsatWitness.Propagation { positives; negatives; undecided; _ } ->
      let r =
        check_examples
          (check_examples (check_examples empty positives) negatives)
          undecided
      in
      let tag exs =
        Set.Poly.of_list
        @@ List.map (clauses_of exs) ~f:(fun ex -> (ex, [ ex ]))
      in
      add r
        (match
           ExClauseSet.unit_propagation (Map.key_set senv) (tag positives)
             (tag negatives) (tag undecided)
         with
        | `Unsat _ -> Passed
        | `Result _ ->
            Failed
              "unit propagation over the recorded examples does not conflict")
  | UnsatWitness.Labeling { positives; negatives; undecided; lemmas } ->
      (* The atom-to-proposition map belongs to this one replay.  Witness
         checks can run in parallel (MuVal runs primal/dual PCSat tasks in
         separate domains), and Core's ordinary hash table is not safe for
         concurrent mutation.  A process-global map also retained every atom
         ever checked. *)
      let bool_vars = Hashtbl.Poly.create () in
      let bool_var_of atm =
        Hashtbl.find_or_add bool_vars atm ~default:(fun () ->
            Formula.of_bool_var
              (Ident.Tvar (sprintf "#wc%d" (Hashtbl.length bool_vars))))
      in
      let r =
        check_examples
          (check_examples (check_examples empty positives) negatives)
          undecided
      in
      let r =
        List.fold lemmas ~init:r ~f:(fun r l -> add r (check_lemma pcsp l))
      in
      (* The labeler encodes the instantiated examples propositionally, one
         variable per atom with its guard.  That is a sound abstraction only
         for atoms that say something: an instance whose guard became [false]
         claims nothing, and two of them from different examples share a
         variable and contradict each other.  So they are removed here, as the
         labeler must remove them, and the problem is decided without them;
         replaying the encoding with them in would certify exactly the
         refutation it should catch. *)
      let vacuous = ref 0 in
      let units b exs =
        List.filter_map
          (Set.to_list (atoms_of_uclauses (clauses_of exs)))
          ~f:(fun a ->
            if ExAtom.guard_is_false a then (
              incr vacuous;
              None)
            else
              Some (if b then bool_var_of a else Formula.mk_neg (bool_var_of a)))
      in
      let phis =
        units true positives @ units false negatives
        @ List.filter_map
            (Set.to_list @@ ExClauseSet.instantiate
            @@ Set.Poly.of_list (clauses_of undecided))
            ~f:(fun cl ->
              if ExClause.has_false_guard cl then (
                incr vacuous;
                None)
              else Some (prop_of_exclause ~bool_var_of cl))
        @ List.map lemmas ~f:(prop_of_exclause ~bool_var_of)
      in
      add r
        (match Z3Smt.Z3interface.check_sat ~timeout ~id fenv phis with
        | `Unsat -> Passed
        | `Sat _ ->
            Failed
              (if !vacuous = 0 then "the recorded labeling problem is satisfiable"
               else
                 sprintf
                   "the recorded labeling problem is satisfiable once the %d \
                    instance(s) whose guard is false at the instantiation \
                    point are removed"
                   !vacuous)
        | _ -> Unchecked "Z3 undecided on the labeling problem")
  | UnsatWitness.FalseConstraint (_, term) ->
      (* The local check is only that the leaf is literally [false].  That
         does not establish the refutation against the *original* problem: the
         leaf is a clause of the preprocessed problem, produced by the
         simplification and elimination steps, and the refutation is
         certified only when those steps are re-derived.  [check_preprocessing]
         re-derives the leaf against the original clauses; until it can, the
         unsat check must not report the refutation as passed, or the two
         summaries disagree about whether it is certified. *)
      let r =
        if Logic.BoolTerm.is_false term then add empty Passed
        else add empty (Failed "recorded constraint is not false")
      in
      add r
        (Unchecked
           "false-constraint: the preprocessed literal false is not re-derived \
            from the original problem")
  | UnsatWitness.Countermodel { formula; model; witnesses } ->
      add empty
        (match
           Z3Smt.Z3interface.check_sat ~timeout ~id fenv
             (List.map ~f:split_seq_reads [ model; Formula.negate formula ])
         with
        | `Sat _ -> Passed
        | `Unsat -> Failed "the recorded model does not falsify the formula"
        | _ ->
            if
              countermodel_falsifies_a_clause ~timeout ~id fenv formula model
                witnesses
            then Passed
            else Unchecked "Z3 undecided on the countermodel")
  | UnsatWitness.External what -> add empty (Unchecked ("external: " ^ what))
  | UnsatWitness.FiniteInstance fi ->
      (* the leaf as for a bare [false] constraint, and then the refutation
         it stands for, in place of the admission that it is not re-derived *)
      let r =
        if Logic.BoolTerm.is_false (snd fi.leaf) then add empty Passed
        else add empty (Failed "recorded constraint is not false")
      in
      add r (check_finite_instance ~id pcsp fi)

(* ---- Stage 3a: are the preprocessed clauses the witness uses consequences
   of the original problem under the preprocessor's definitions? ---- *)

and clauses_used (w : UnsatWitness.t) : Clause.t list =
  let of_examples exs =
    List.concat_map exs ~f:(fun (e : UnsatWitness.example) ->
        List.filter_map e.sources ~f:(function
          | UnsatWitness.Clause c -> Some c
          | UnsatWitness.Assumed _ | UnsatWitness.Untracked -> None))
  in
  let cs =
    match w.body with
    | UnsatWitness.Conflict { positives; negatives; _ } ->
        of_examples positives @ of_examples negatives
    | UnsatWitness.Labeling { positives; negatives; undecided; _ }
    | UnsatWitness.Propagation { positives; negatives; undecided; _ } ->
        of_examples positives @ of_examples negatives @ of_examples undecided
    | UnsatWitness.FalseConstraint (uni_senv, term) ->
        [ Clause.canon (uni_senv, Set.Poly.empty, Set.Poly.empty, term) ]
    | UnsatWitness.Countermodel _ | UnsatWitness.External _ -> []
    | UnsatWitness.FiniteInstance { source; _ } ->
        (* what the refutation rests on at this level is the problem the
           instantiation was applied to, all of it: the instance is re-derived
           from it and re-refuted separately, so what is left to establish
           here is that its clauses follow from the original problem *)
        Set.to_list @@ PCSP.Problem.clauses_of @@ PCSP.Problem.to_cnf
        @@ PCSP.Problem.to_nnf source
  in
  (* distinct, by printed form *)
  let senv = clause_senv w in
  List.dedup_and_sort cs ~compare:(fun c1 c2 ->
      String.compare (Clause.str_of senv c1) (Clause.str_of senv c2))

(* the signature the used clauses are read in: the preprocessed problem's, and
   for a finite-instance refutation also that of the problem the instantiation
   was applied to, whose unknowns a later step may have dropped from the
   signature of the [false] that replaced it *)
and clause_senv (w : UnsatWitness.t) =
  match w.body with
  | UnsatWitness.FiniteInstance { source; _ } ->
      Map.Poly.merge_skewed w.senv (PCSP.Problem.senv_of source)
        ~combine:(fun ~key:_ s _ -> s)
  | _ -> w.senv

and check_preprocessing ~id orig (w : UnsatWitness.t) =
  match w.problem with
  | None -> add empty (Unchecked "preprocessed problem not recorded")
  | Some pre ->
      let fenv = get_fenv () in
      let osenv = PCSP.Problem.senv_of orig in
      (* An existential over a sequence that its body reads only through the
         length is an arithmetic condition, and while it stands the query it
         appears in is one the solver decides neither way -- three of the
         consequence checks below were left [Unchecked] over exactly that shape.
         The replacement is exact, so applying it to both sides of a consequence
         question changes no answer that was available and makes some available
         that were not.  Preprocessing does the same to the problem it hands on;
         doing it here as well is what keeps the two sides comparable. *)
      let closed senv (uni_senv, term) =
        let phi = Logic.ExtTerm.to_old_fml senv uni_senv term in
        Evaluator.elim_seq_existentials
        @@ Formula.forall
             (Map.Poly.to_alist (Logic.to_old_sort_env_map uni_senv))
             phi
      in
      let originals =
        List.map (Set.to_list (PCSP.Problem.formulas_of orig)) ~f:(closed osenv)
      in
      (* A DEFINITION MAY MENTION AN UNKNOWN THE ORIGINAL PROBLEM DOES NOT HAVE.
         The pass that shares an argument determined by the others replaces
         [P] by [fun xs -> e(xs) && Q(kept xs)] with [Q] a fresh unknown of the
         preprocessed problem, so reading that definition in the original
         signature alone fails with an unbound name and the whole report is
         lost.  The definitions are read in the original signature extended by
         the preprocessed one; an original name keeps its original sort.  Such
         a definition is then kept out of the premises and reported per
         recorded reason, both below. *)
      let dsenv =
        (* the fresh unknown may be gone from the preprocessed signature by
           the time the witness is taken -- a later step that finds no clause
           mentioning it drops it -- but the pass records every unknown it
           introduces in the argument record, with its full argument sorts *)
        Map.Poly.fold (PCSP.Problem.args_record_of pre)
          ~init:
            (Map.Poly.merge_skewed osenv (PCSP.Problem.senv_of pre)
               ~combine:(fun ~key:_ o _ -> o))
          ~f:(fun ~key ~data:(_, sorts) acc ->
            let q = Ident.pvar_to_tvar key in
            if Map.Poly.mem acc q then acc
            else
              Map.Poly.set acc ~key:q
                ~data:(Logic.Sort.mk_fun (sorts @ [ Logic.BoolTerm.SBool ])))
      in
      (* definitions of eliminated predicates: forall xs. P xs <=> body, kept
         with the predicate so that the per-definition check below can find
         the recorded reason *)
      let named_defs =
        Map.Poly.to_alist (PCSP.Problem.sol_for_eliminated_of pre)
        |> List.filter_map ~f:(fun (pv, term) ->
            match Map.Poly.find osenv pv with
            | None -> None
            | Some _ ->
                let params, body = Logic.ExtTerm.let_lam term in
                let uni = Map.Poly.of_alist_exn params in
                let app =
                  Logic.ExtTerm.mk_var_app pv
                    (List.map params ~f:(fst >> Logic.ExtTerm.mk_var))
                in
                Some
                  ( pv,
                    closed dsenv
                      ( uni,
                        Logic.BoolTerm.and_of
                          [
                            Logic.BoolTerm.imply_of app body;
                            Logic.BoolTerm.imply_of body app;
                          ] ) ))
      in
      (* Definitions of the predicates removed by resolution.  They are not
         implied by the original clauses -- they only preserve satisfiability
         -- so they are not premises of the clause checks; but the checker must
         report them, because a refutation that reaches a false leaf through
         one of them rests on a step this stage has not re-derived.  No reason
         is recorded for a resolution, so [check_def] reports each as
         [Unchecked] ("without a recorded reason"). *)
      let resolved_defs =
        Map.Poly.to_alist (PCSP.Problem.sol_for_resolved_of pre)
        |> List.filter_map ~f:(fun (pv, term) ->
            match Map.Poly.find osenv pv with
            | None -> None
            | Some _ ->
                let params, body = Logic.ExtTerm.let_lam (Lazy.force term) in
                let uni = Map.Poly.of_alist_exn params in
                let app =
                  Logic.ExtTerm.mk_var_app pv
                    (List.map params ~f:(fst >> Logic.ExtTerm.mk_var))
                in
                Some
                  ( pv,
                    closed dsenv
                      ( uni,
                        Logic.BoolTerm.and_of
                          [
                            Logic.BoolTerm.imply_of app body;
                            Logic.BoolTerm.imply_of body app;
                          ] ) ))
      in
      (* Premises of the clause checks below.  The justification for using a
         definition as a premise is that every model of the original problem
         extends to one satisfying it -- which holds for the eliminations, and
         *not* for the [Unused] defaults: a residue's occurrences were dropped
         by clause simplification (measured on `fold_noloop_fn`: p2, p3, p4
         disappear at the "simplified" step, before any named elimination),
         while the original problem still constrains it.  Such a default would
         strengthen the premises without warrant, so it is left out; the
         preprocessed clauses do not mention those predicates anyway.  Their
         own entry in the report stays, because the printed model uses them --
         and there the [sat] check verifies them against the original
         constraints. *)
      (* Nor is a definition over an unknown that preprocessing introduced (the
         shared-argument definition [P := fun xs -> e(xs) && Q(kept xs)]): it
         carries no recorded reason, so nothing below justifies the equalities
         it imposes on [P], and a premise nothing justifies could make a
         consequence check pass.  Leaving it out costs no check that could
         otherwise pass, because after it every clause that constrained [P]
         mentions [Q] instead, and a clause over an unknown absent from the
         original problem is reported unchecked anyway. *)
      let mentions_introduced pv =
        match Map.Poly.find (PCSP.Problem.sol_for_eliminated_of pre) pv with
        | None -> false
        | Some term ->
            Set.exists (Logic.ExtTerm.fvs_of term) ~f:(fun x ->
                Map.Poly.mem dsenv x && not (Map.Poly.mem osenv x))
      in
      let defs =
        List.filter_map named_defs ~f:(fun (pv, d) ->
            match
              Map.Poly.find (PCSP.Problem.elimination_reasons_of pre) pv
            with
            | Some (PCSP.Params.Unused, _) -> None
            | _ when mentions_introduced pv -> None
            | _ -> Some d)
      in
      let erased =
        Map.Poly.filter (PCSP.Problem.args_record_of pre) ~f:(fun (arr, _) ->
            Array.exists arr ~f:not)
        |> Map.key_set
        |> Set.Poly.map ~f:Ident.pvar_to_tvar
      in
      (* The axioms are facts about the ORIGINAL predicates, so their kinds are
         read from the original problem.  The preprocessed one need not know
         them at all: once preprocessing has reduced the problem to [false]
         its kind map can be empty, and reading a kind from it then raised. *)
      let kind_axioms pvs =
        List.concat_map (Set.to_list pvs) ~f:(fun pv ->
            match Map.Poly.find osenv pv with
            | None -> []
            | Some sort -> (
                let args = Logic.Sort.args_of sort in
                let mk_params pre =
                  List.mapi args ~f:(fun i s ->
                      (Ident.Tvar (sprintf "%s%d" pre i), s))
                in
                if
                  PCSP.Problem.is_wf_pred orig pv
                  || PCSP.Problem.is_dwf_pred orig pv
                then
                  (* irreflexivity: forall xs. not WF(xs, xs) *)
                  let n = List.length args / 2 in
                  let xs = mk_params "#wa" in
                  let l = List.take xs n in
                  let app =
                    Logic.ExtTerm.mk_var_app pv
                      (List.map (l @ l) ~f:(fst >> Logic.ExtTerm.mk_var))
                  in
                  [
                    closed osenv
                      (Map.Poly.of_alist_exn l, Logic.BoolTerm.neg_of app);
                  ]
                else if PCSP.Problem.is_fn_pred orig pv then
                  let xs = mk_params "#fa" and ys = mk_params "#fb" in
                  let ins = List.drop_last_exn xs and o1 = List.last_exn xs in
                  let o2 = List.last_exn ys in
                  let app o =
                    Logic.ExtTerm.mk_var_app pv
                      (List.map (ins @ [ o ]) ~f:(fst >> Logic.ExtTerm.mk_var))
                  in
                  (* functionality and totality: the preprocessor uses both
                     (elim_triv_fn_predicate drops a body atom [FN(ins, y)]
                     with [y] fresh by totality) *)
                  [
                    closed osenv
                      ( Map.Poly.of_alist_exn (ins @ [ o1; o2 ]),
                        Logic.BoolTerm.imply_of
                          (Logic.BoolTerm.and_of [ app o1; app o2 ])
                          (Logic.BoolTerm.eq_of (snd o1)
                             (Logic.ExtTerm.mk_var (fst o1))
                             (Logic.ExtTerm.mk_var (fst o2))) );
                    closed osenv
                      ( Map.Poly.of_alist_exn ins,
                        Logic.ExtTerm.mk_exists [ o1 ] (app o1) );
                  ]
                else if PCSP.Problem.is_uniq_pred orig pv then
                  match PCSP.Problem.kind_of orig pv with
                  | Kind.Uniq (j, _) ->
                      (* single-valuedness at [j] only: the axiom a Uniq
                         predicate licenses, and nothing about totality *)
                      let xs = mk_params "#ua" and ys = mk_params "#ub" in
                      let yj = List.nth_exn ys j in
                      let ys' = List.mapi xs ~f:(fun i x -> if i = j then yj else x) in
                      let app ps =
                        Logic.ExtTerm.mk_var_app pv
                          (List.map ps ~f:(fst >> Logic.ExtTerm.mk_var))
                      in
                      let xj = List.nth_exn xs j in
                      [
                        closed osenv
                          ( Map.Poly.of_alist_exn (yj :: xs),
                            Logic.BoolTerm.imply_of
                              (Logic.BoolTerm.and_of [ app xs; app ys' ])
                              (Logic.BoolTerm.eq_of (snd xj)
                                 (Logic.ExtTerm.mk_var (fst xj))
                                 (Logic.ExtTerm.mk_var (fst yj))) );
                      ]
                  | _ -> []
                else
                  match PCSP.Problem.kind_of orig pv with
                  | (Kind.NWF (nwf, (i, j)) | Kind.Parity (nwf, (i, j))) as kind
                    -> (
                      (* first-order facts every global-WF / parity
                         family satisfies.  A diagonal member P_{i,i} is
                         irreflexive, and a two-cycle through P_{i,j} and
                         P_{j,i} is impossible — always for NWF, and for
                         Parity unless the dominant priority of the cycle is
                         accepting (Kura & Unno, Def. 3.1).  Emitted once per
                         unordered pair, only for members the original problem
                         has. *)
                      let is_nwf =
                        match kind with Kind.NWF _ -> true | _ -> false
                      in
                      let priority t =
                        Option.value ~default:0 (Map.Poly.find nwf.Kind.sigma t)
                      in
                      let accepting t =
                        match Map.Poly.find nwf.Kind.sigma t with
                        | Some p -> Set.mem nwf.Kind.acc_set p
                        | None -> true (* unknown priority: assume nothing *)
                      in
                      let n_s = List.length nwf.Kind.sorts_shared in
                      let n_x =
                        match Hashtbl.Poly.find nwf.Kind.sorts_map i with
                        | Some l -> List.length l
                        | None -> -1
                      in
                      if n_x < 0 || n_s + n_x > List.length args then []
                      else
                        let xs = mk_params "#na" in
                        let s = List.take xs n_s in
                        let x = List.take (List.drop xs n_s) n_x in
                        let y = List.drop xs (n_s + n_x) in
                        let app p l =
                          Logic.ExtTerm.mk_var_app p
                            (List.map l ~f:(fst >> Logic.ExtTerm.mk_var))
                        in
                        if Ident.tvar_equal i j then
                          if List.length y <> n_x then []
                          else if is_nwf || not (accepting i) then
                            [
                              closed osenv
                                ( Map.Poly.of_alist_exn (s @ x),
                                  Logic.BoolTerm.neg_of (app pv (s @ x @ x)) );
                            ]
                          else []
                        else
                          let mirror =
                            List.find (Set.to_list pvs) ~f:(fun pv' ->
                                match PCSP.Problem.kind_of orig pv' with
                                | Kind.NWF (nwf', (i', j'))
                                | Kind.Parity (nwf', (i', j')) ->
                                    Ident.tvar_equal nwf'.Kind.name
                                      nwf.Kind.name
                                    && Ident.tvar_equal i' j
                                    && Ident.tvar_equal j' i
                                | _ -> false)
                          in
                          match mirror with
                          | Some pv'
                            when String.(
                                   Ident.name_of_tvar pv
                                   < Ident.name_of_tvar pv') ->
                              let dominant_accepting =
                                accepting
                                  (if priority i >= priority j then i else j)
                              in
                              if is_nwf || not dominant_accepting then
                                [
                                  closed osenv
                                    ( Map.Poly.of_alist_exn (s @ x @ y),
                                      Logic.BoolTerm.neg_of
                                        (Logic.BoolTerm.and_of
                                           [
                                             app pv (s @ x @ y);
                                             app pv' (s @ y @ x);
                                           ]) );
                                ]
                              else []
                          | _ -> [])
                  | _ -> []))
      in
      let trail = PCSP.Problem.erasure_trail_of pre in
      (* the reduced predicate [P'] keeps [P]'s name with fewer arguments; for
         the check it is renamed apart and defined from [P] by the trail:
         [P'(rest) <=> Q_k xs_k ... Q_1 xs_1. P(all)], the last committed
         phase outermost, RAF positions existential, FAR positions universal
         *)
      let reduced_name pv = Ident.Pvar (Ident.name_of_tvar pv ^ "#reduced") in
      let erasure_defs pvs =
        List.filter_map (Set.to_list pvs) ~f:(fun pv ->
            let pvar = Ident.tvar_to_pvar pv in
            match
              ( Map.Poly.find (PCSP.Problem.args_record_of pre) pvar,
                Map.Poly.find trail pvar,
                Map.Poly.find osenv pv )
            with
            | Some (arr, sorts), Some rounds, Some _ ->
                let n = Array.length arr in
                let osorts = List.map sorts ~f:Logic.ExtTerm.to_old_sort in
                let xs =
                  List.mapi osorts ~f:(fun i s ->
                      (Ident.Tvar (sprintf "#er%d" i), s))
                in
                let app_orig =
                  Atom.mk_pvar_app pvar osorts
                    (List.map xs ~f:(fun (x, s) -> Term.mk_var x s))
                in
                let kept = List.filteri xs ~f:(fun i _ -> Array.get arr i) in
                let app_red =
                  Atom.mk_pvar_app (reduced_name pv) (List.map kept ~f:snd)
                    (List.map kept ~f:(fun (x, s) -> Term.mk_var x s))
                in
                let erased_positions =
                  List.concat_map rounds ~f:snd
                  |> List.dedup_and_sort ~compare:Int.compare
                in
                if
                  List.length erased_positions <> Array.count arr ~f:not
                  || List.exists erased_positions ~f:(fun i -> i >= n)
                then None (* trail and record disagree: do not guess *)
                else
                  (* rounds folded from the last phase inwards: the innermost
                     quantifier is the first phase *)
                  let body =
                    List.fold (List.rev rounds) ~init:(Formula.mk_atom app_orig)
                      ~f:(fun body (kind, ids) ->
                        let bounds = List.map ids ~f:(List.nth_exn xs) in
                        match kind with
                        | `RAF -> Formula.exists bounds body
                        | `FAR -> Formula.forall bounds body)
                  in
                  Some
                    (Formula.forall kept
                       (Formula.mk_iff (Formula.mk_atom app_red) body))
            | _ -> None)
      in
      let csenv = clause_senv w in
      let r =
        List.fold (clauses_used w) ~init:empty ~f:(fun r c ->
            let pvs = Clause.pvs_of c in
            let erased_here = Set.filter pvs ~f:(Set.mem erased) in
            let defs_er = erasure_defs erased_here in
            if Set.length erased_here <> List.length defs_er then
              add r
                (Unchecked
                   "clause over a predicate with erased arguments whose \
                    erasure trail is incomplete")
            else if Set.exists pvs ~f:(fun pv -> not (Map.Poly.mem osenv pv))
            then
              add r
                (Unchecked
                   "clause over a predicate absent from the original problem")
            else
              let goal =
                let uni_senv, term = Clause.to_senv_formula c in
                let phi = Logic.ExtTerm.to_old_fml csenv uni_senv term in
                let phi =
                  if Set.is_empty erased_here then phi
                  else
                    Formula.rename_pvars
                      (Map.of_set_exn
                      @@ Set.Poly.map erased_here ~f:(fun pv ->
                          (Ident.tvar_to_pvar pv, reduced_name pv)))
                      phi
                in
                Evaluator.elim_seq_existentials
                @@ Formula.forall
                     (Map.Poly.to_alist (Logic.to_old_sort_env_map uni_senv))
                     phi
              in
              let query =
                originals @ defs @ defs_er
                @ kind_axioms (Map.key_set osenv)
                @ [ Formula.negate goal ]
              in
              match
                (* a binder of certain sorts makes the call not return at all,
                   and the budget passed below reaches the solver as a tactic's
                   and does not hold there, so the shape is checked before
                   asking.  Reporting the check as not made is what this site
                   already does when the solver gives up, and it is the right
                   direction for a checker: a missing accusation costs less
                   than a wrong one *)
                if List.exists query ~f:Z3Smt.Z3interface.may_not_return then
                  Error
                    "a sort the query may not return on (a binder, or an occurrence)"
                else
                  try
                    Ok
                      (Z3Smt.Z3interface.check_sat_with_preds ~timeout ~id fenv
                         (List.map ~f:split_seq_reads query))
                  with e when not (Common.Timer.is_interrupt e) -> Error (Exn.to_string e)
              with
              | Ok `Unsat -> add r Passed
              | Ok `Sat ->
                  add r
                    (Failed
                       (sprintf
                          "preprocessed clause is not a consequence of the \
                           original problem: %s"
                          (Clause.str_of csenv c)))
              | Ok `Unknown ->
                  add r
                    (Unchecked
                       (sprintf "Z3 undecided on a consequence check: %s"
                          (Clause.str_of csenv c)))
              | Error msg ->
                  add r (Unchecked ("Z3 failed on a consequence check: " ^ msg)))
      in
      (* Stage 3b: the definitions
         were premises of every check above; now check the definitions
         themselves.  Which condition applies depends on *why* the
         preprocessor made each one, which is what [elimination_reasons]
         records. *)
      let orig_clauses =
        lazy
          (Set.to_list @@ PCSP.Problem.clauses_of @@ PCSP.Problem.to_cnf
         @@ PCSP.Problem.to_nnf orig)
      in
      (* The eliminator's own side condition, re-read on the original problem.
         [count_pvar_apps] does not count a clause in which [P] occurs on both
         sides (it goes to the [dc] counter), and that is sound: with [P := false]
         such a clause has a false body, with [P := true] a true head.  So
         "no lower bound" is "every clause with a positive occurrence has a
         negative one too", and dually. *)
      let occurs_in pv =
        Set.exists ~f:(fun atm ->
            Ident.tvar_equal pv (Logic.ExtTerm.pvar_of_atom atm))
      in
      (* the one-sided eliminations committed before this one: each of them
         removed *every* clause mentioning its predicate, and soundly so (with
         [P := false] such a clause has a false body, with [P := true] a true
         head), so the condition of a later step is to be read on what was left *)
      let earlier_one_sided order =
        Map.Poly.fold (PCSP.Problem.elimination_reasons_of pre)
          ~init:Set.Poly.empty ~f:(fun ~key ~data acc ->
            match data with
            | (PCSP.Params.OneSidedNoLB | OneSidedNoUB), i when i < order ->
                Set.add acc key
            | _ -> acc)
      in
      let one_sided_ok pv ~positive ~order =
        let gone = earlier_one_sided order in
        List.for_all (Lazy.force orig_clauses) ~f:(fun (_, ps, ns, phi) ->
            let mentions_gone =
              Set.exists gone ~f:(fun q -> occurs_in q ps || occurs_in q ns)
            in
            (* an application inside the clause's pure part carries no polarity
               the rule can use, and neither the eliminator's counting nor this
               check would otherwise see it: treat it as disqualifying *)
            let in_phi =
              Set.exists (Logic.ExtTerm.fvs_of phi) ~f:(Ident.tvar_equal pv)
            in
            let here, other = if positive then (ps, ns) else (ns, ps) in
            mentions_gone
            || (not in_phi)
               && ((not (occurs_in pv here)) || occurs_in pv other))
      in
      (* [Problem.elim_triv_{nwf,parity}_predicate] assumes [true] for a family
         member whose tag pair is not "non-trivial": one of its two tags never
         appears on the other side, so the member lies on no cycle.  The
         condition is syntactic and can be re-derived -- but on the clause set
         that step saw, which is the original one *after*
         [elim_unsat_{nwf,parity}_predicates] have replaced the diagonal atoms
         by [false].  That rewrite is emulated exactly: an atom is skipped when
         its two tags are equal and its left and right argument tuples are
         syntactically equal (for a Parity predicate, only when the tag's
         priority is not accepting -- that step's extra condition).  Emulating
         it too generously would shrink the tag set and pass a member that is
         on a cycle, so the arms follow the two functions literally. *)
      let triv_kind_ok pv =
        match PCSP.Problem.nwf_tag_of orig pv with
        | None -> false
        | Some (nwf, (idl, idr)) ->
            let rewritten_away atm =
              let apv = Logic.ExtTerm.pvar_of_atom atm in
              match PCSP.Problem.nwf_tag_of orig apv with
              | None -> false
              | Some (nwf', (l, r)) ->
                  Ident.tvar_equal l r
                  && (PCSP.Problem.is_nwf_pred orig apv
                     ||
                     (* a Parity tag without a priority is not a case
                        [elim_unsat_parity_predicates] rewrites; a checker must
                        not raise on it (Core's [find_exn] raises
                        [Not_found_s]) *)
                     match Map.Poly.find nwf'.Kind.sigma l with
                     | Some pri -> not (Set.mem nwf'.Kind.acc_set pri)
                     | None -> false)
                  &&
                  let _, args = Logic.ExtTerm.let_var_app atm in
                  let args =
                    List.drop args (List.length nwf'.Kind.sorts_shared)
                  in
                  List.length args % 2 = 0
                  &&
                  let l_args, r_args =
                    List.split_n args (List.length args / 2)
                  in
                  List.equal Stdlib.( = ) l_args r_args
            in
            let tags =
              List.concat_map (Lazy.force orig_clauses)
                ~f:(fun (_, ps, ns, _) ->
                  List.filter_map
                    (Set.to_list (Set.union ps ns))
                    ~f:(fun atm ->
                      if rewritten_away atm then None
                      else
                        match
                          PCSP.Problem.nwf_tag_of orig
                          @@ Logic.ExtTerm.pvar_of_atom atm
                        with
                        | Some (nwf', (l, r))
                          when Ident.tvar_equal nwf'.Kind.name nwf.Kind.name ->
                            Some (l, r)
                        | _ -> None))
            in
            let non_trivial =
              Set.inter
                (Set.Poly.of_list (List.map tags ~f:fst))
                (Set.Poly.of_list (List.map tags ~f:snd))
            in
            not (Set.mem non_trivial idl && Set.mem non_trivial idr)
      in
      let order_of pv =
        match Map.Poly.find (PCSP.Problem.elimination_reasons_of pre) pv with
        | Some (_, i) -> i
        | None -> Int.max_value
      in
      (* the definitions committed before this one.  An elimination's rule
         reads the clause set *as it then was*, which is the original one with
         the earlier definitions substituted: [P := false] "because the upper
         bound is unsatisfiable" is implied by the original clauses only once
         those substitutions are premises too.  Taking strictly earlier ones
         keeps the induction well founded -- each definition is justified
         relative to the ones already justified. *)
      let earlier_defs order =
        List.filter_map named_defs ~f:(fun (pv', d) ->
            if order_of pv' < order then Some d else None)
      in
      let check_def r (pv, def) =
        let name = Ident.name_of_tvar pv in
        match Map.Poly.find (PCSP.Problem.elimination_reasons_of pre) pv with
        | None when mentions_introduced pv ->
            add r
              (Unchecked
                 "definition over an unknown introduced by preprocessing \
                  (a shared determined argument): its equalities are not \
                  re-derived")
        | None ->
            add r
              (Unchecked
                 "definition of an eliminated predicate without a recorded \
                  reason")
        | Some (((PCSP.Params.Forced | LbValid | UbUnsat) as reason), order)
          -> (
            (* implied by the original clauses: one query decides it *)
            match
              try
                Ok
                  (Z3Smt.Z3interface.check_sat_with_preds ~timeout ~id fenv
                     (List.map ~f:split_seq_reads
                        (originals
                        @ kind_axioms (Map.key_set osenv)
                        @ earlier_defs order
                        @ [ Formula.negate def ])))
              with e when not (Common.Timer.is_interrupt e) -> Error (Exn.to_string e)
            with
            | Ok `Unsat ->
                passed_kind r ("def: " ^ PCSP.Params.str_of_elim_reason reason)
            | Ok `Sat ->
                add r
                  (Failed
                     (sprintf
                        "the definition of %s (%s) does not follow from the \
                         original problem"
                        name
                        (PCSP.Params.str_of_elim_reason reason)))
            | Ok `Unknown -> add r (Unchecked "Z3 undecided on a definition")
            | Error msg ->
                add r (Unchecked ("Z3 failed on a definition: " ^ msg)))
        | Some (((OneSidedNoLB | OneSidedNoUB) as reason), order) ->
            (* satisfiability-preserving, not implied: what is checkable is the
               rule's side condition.  Eliminations compose, so a step whose
               condition held on the clause set it saw may not show it on the
               original problem; that is [Unchecked], never [Failed] -- a
               guessed justification is worse than no check at all *)
            let positive =
              match reason with PCSP.Params.OneSidedNoLB -> true | _ -> false
            in
            if one_sided_ok pv ~positive ~order then
              passed_kind r ("def: " ^ PCSP.Params.str_of_elim_reason reason)
            else
              add r
                (Unchecked
                   (sprintf
                      "one-sided elimination of %s (%s): the polarity \
                       condition does not hold in the original problem, so an \
                       earlier step must have removed the occurrence"
                      name
                      (PCSP.Params.str_of_elim_reason reason)))
        | Some (TrivKind, _) ->
            if triv_kind_ok pv then
              passed_kind r "def: family member on no cycle"
            else
              add r
                (Unchecked
                   (sprintf
                      "%s was assumed true as a family member on no cycle, but \
                       its tag pair is non-trivial in the original problem"
                      name))
        | Some (FnOneSided, _) ->
            (* this elimination records no definition -- it replaces the
               predicate by an existential over its result and *chooses* a
               witness per argument tuple, which need not be expressible -- so
               reaching this case means a definition was recorded for a
               predicate that has none *)
            add r
              (Failed
                 (sprintf
                    "a definition was recorded for %s, which was replaced by \
                     an existential over its result and therefore has none"
                    name))
        | Some (Unused, _) ->
            (* the default is justified by the steps that removed the
               occurrences, which this stage does not re-derive.  What it can
               decide is the necessary condition: nothing in the preprocessed
               problem constrains the predicate any more.  A default recorded
               for a predicate that *is* still constrained is a bookkeeping
               error, and the model built from it would be wrong. *)
            if
              List.exists
                (Set.to_list (PCSP.Problem.clauses_of pre))
                ~f:(fun (_, ps, ns, _) -> occurs_in pv ps || occurs_in pv ns)
            then
              add r
                (Failed
                   (sprintf
                      "a default solution was recorded for %s, but the \
                       preprocessed problem still constrains it"
                      name))
            else
              add r
                (Unchecked
                   (sprintf
                      "%s: an unconstrained residue -- nothing constrains it \
                       any more, but the steps that removed its occurrences \
                       are not re-derived"
                      name))
      in
      List.fold (named_defs @ resolved_defs) ~init:r ~f:check_def

(* A refutation at one finite cardinality of the quantified sorts.  What makes
   it a refutation of the problem: a universally quantified sort is
   uninterpreted, a theory model may give it any non-empty carrier, and the
   system is satisfiable only when every model admits a solution -- so a model
   with [size]-element carriers that admits none refutes it.  Replacing each
   sort by a datatype with [size] nullary constructors is reading the problem
   in such a model (a carrier is fixed up to isomorphism by its size, an array
   over a finite index is fixed by its reads, and the datatypes built over the
   sort are their term algebras there too), so what has to be checked is:

   - that the substitution names such datatypes, [size] nullary constructors
     each, of at least one element;
   - that the environments the instance was substituted from agree with this
     process's wherever they define a name, the enumerations aside, since the
     instance is re-derived from them;
   - that the unknowns of the substituted problem carry the kinds they carry in
     the original problem, a kind being part of the question;
   - that the nested refutation is a refutation of the instance as re-derived
     here -- its own witness check, and its clauses consequences of the
     re-derived instance, which is what ties it to the instance this code
     builds and not to a recorded copy.

   That the substituted problem's clauses follow from the original problem is
   the preprocessing check's, over [clauses_used].  Anything not shown is
   reported [Unchecked] with its reason; nothing here can report [Failed],
   because a nested check that fails exhibits no model of the original problem
   in which it has no solution. *)
and check_finite_instance ~id orig (fi : UnsatWitness.finite_instance) =
  let unchecked why = Unchecked (sprintf "finite instance of size %d: %s" fi.size why) in
  let enumeration = function
    | T_dt.SDT dt as srt ->
        CellQual.is_finite_sort_instance srt
        && Stdlib.(Datatype.flag_of dt = Datatype.FDt)
        && List.is_empty (Datatype.params_of dt)
        && List.length (Datatype.dts_of dt) = 1
        && List.length (Datatype.conses_of dt) = fi.size
        && List.for_all (Datatype.conses_of dt) ~f:(fun c ->
               List.is_empty (Datatype.sorts_of_cons dt c))
    | _ -> false
  in
  (* structural equality where it can be decided; a value it cannot compare
     counts as a disagreement, which leaves the certificate unchecked *)
  let same a b =
    phys_equal a b || try Stdlib.(a = b) with Invalid_argument _ -> false
  in
  let enumeration_names =
    Set.Poly.of_list
    @@ List.filter_map (Map.Poly.data fi.smap) ~f:(function
         | T_dt.SDT dt -> Some (Datatype.name_of dt)
         | _ -> None)
  in
  let agrees recorded current ~skip =
    Map.Poly.for_alli recorded ~f:(fun ~key ~data ->
        skip key
        ||
        match Map.Poly.find current key with
        | Some data' -> same data data'
        | None -> false)
  in
  let is_fin name =
    CellQual.is_finite_sort_instance
      (T_dt.SDT (Datatype.make name [ Datatype.mk_dt name [] ] Datatype.FDt))
  in
  let osenv = PCSP.Problem.senv_of orig in
  if fi.size < 1 || Map.Poly.is_empty fi.smap then unchecked "no finite sort"
  else if not (Map.Poly.for_all fi.smap ~f:enumeration) then
    unchecked "a substituted sort is not an enumeration of that size"
  else if
    not
      (Map.Poly.for_alli fi.smap ~f:(fun ~key:_ ~data ->
           match data with
           | T_dt.SDT dt -> (
               match Map.Poly.find fi.dtenv (Datatype.name_of dt) with
               | Some dt' -> same dt dt'
               | None -> false)
           | _ -> false))
  then unchecked "an enumeration is not the one the environment defines"
  else if
    not
      (agrees fi.dtenv (get_dtenv ()) ~skip:(fun name ->
           Set.mem enumeration_names name || is_fin name)
      && agrees fi.fenv (get_fenv ()) ~skip:(fun _ -> false))
  then
    unchecked
      "the environments it was substituted from disagree with this process's"
  else if
    not
      (Map.Poly.for_alli (PCSP.Problem.senv_of fi.source) ~f:(fun ~key ~data:_ ->
           Map.Poly.mem osenv key
           && String.equal
                (Kind.str_of (PCSP.Problem.kind_of fi.source key))
                (Kind.str_of (PCSP.Problem.kind_of orig key))))
  then unchecked "an unknown's kind differs from the original problem's"
  else if not (try_enter_env_bracket ()) then
    unchecked "the global environments are held elsewhere"
  else
    (* the instance is read in its own environments, installed process-wide
       as the nested solve had them, and every pooled solver context is
       dropped on the way in and on the way out: a context keeps the datatypes
       it has declared, and the instance uses the original names at other
       sorts *)
    let saved_dtenv = get_dtenv () and saved_fenv = get_fenv () in
    let restore () =
      set_fenv saved_fenv;
      set_dtenv saved_dtenv;
      Z3Smt.Z3interface.clear_instance_pool ();
      leave_env_bracket ()
    in
    let run () =
      let dtenv_substituted, fenv_substituted =
        Preprocessing.Preprocessor.finite_instance_envs fi.smap fi.dtenv fi.fenv
      in
      set_dtenv dtenv_substituted;
      set_fenv fenv_substituted;
      Z3Smt.Z3interface.clear_instance_pool ();
      let instance =
        Preprocessing.Preprocessor.finite_instance_problem fi.smap
          ~dtenv_substituted ~fenv_substituted fi.source
      in
      ( check_unsat_witness ~id instance fi.nested,
        check_preprocessing ~id instance fi.nested )
    in
    match run () with
    | exception e when Common.Timer.is_async e ->
        restore ();
        raise e
    | exception e ->
        restore ();
        unchecked ("the nested check raised: " ^ Exn.to_string e)
    | r1, r2 -> (
        restore ();
        let first r =
          match (r.failed, r.unchecked) with
          | msg :: _, _ -> Some ("failed: " ^ msg)
          | [], (why, _) :: _ -> Some why
          | [], [] -> None
        in
        match (first r1, first r2) with
        | Some why, _ -> unchecked ("the nested refutation is not certified: " ^ why)
        | None, Some why ->
            unchecked
              ("the nested refutation's clauses are not shown to follow from \
                the instance: " ^ why)
        | None, None ->
            if r1.passed = 0 then unchecked "the nested check checked nothing"
            else Passed)

let check ?(seq_as_array = false) ?(retry = false) ?matched ?ladder ~id pcsp
    (solution, (info : State.info)) =
  match solution with
  | PCSP.Problem.Sat sol ->
      Some
        (str_of_report "sat"
           (check_sat_solution ~seq_as_array ~retry ?matched ?ladder ~id
              ~certs:info.kind_certificates pcsp sol))
  | PCSP.Problem.Unsat _ -> (
      match info.unsat_witness with
      | Some w ->
          Some
            (str_of_report "unsat" (check_unsat_witness ~id pcsp w)
            ^ "\n"
            ^ str_of_report "preprocessing" (check_preprocessing ~id pcsp w))
      | None -> Some "(unsat-check (no-witness-recorded))")
  | _ -> None
