(** The Houdini-style pre-pass of the PCSat validator: the candidate atoms per
    unknown ([Candidates]), the greatest fixed point of the clauses with an
    unknown in the head over them, its final check against every clause, and
    when the pre-pass runs against the CEGIS loop (before the first round, at
    a round boundary, or raced in a forked copy).

    A functor over the validator's clause checks ([V]): every question the
    fixed point asks is the validator's own, with its budgets and its guards
    against queries that may not return.  The state the two share while the
    pre-pass runs (its deadline, which kind of question is being asked, the
    countermodel judge) is [V.window], a value the validator creates and its
    checks read; this module sets and restores it around each question. *)

open Core
open Common.Ext
open Common.Util
open Common.Combinator
open PCSatCommon
open Ast
open Ast.LogicOld

(* the validator's side of the pre-pass *)
module type ValidatorChecks = sig
  val window : Window.t
  (** the state shared with the clause checks while the pre-pass runs *)

  val id : int option

  module Debug : sig
    val print : ?id:int option -> string Lazy.t -> unit
  end

  val check_clause_nonparam :
    ?timeout:int option ->
    ?verdict_only:bool ->
    FunEnv.t ->
    Formula.t ->
    [ `Sat of PCSatCommon.ScalarDiversity.model
    | `Timeout
    | `Unknown of string
    | `Unsat ]
  (** whether a clause without parameters holds: [`Unsat] when its negation
      has no model, under the validator's budgets and guards *)

  val find_all_counterexamples :
    ?record:(ExClause.t -> TermSubst.t -> unit) ->
    ?stop:(unit -> bool) ->
    ?retry_undecided:
      (Formula.t ->
      [ `Sat of model | `Timeout | `Unknown of string | `Unsat ] ->
      [ `Sat of model | `Timeout | `Unknown of string | `Unsat ]) ->
    (Clause.t, 'a) Set.t ->
    FunEnv.t ->
    CandSol.t ->
    (ExClause.t * (ClauseGraph.vertex * bool) Set.Poly.t) Set.Poly.t
  (** the validator's check of a candidate against every clause *)

  val timeout_for : Formula.t -> int option
  val negation_asked : Formula.t -> Formula.t
  val cap_ms : int -> int
  val elapsed_since : Time_float.t -> float
  val binds_sequence_existentially : Formula.t -> bool
end

module Make
    (Cfg : ValidatorConfig.ConfigType)
    (APCSP : PCSP.Problem.ProblemType)
    (V : ValidatorChecks) =
struct
  open V

  (* the names the pre-pass is written in, not exported *)
  open struct
    module Config = ValidatorConfig
    module HoudiniCandidates = Candidates
    module HoudiniByModel = ByModel

    let config = Cfg.config
    let houdini_deadline = window.deadline
    let houdini_judged_drops = window.judged_drops
    let houdini_pending_judge = window.pending_judge
    let houdini_atom_model_drops = window.atom_model_drops
    let houdini_shared_body_proofs = window.shared_body_proofs
    let houdini_shared_body_refutations = window.shared_body_refutations
    let houdini_skip_weakened_once = window.skip_weakened_once
    let houdini_in_final = window.in_final
    let in_houdini_fixed_point = window.in_fixed_point
    let in_houdini_atom_question = window.in_atom_question
    let in_houdini_conjunction_question = window.in_conjunction_question
    let in_houdini_seq_instantiation = window.in_seq_instantiation
    let houdini_instr_pass = window.instr_pass
    let houdini_instr_clause = window.instr_clause
    let houdini_instr_premise = window.instr_premise
    let houdini_budget_spent () = Window.budget_spent window
    let houdini_budget_nearly_spent () = Window.budget_nearly_spent window
    let cap_timeout t = Window.cap_timeout window t
  end

  (* A Houdini-style first candidate (after Flanagan and Leino, "Houdini, an
     Annotation Assistant for ESC/Java", FME 2001) from the candidate atoms the
     input declared ([(set-info :candidates ...)]) and, with
     [houdini_extracted_qualifiers] or [houdini.candidates.defined_body_atoms], atoms the
     tool generates itself ([houdini_candidates]): each unknown starts as the
     conjunction of its candidate atoms (an unknown with none as [true]), and an
     atom is dropped while some clause, with the current conjunctions in its
     body, is not valid with that atom alone in its head.  The loop stops when a
     pass drops nothing; since every pass but the last drops an atom, it makes
     at most (atoms + 1) passes, each asking at most one question per remaining
     atom per (clause, head atom) pair.  Where the atoms come from does not
     matter to what follows: a generated atom is kept only as a declared one
     is, by the same questions.  A question the solver
     leaves undecided (budget, [unknown]) drops the atom, as a refutation would.
     With [houdini.budget_ms], this function runs under the pre-pass's one
     wall-clock budget ([with_houdini_deadline]; [houdini_outcome]'s final
     check shares it): candidate generation stops when it runs out, each
     question is given at most what is left of it, and once it is spent no
     question is asked and this function returns [None] -- every atom still
     unconfirmed would count as undecided and be dropped, which leaves nothing
     to try.

     The fixed point is inductive for the clauses with an unknown in the head;
     it is a solution only if the goal clauses hold as well, and that is not
     assumed: this function returns the fixed point unchecked, and
     [houdini_outcome] reports it as a solution only after
     [find_all_counterexamples] has checked it against every clause, exactly as
     a synthesized candidate is checked.  So the pre-pass cannot make an answer
     wrong; what it can do is answer early, hand the check's counterexamples on
     as ordinary examples, or cost the questions above and change nothing.
     [None] means there is nothing to try.

     Each question is the validator's own [check_clause_nonparam], with its
     budgets and its guards against queries that may not return.  Only problems
     whose unknowns are all of the ordinary kind are tried: [true] and a
     conjunction of atoms carry no certificate for a well-foundedness or a
     totality demand. *)
  (* whether the pre-pass generates candidates of its own; a function,
     since a reconstruction pass run by the solver after this module is
     made can switch the reconstructed-function family on *)
  let houdini_generates () =
    Option.is_some config.houdini_extracted_qualifiers
    || config.houdini.candidates.defined_body_atoms > 0
    || config.houdini.candidates.rec_fun_apps > 0
    || Atomic.get PCSatCommon.RecFunReconstruct.qual_limit > 0
    || config.houdini.candidates.frame_equations > 0
    || config.houdini.candidates.contract_memberships > 0
    || config.houdini.candidates.oriented_inequalities > 0
    || config.houdini.candidates.quantified_facts > 0
    || config.houdini.candidates.relation_inclusions > 0
    || config.houdini.candidates.guarded_inclusions > 0
    || config.houdini.candidates.exists_memberships > 0
    || config.houdini.candidates.guarded_frame_equations > 0
    || config.houdini.candidates.empty_guarded_frames > 0
    || config.houdini.candidates.length_sums > 0
    || config.houdini.candidates.last_element_equations > 0
    || config.houdini.candidates.affine_elements > 0
    || config.houdini.candidates.prefix_elements > 0
    || config.houdini.candidates.three_term_equations > 0
    || config.houdini.candidates.guarded_orders > 0
    || config.houdini.candidates.shifted_elements > 0
    || config.houdini.candidates.affix_elements > 0
    || config.houdini.candidates.concat_equations > 0
    || config.houdini.candidates.constructor_cases > 0

  (* The atoms the pre-pass generates for each unknown, over [x1 ... xn] (the
     names every qualifier of an unknown is written over), before
     [HoudiniCandidates.merge] filters and caps them.  Computed when the
     pre-pass first asks and kept, from the problem this validator was built with and
     the process-global definitions the parser registered -- never from the
     synthesizer's state -- so it is the same whether or not the synthesizer
     has extracted its qualifiers by then (the pre-pass can run before the
     first synthesis).  A generator that raises gives no atom for that
     unknown.  [stop] is asked before each unknown, between its generators
     and inside the generators' loops; once it holds the generation is
     abandoned, [None] is returned and nothing is kept, so a later call
     starts again.  The extraction ([houdini_extracted_qualifiers]) is one
     call into the qualifier generator and is not interrupted inside.  The
     atoms are kept per class (the name of the switch that
     produced them), both polarities of each, for the census below; they live
     here and in the pre-pass's questions only, and never reach the
     synthesizer's qualifiers or the problem's declared atoms. *)
  (* whether the pre-pass runs in two rounds
     ([houdini.candidates.inclusions.second_round] with both inclusion counts positive) *)
  let houdini_two_rounds =
    (HoudiniConfig.Switch.inclusions_second_round config.houdini)
    && config.houdini.candidates.relation_inclusions > 0
    && config.houdini.quotas.inclusion > 0

  (* whether the round being run generates the inclusion family; [false] only
     inside round 1 of a two-round pre-pass, where the family is the empty
     list it is with [houdini.candidates.relation_inclusions = 0] *)
  let houdini_with_inclusions = ref true

  (* [Some (with_inclusions, m)]: the atoms generated, and whether [m] holds
     the inclusion family or has it empty *)
  let houdini_generated_cache = ref None

  let houdini_inclusion_family ~stop args =
    HoudiniCandidates.inclusions ~stop ~limit:config.houdini.candidates.relation_inclusions
      ~skip_constructor_equations:
        (config.houdini.candidates.inclusions.skip_constructor_equations
        && config.houdini.candidates.frame_equations > 0)
      ~defs:(LogicOld.get_inlined_defs ()) args

  (* the ranges the input states for a bound integer variable
     ([HoudiniCandidates.range_guards]), read once from the input's own
     assertions and the problem's clauses; [[]] with
     [houdini.candidates.guarded_inclusions = 0], where nothing is read *)
  let houdini_range_guards =
    lazy
      (if config.houdini.candidates.guarded_inclusions <= 0 then []
       else
         HoudiniCandidates.range_guards ~limit:4
           (HoudiniCandidates.input_quantified_group ()
           @ Set.to_list (PCSP.Problem.old_formulas_of APCSP.problem)))

  let houdini_guarded_inclusion_family ~stop args =
    HoudiniCandidates.guarded_inclusions ~stop
      ~limit:config.houdini.candidates.guarded_inclusions
      ~skip_constructor_equations:
        (config.houdini.candidates.inclusions.skip_constructor_equations
        && config.houdini.candidates.frame_equations > 0)
      ~guards:(Lazy.force houdini_range_guards)
      ~defs:(LogicOld.get_inlined_defs ()) args

  (* the families generated only when the inclusions are wanted (round 2
     of a two-round pre-pass) *)
  let is_inclusion_family name =
    String.equal name "inclusion" || String.equal name "guarded-inclusion"

  let houdini_print_family key args name atoms =
    if not (List.is_empty atoms) then
      Debug.print
      @@ lazy
           (sprintf "[houdini] %s over %s: %s (%d): %s"
              (Ident.name_of_tvar key)
              (String.concat_map_list ~sep:"," args
                 ~f:(fst >> Ident.name_of_tvar))
              name (List.length atoms)
              (String.concat_map_list ~sep:" | " atoms ~f:Formula.str_of))

  (* the parameters of [key] its loops pass on unchanged, for
     [houdini.candidates.quantified_facts_frame_only] ([[]] with the switch off) *)
  let houdini_frame_args key (args : sort_env_list) =
    if not config.houdini.candidates.quantified_facts_frame_only then []
    else
      let pos =
        HoudiniCandidates.frame_positions
          (Set.to_list (PCSP.Problem.clauses_of APCSP.problem))
          key
      in
      let frame = List.filteri args ~f:(fun i _ -> List.mem pos i ~equal:( = )) in
      Debug.print
      @@ lazy
           (sprintf "[houdini] %s: frame parameters %s" (Ident.name_of_tvar key)
              (String.concat_map_list ~sep:"," frame ~f:(fst >> Ident.name_of_tvar)));
      frame

  let houdini_generated_atoms ~stop =
    let want = !houdini_with_inclusions in
    match !houdini_generated_cache with
    | Some (w, m) when Bool.equal w want -> Some m
    | Some (true, m) ->
        (* the inclusions held but not wanted: the family emptied *)
        Some
          (Map.Poly.map m ~f:(fun (args, fams) ->
               ( args,
                 List.map fams ~f:(fun (name, atoms) ->
                     if is_inclusion_family name then (name, [])
                     else (name, atoms)) )))
    | Some (false, m) -> (
        (* round 2 after round 1: only the inclusion family is generated, in
           its place among the families, so the atoms are those a one-round
           generation gives; a generator that raises gives no atom for that
           unknown, as it does there *)
        match
          Map.Poly.mapi m ~f:(fun ~key ~data:(args, fams) ->
              HoudiniCandidates.poll stop;
              if List.is_empty fams then (args, fams)
              else
                try
                  let inc = houdini_inclusion_family ~stop args in
                  houdini_print_family key args "inclusion" inc;
                  let ginc = houdini_guarded_inclusion_family ~stop args in
                  houdini_print_family key args "guarded-inclusion" ginc;
                  (* an instrument, as in the one-round generation below *)
                  if not (List.is_empty ginc) then
                    Common.PhaseTime.event_here
                      "houdini-family-nonempty/guarded-inclusion";
                  ( args,
                    List.map fams ~f:(fun (name, atoms) ->
                        if String.equal name "inclusion" then (name, inc)
                        else if String.equal name "guarded-inclusion" then
                          (name, ginc)
                        else (name, atoms)) )
                with
                | HoudiniCandidates.Budget_spent as exn_ -> raise exn_
                | exn_ when not (Common.Timer.is_async exn_) ->
                    Debug.print
                    @@ lazy
                         (sprintf "[houdini] no generated atom for %s: %s"
                            (Ident.name_of_tvar key) (Exn.to_string exn_));
                    (args, []))
        with
        | m ->
            houdini_generated_cache := Some (true, m);
            Some m
        | exception HoudiniCandidates.Budget_spent ->
            Debug.print
            @@ lazy "[houdini] budget spent while generating candidates";
            None)
    | None -> (
       let poll = HoudiniCandidates.poll in
       let senv = PCSP.Problem.senv_of APCSP.problem in
       let args_of data =
         sort_env_list_of_sorts
         @@ List.map (Logic.Sort.args_of data) ~f:Logic.ExtTerm.to_old_sort
       in
       let extracted =
         match config.houdini_extracted_qualifiers with
         | None -> fun _ _ -> []
         | Some gcfg ->
             (* loaded here as well as by [instantiate_ext_files]: a validator
                config written inline ([Instance]) is not instantiated by the
                loader, so a nested [Filename] can still arrive here *)
             let gcfg =
               match
                 Or_error.(
                   Qualifier.Generator.Config.load_ext_file gcfg
                   >>= ExtFile.unwrap)
               with
               | Ok c -> c
               | Error e -> Error.raise e
             in
             let module G =
               Qualifier.Generator.Make
                 (struct
                   let config = gcfg
                 end)
                 (APCSP)
             in
             fun key args ->
               List.map ~f:snd @@ Set.to_list
               @@ G.generate (Ident.tvar_to_pvar key) args Set.Poly.empty
                    (Map.Poly.empty, ClauseGraph.create ())
                    0
       in
       let defined args =
         if config.houdini.candidates.defined_body_atoms <= 0 then []
         else
           Template.PredicateArrays.defined_body_quals
             ~limit:config.houdini.candidates.defined_body_atoms
             ~defs:(LogicOld.get_inlined_defs ()) args
       in
       (* the problem's clauses and the input's own assertions: a
          preprocessing step can remove a quantifier the input stated *)
       let sources =
         lazy
           [
             HoudiniCandidates.input_quantified_group ();
             Set.to_list (PCSP.Problem.old_formulas_of APCSP.problem);
           ]
       in
       (* the element sorts of the sequences the problem's clauses build by
          concatenation, read once *)
       let concatenated_sorts =
         lazy
           (HoudiniCandidates.concatenated_elem_sorts
              (Set.to_list (PCSP.Problem.old_formulas_of APCSP.problem)))
       in
       (* one family at a time, [stop] asked before each *)
       let families key args =
         let open HoudiniCandidates in
         let quantified_split =
           lazy
             (if config.houdini.candidates.quantified_facts <= 0 then ([], [])
              else
                quantified_facts_split ~stop
                  ~closed_beside:
                    config.houdini.candidates.quantified_facts_closed_beside
                  ~limit:config.houdini.candidates.quantified_facts
                  ~frame:(houdini_frame_args key args)
                  ~sources:(Lazy.force sources) args)
         in
         List.map
           [
             ( "frame",
               fun () ->
                 frame_equations ~stop ~limit:config.houdini.candidates.frame_equations
                   args );
             ( "membership",
               fun () ->
                 memberships ~stop ~limit:config.houdini.candidates.contract_memberships
                   ~defs:(LogicOld.get_inlined_defs ()) args );
             ( "inequality",
               fun () ->
                 inequalities ~stop ~limit:config.houdini.candidates.oriented_inequalities
                   args );
             ( "quantified",
               fun () -> fst (Lazy.force quantified_split) );
             (* the closed atoms of the family and the open ones they
                displaced, offered outside its limit and every quota
                ([houdini.candidates.quantified_facts_closed_beside]); empty
                with the switch off *)
             ( "quantified-closed",
               fun () -> snd (Lazy.force quantified_split) );
             ( "inclusion",
                 fun () ->
                   if want then houdini_inclusion_family ~stop args else [] );
             ( "guarded-inclusion",
                 fun () ->
                   if want then houdini_guarded_inclusion_family ~stop args
                   else [] );
             ( "exists-membership",
               fun () ->
                 exists_memberships ~stop
                   ~array_pairs:config.houdini.candidates.array_pair_memberships
                   ~limit:config.houdini.candidates.exists_memberships args );
             ( "guarded-frame",
               fun () ->
                 guarded_frame_equations ~stop
                   ~limit:config.houdini.candidates.guarded_frame_equations args );
             ( "empty-guarded-frame",
               fun () ->
                 empty_guarded_frames ~stop
                   ~limit:config.houdini.candidates.empty_guarded_frames args );
             ( "length_sum",
               fun () ->
                 length_sums ~stop ~limit:config.houdini.candidates.length_sums args );
             ( "last-element",
               fun () ->
                 last_element_equations ~stop
                   ~limit:config.houdini.candidates.last_element_equations args );
             ( "affine_element",
               fun () ->
                 affine_elements ~stop ~limit:config.houdini.candidates.affine_elements
                   args );
             ( "prefix-element",
               fun () ->
                 if config.houdini.candidates.prefix_elements <= 0 then []
                 else
                   prefix_elements ~stop ~limit:config.houdini.candidates.prefix_elements
                     ~consts:
                       (input_int_literals ~n:4)
                     args );
             ( "three_term",
               fun () ->
                 three_term_equations ~stop
                   ~limit:config.houdini.candidates.three_term_equations args );
             ( "guarded_order",
               fun () ->
                 guarded_orders ~stop ~limit:config.houdini.candidates.guarded_orders args
             );
             (* the problem's own clauses decide the element sorts: only a
                sequence some clause builds by concatenation can be one
                sequence followed by another *)
             ( "shifted-element",
               fun () ->
                 if config.houdini.candidates.shifted_elements <= 0 then []
                 else
                   shifted_elements ~stop
                     ~limit:config.houdini.candidates.shifted_elements
                     ~elem_sorts:(Lazy.force concatenated_sorts) args );
             (* prefix and suffix relations between two reached sequences *)
             ( "affix-element",
               fun () ->
                 affix_elements ~stop
                   ~limit:config.houdini.candidates.affix_elements args );
             ( "concat-equation",
               fun () ->
                 if config.houdini.candidates.concat_equations <= 0 then []
                 else
                   concat_equations ~stop
                     ~limit:config.houdini.candidates.concat_equations
                     ~elem_sorts:(Lazy.force concatenated_sorts) args );
             (* inside the cases of a multi-constructor datatype, which the
                families above do not reach: the same scalar families over
                each opened view, at their own limits *)
             ( "constructor-case",
               fun () ->
                 let c = config.houdini.candidates in
                 (* [COAR_HOUDINI_CC_CENSUS] set (an instrument): with the
                    family off, its atoms are still built at the limit 24 and
                    the event [houdini-constructor-cases-would-offer] is
                    counted when there are any, so that a run under any
                    configuration says whether the family could act on its
                    input; nothing is offered *)
                 let census =
                   c.constructor_cases <= 0
                   && Option.is_some (Sys.getenv "COAR_HOUDINI_CC_CENSUS")
                 in
                 let atoms =
                   constructor_cases ~stop
                     ~limit:(if census then 24 else c.constructor_cases)
                     ~families:(fun view ->
                       [
                         frame_equations ~stop ~limit:c.frame_equations view;
                         inequalities ~stop ~limit:c.oriented_inequalities view;
                         length_sums ~stop ~limit:c.length_sums view;
                         affine_elements ~stop ~limit:c.affine_elements view;
                         three_term_equations ~stop ~limit:c.three_term_equations
                           view;
                         guarded_orders ~stop ~limit:c.guarded_orders view;
                         empty_guarded_frames ~stop ~limit:c.empty_guarded_frames
                           view;
                       ])
                     args
                 in
                 if census then (
                   if not (List.is_empty atoms) then
                     Common.PhaseTime.event_here
                       "houdini-constructor-cases-would-offer";
                   [])
                 else atoms );
             ( "rec_fun_app",
               fun () ->
                 Template.PredicateArrays.rec_fun_app_quals
                   ~limit:config.houdini.candidates.rec_fun_apps
                   ~fenv:(LogicOld.get_fenv ()) args );
             (* the functions a reconstruction pass added (the solver's
                [recursive_functions.reconstruction]), as in the template *)
             ( "reconstructed_fun_app",
               fun () ->
                 let names =
                   Set.union
                     (Atomic.get PCSP.Problem.reconstructed_functions)
                     (Atomic.get PCSP.Problem.reconstruction_aliases)
                 in
                 if Set.is_empty names then []
                 else
                   Template.PredicateArrays.rec_fun_app_quals
                     ~bool_equalities:true
                     ~limit:(Atomic.get PCSatCommon.RecFunReconstruct.qual_limit)
                     ~fenv:
                       (Map.Poly.filter_keys (LogicOld.get_fenv ())
                          ~f:(Set.mem names))
                     args );
           ]
           ~f:(fun (name, gen) ->
             poll stop;
             let atoms = Common.PhaseTime.with_phase name gen in
             (* an instrument, deciding nothing: with the phase account on,
                one event per unknown a family builds at least one atom for,
                counted in the row [houdini-family-nonempty/<family>] (or
                printed at once in a forked copy, where the pre-pass usually
                runs), so a run says whether a family acted on its input at
                all *)
             if not (List.is_empty atoms) then
               Common.PhaseTime.event_here ("houdini-family-nonempty/" ^ name);
             (name, atoms))
       in
       match
       Map.Poly.mapi senv ~f:(fun ~key ~data ->
           poll stop;
           let args = args_of data in
           let atoms =
             try
               let ex =
                 Common.PhaseTime.with_phase "extracted" (fun () ->
                     extracted key args)
               in
               poll stop;
               let de =
                 Common.PhaseTime.with_phase "defined" (fun () -> defined args)
               in
               let fam = families key args in
               Debug.print
               @@ lazy
                    (sprintf
                       "[houdini] %s over %s: extracted (%d): %s; defined (%d): %s"
                       (Ident.name_of_tvar key)
                       (String.concat_map_list ~sep:"," args ~f:(fst >> Ident.name_of_tvar))
                       (List.length ex)
                       (String.concat_map_list ~sep:" | " ex ~f:Formula.str_of)
                       (List.length de)
                       (String.concat_map_list ~sep:" | " de ~f:Formula.str_of));
               List.iter fam ~f:(fun (name, atoms) ->
                   houdini_print_family key args name atoms);
               (* the generated families are offered as they are: each already
                  holds the orientations that matter (both orders of a
                  pair), and the negation of an equation or of a membership
                  is rarely an invariant, while every candidate costs its
                  questions *)
               ("extracted", HoudiniCandidates.both_polarities ex)
               :: ("defined", HoudiniCandidates.both_polarities de)
               :: fam
             with
             | HoudiniCandidates.Budget_spent as exn_ -> raise exn_
             | exn_ when not (Common.Timer.is_async exn_) ->
               Debug.print
               @@ lazy
                    (sprintf "[houdini] no generated atom for %s: %s"
                       (Ident.name_of_tvar key) (Exn.to_string exn_));
               []
           in
           (args, atoms))
       with
       | m ->
           houdini_generated_cache := Some (want, m);
           Some m
       | exception HoudiniCandidates.Budget_spent ->
           Debug.print
           @@ lazy "[houdini] budget spent while generating candidates";
           None)

  (* the datatypes the problem's own clauses use, which a generated atom must
     agree with; empty (no check) if the clauses themselves do not agree *)
  let houdini_problem_dtenv =
    lazy
      (try
         DTEnv.of_formula @@ Formula.and_of @@ Set.to_list
         @@ PCSP.Problem.old_formulas_of APCSP.problem
       with exn_ when not (Common.Timer.is_async exn_) -> Map.Poly.empty)

  (* the candidate atoms of each unknown: the declared ones, and with
     generation on, the generated ones renamed onto the declared parameters
     (onto [x1 ... xn] when nothing is declared) and merged with them; none at
     all when [stop] ended the generation *)
  (* With COAR_HOUDINI_FAMILY_LOG set in the environment, the pre-pass says
     on stderr, per candidate atom, which generating family offered it and
     how it left the fixed point (or that it stayed), one line each:
       houdini-family: <event> <unknown> <family> pass=<i> clause=<j> rank=<k>
     where <event> is [offered], [model-drop] (a countermodel of a
     conjunction question judged it false; <k> is that countermodel's rank
     among those of the same unknown and clause in the pass, 1 the first),
     [atom-refuted], [atom-undecided], [unasked] (budget spent or clause
     stalled) or [kept].  An instrument: it decides nothing.  The family is
     looked up by the atom's printed form after the renaming onto the
     declared parameters; an atom the merge rewrote is [unknown]. *)
  let houdini_family_log =
    Stdlib.(Sys.getenv_opt "COAR_HOUDINI_FAMILY_LOG" <> None)

  let houdini_family_of : (string, string) Hashtbl.t = Hashtbl.create (module String)

  let houdini_family_key p a = Ident.name_of_tvar p ^ "|" ^ Formula.str_of a

  let houdini_family_event ?(pass = 0) ?(clause = 0) ?(rank = 0) event p a =
    if houdini_family_log then (
      let fam =
        Option.value ~default:"unknown"
          (Hashtbl.find houdini_family_of (houdini_family_key p a))
      in
      Out_channel.output_string stderr
        (sprintf "houdini-family: %s %s %s pass=%d clause=%d rank=%d\n" event
           (Ident.name_of_tvar p) fam pass clause rank);
      Out_channel.flush stderr)

  (* set while the pre-pass runs over the declared atoms alone
     ([houdini.declared_first]) *)
  let houdini_declared_only = ref false

  let houdini_candidates ?(stop = fun () -> false) senv params =
    let generates = houdini_generates () && not !houdini_declared_only in
    match
      if generates then houdini_generated_atoms ~stop
      else Some Map.Poly.empty
    with
    | None -> Map.Poly.empty
    | Some generated_atoms ->
    Map.Poly.filter_mapi senv ~f:(fun ~key ~data ->
        let sorts =
          List.map (Logic.Sort.args_of data) ~f:Logic.ExtTerm.to_old_sort
        in
        let declared = PCSP.Params.candidate_atoms_at params key sorts in
        if not generates then declared
        else
          let args, generated =
            Map.Poly.find_exn generated_atoms key
          in
          let xs, decl =
            match declared with Some e -> e | None -> (args, [])
          in
          let sub =
            Map.Poly.of_alist_exn
            @@ List.map2_exn args xs ~f:(fun (y, _) (x, s) ->
                (y, Term.mk_var x s))
          in
          let generated =
            Common.PhaseTime.with_phase "rename" @@ fun () ->
            List.map generated ~f:(fun (name, atoms) ->
                (name, List.map atoms ~f:(Formula.subst sub)))
          in
          let atoms =
            Common.PhaseTime.with_phase "merge" @@ fun () ->
            let exists_mems, generated' =
              List.partition_tf generated
                ~f:(fst >> String.equal "exists-membership")
            in
            let guarded_frames, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "guarded-frame")
            in
            let empty_guarded, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "empty-guarded-frame")
            in
            let prefix_elems, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "prefix-element")
            in
            let last_elems, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "last-element")
            in
            let shifted_elems, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "shifted-element")
            in
            let affix_elems, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "affix-element")
            in
            let concat_eqs, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "concat-equation")
            in
            let constructor_cases, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "constructor-case")
            in
            let guarded_incls, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "guarded-inclusion")
            in
            let closed_quantified, generated' =
              List.partition_tf generated'
                ~f:(fst >> String.equal "quantified-closed")
            in
            let own_memberships, generated' =
              if config.houdini.quotas.membership > 0 then
                List.partition_tf generated'
                  ~f:(fst >> String.equal "membership")
              else ([], generated')
            in
            (* the inclusion and the affine element families go to their
               own quotas when they have one *)
            let inclusions, others =
              if config.houdini.quotas.inclusion > 0 then
                List.partition_tf generated' ~f:(fst >> String.equal "inclusion")
              else ([], generated')
            in
            let affine, others =
              if config.houdini.quotas.affine > 0 then
                List.partition_tf others
                  ~f:(fst >> String.equal "affine_element")
              else ([], others)
            in
            let counting, others =
              if config.houdini.quotas.counting > 0 then
                List.partition_tf others ~f:(fun (name, _) ->
                    List.mem [ "length_sum"; "three_term"; "guarded_order" ]
                      name ~equal:String.equal)
              else ([], others)
            in
            HoudiniCandidates.merge ~dtenv:(Lazy.force houdini_problem_dtenv)
              ~quota:config.houdini.quotas.quantified
              ~inclusion_quota:config.houdini.quotas.inclusion
              ~inclusions:(List.concat_map inclusions ~f:snd)
              ~own_quotas:
                [
                  ( List.concat_map exists_mems ~f:snd,
                    config.houdini.candidates.exists_memberships );
                  ( List.concat_map guarded_frames ~f:snd,
                    config.houdini.candidates.guarded_frame_equations );
                  ( List.concat_map empty_guarded ~f:snd,
                    config.houdini.candidates.empty_guarded_frames );
                  ( List.concat_map prefix_elems ~f:snd,
                    config.houdini.candidates.prefix_elements );
                  ( List.concat_map last_elems ~f:snd,
                    config.houdini.candidates.last_element_equations );
                  ( List.concat_map own_memberships ~f:snd,
                    config.houdini.quotas.membership );
                  ( List.concat_map shifted_elems ~f:snd,
                    config.houdini.candidates.shifted_elements );
                  ( List.concat_map guarded_incls ~f:snd,
                    config.houdini.candidates.guarded_inclusions );
                  ( List.concat_map constructor_cases ~f:snd,
                    Int.max_value );
                  (* last of the switched families, so that every atom the
                     families before them keep is kept with them off *)
                  ( List.concat_map affix_elems ~f:snd,
                    config.houdini.candidates.affix_elements );
                  ( List.concat_map concat_eqs ~f:snd,
                    config.houdini.candidates.concat_equations );
                  (* every one of them, last: they are the atoms the
                     quantified family's limit and quota would have kept or
                     cut in their place, so the list holds every atom it
                     held without the switch.  That needs the families on
                     own quotas before this one to build no closed atom
                     (their deduplication no longer sees the closed ones):
                     each builds its atoms over the terms the unknown
                     reaches, which mention a parameter *)
                  ( List.concat_map closed_quantified ~f:snd,
                    Int.max_value );
                ]
              ~affine_quota:config.houdini.quotas.affine
              ~affine:(List.concat_map affine ~f:snd)
              ~counting_quota:config.houdini.quotas.counting
              ~counting:(List.concat_map counting ~f:snd)
              ~cap:config.houdini.quotas.candidates
              ~params:xs ~declared:decl
              ~generated:(List.concat_map others ~f:snd) ()
          in
          if houdini_family_log then (
            List.iter decl ~f:(fun a ->
                Hashtbl.set houdini_family_of ~key:(houdini_family_key key a)
                  ~data:"declared");
            List.iter generated ~f:(fun (name, fatoms) ->
                List.iter fatoms ~f:(fun a ->
                    ignore
                      (Hashtbl.add houdini_family_of
                         ~key:(houdini_family_key key a) ~data:name
                        : [ `Ok | `Duplicate ])));
            List.iter atoms ~f:(fun a -> houdini_family_event "offered" key a));
          (* [houdini.candidates.drop_premise_atoms]: a generated atom every clause
             applying the unknown already has as a premise is left out.
             Leaving one in is never wrong (dropping is only a saving), so a
             problem that is not in clausal form, whose clauses cannot be
             read, keeps every atom *)
          let atoms =
            match PCSP.Problem.clauses_of_opt APCSP.problem with
            | Some clauses when config.houdini.candidates.drop_premise_atoms ->
              let redundant =
                HoudiniCandidates.premise_redundant (Set.to_list clauses) key xs
              in
              let kept, dropped =
                List.partition_tf atoms ~f:(fun a ->
                    List.mem decl a ~equal:phys_equal || not (redundant a))
              in
              Debug.print
              @@ lazy
                   (sprintf "[houdini] %s: %d atom(s) already premises: %s"
                      (Ident.name_of_tvar key) (List.length dropped)
                      (String.concat_map_list ~sep:" | " dropped
                         ~f:Formula.str_of));
              kept
            | _ -> atoms
          in
          (* the census: for each declared atom, which classes generate it
             too (compared in normal form, an equation either way round) *)
          Debug.print
          @@ lazy
               (let keys =
                  List.map generated ~f:(fun (name, atoms) ->
                      ( name,
                        Set.Poly.of_list
                        @@ List.concat_map atoms
                             ~f:HoudiniCandidates.census_keys ))
                in
                String.concat_map_list ~sep:"\n" decl ~f:(fun d ->
                    let dk = HoudiniCandidates.census_keys d in
                    sprintf "[houdini census] %s: %s <- %s"
                      (Ident.name_of_tvar key) (Formula.str_of d)
                      (match
                         List.filter_map keys ~f:(fun (name, ks) ->
                             if List.exists dk ~f:(Set.mem ks) then Some name
                             else None)
                       with
                      | [] -> "none"
                      | ns -> String.concat ~sep:"," ns)));
          Debug.print
          @@ lazy
               (sprintf "[houdini] %s: %d declared, %d of %d generated kept"
                  (Ident.name_of_tvar key) (List.length decl)
                  (List.length atoms - List.length decl)
                  (List.sum (module Int) generated ~f:(snd >> List.length)));
          if List.is_empty atoms then None else Some (xs, atoms))

  (* how many questions the last pre-pass asked, and whether its budget ran
     out; read by the tests *)
  let houdini_last_questions = ref 0
  let houdini_last_spent = ref false

  (* whether the last fixed point ran inside a pre-pass window
     ([houdini_deadline] set), read by the tests *)
  let houdini_last_windowed = ref false

  (* how many atoms the last pre-pass dropped without asking, after a question
     about the same clause ran out of its budget in the same pass
     ([houdini.questions.skip_clause_after_timeout]); read by the tests *)
  let houdini_last_skipped = ref 0
  (* every question the pre-pass asks, newest first, as (unknown, candidate
     atom); never cleared here, read and cleared by the tests *)
  let houdini_question_log : (Ident.tvar * Formula.t) list ref = ref []

  (* how many rounds the last pre-pass ran; read by the tests *)
  let houdini_last_rounds = ref 0

  (* [f ()] with the pre-pass's deadline set to [houdini.budget_ms] from now
     and restored afterwards, on a raise too; an enclosing call's deadline is
     kept, so the fixed point run by [houdini_outcome] shares its budget *)
  let with_houdini_deadline ?(budget_ms = config.houdini.budget_ms) f =
    match (budget_ms, !houdini_deadline) with
    | None, _ | Some _, Some _ -> f ()
    | Some ms, None ->
        houdini_deadline :=
          Some (Time_ns.add (Common.Clock.now_ns ()) (Time_ns.Span.of_int_ms ms));
        Exn.protect ~f ~finally:(fun () -> houdini_deadline := None)

  (* [budget_ms] is the caller's budget, passed on rather than re-read from
     [houdini.budget_ms]: [with_houdini_deadline] sets no deadline for
     [None], so a fixed point reached through an unbounded caller (the raced
     copy under [houdini.schedule.budget]) must not fall back to the
     sequential default here -- doing so cut that copy at 30 s while it
     reported itself unbounded. *)
  let houdini_fixed_point ?(budget_ms = config.houdini.budget_ms) fenv clauses
      : CandSol.t option =
    with_houdini_deadline ~budget_ms @@ fun () ->
    let saved_in_fixed_point = !in_houdini_fixed_point in
    in_houdini_fixed_point := true;
    (fun f ->
      Exn.protect ~f ~finally:(fun () ->
          in_houdini_fixed_point := saved_in_fixed_point))
    @@ fun () ->
    let started = Common.Clock.now_ns () in
    let spent = ref false in
    let out_of_budget () =
      if houdini_budget_spent () then spent := true;
      !spent
    in
    houdini_last_questions := 0;
    houdini_last_spent := false;
    houdini_last_windowed := Option.is_some !houdini_deadline;
    houdini_last_skipped := 0;
    let problem = APCSP.problem in
    let senv = PCSP.Problem.senv_of problem in
    let params = PCSP.Problem.params_of problem in
    let kind_map = PCSP.Problem.kind_map_of problem in
    let ordinary =
      Map.Poly.for_alli senv ~f:(fun ~key ~data:_ ->
          match Map.Poly.find kind_map key with
          | Some Kind.Ord | None -> true
          | Some _ -> false)
    in
    let declared =
      if ordinary then
        Common.PhaseTime.with_phase "gen" (fun () ->
            houdini_candidates ~stop:out_of_budget senv params)
      else Map.Poly.empty
    in
    if out_of_budget () then (
      houdini_last_spent := true;
      Debug.print @@ lazy "[houdini] budget spent before the first question";
      None)
    else if (not ordinary) || Map.Poly.for_all declared ~f:(snd >> List.is_empty)
    then None
    else
      let lam p atoms =
        let xs, _ = Map.Poly.find_exn declared p in
        Logic.Term.mk_lambda (Logic.of_old_sort_env_list xs)
        @@ Logic.ExtTerm.of_old_formula (Formula.and_of atoms)
      in
      let cand_map cur : Logic.cand_map =
        Map.Poly.mapi senv ~f:(fun ~key ~data ->
            match Map.Poly.find cur key with
            | Some atoms -> (data, lam key atoms)
            | None ->
                let xs =
                  List.mapi (Logic.Sort.args_of data) ~f:(fun i s ->
                      (Ident.Tvar (sprintf "x%d" (i + 1)), s))
                in
                (data, Logic.Term.mk_lambda xs (Logic.BoolTerm.mk_bool true)))
      in
      (* whether the last question [valid] asked ran out of its budget, for
         [houdini.questions.skip_clause_after_timeout] *)
      let last_timed_out = ref false in
      (* the countermodel of the last refuted question, for
         [houdini.questions.drop_by_model] *)
      let last_model = ref None in
      (* [houdini.questions.memo.before_simplify]: the decided answers of this fixed
         point by a digest of the printed unsimplified question together with
         the sorts of its free term variables (see [valid_old]'s key).  It lives
         as long as the fixed point, which for Houdini's raced copy is the whole
         run, so it holds a key of about 20 bytes per decided question rather than the
         text itself: on one input the printed keys averaged about 470 KB and
         the memo held about 1 GiB at 2,241 entries *)
      let raw_memo = Hashtbl.create (module String) in
      (* [houdini.questions.simplify_shared_once]: the simplified disjuncts of the
         current clause's shared leaves, by physical identity of the leaf *)
      let leaf_lookup = ref (fun (_ : Formula.t) -> None) in
      (* the simplifier's memo of the current (clause, head atom) pair, whose
         questions share their parts physically
         ([Evaluator.simplify_in_memo]): made afresh for every pair, so it
         spans no change of the environments or the simplifier's switches,
         and dropped with the fixed point *)
      let simplify_memo = ref None in
      let skipped = ref 0 in
      (* [houdini.questions.atom_countermodel_drops]: the judge of the atoms still to be
         asked, set by the per-atom loop for the next question only *)
      let atom_judge_next : (model -> int list) option ref = ref None in
      (* [houdini.questions.shared_body_session]: one solver of a context of this fixed
         point's own, holding the body of one clause at a time; [base_owner]
         names the clause and atom position whose body it holds *)
      let body_session =
        lazy (Z3Smt.Z3interface.base_session_create ~id ())
      in
      let base_owner = ref (-1) and base_owners = ref 0 in
      houdini_skip_weakened_once := false;
      (* [raw_memo]'s key must determine the question, since a [`Valid] it
         returns is trusted as a proof: the final check asks only the goal
         clauses ([houdini.final_check.goals_only]) on the ground that every
         head question of the last pass was proved.  [Formula.str_of] prints a
         free variable without its sort and [=]/[!=] alike at every sort
         (three pairwise distinct variables are unsatisfiable over 1-bit
         vectors and satisfiable over the integers), so the printed question
         is a sound key only while no two questions of one fixed point share a
         free variable name at two sorts.  That is assumed of the clause set,
         not checked here: a question's free variables are its clause's, and
         the clauses reaching this pre-pass carry their own variable names. *)
      let valid_old phi =
        (* The memo key determines the question up to meaning: two questions
           with one key are the same formula over the same sorts. This is
           required because a memoised "valid" is trusted as a proof, and the
           final check re-asks only the clauses with no unknown in the head.
           [Formula.str_of] alone does not determine it: it prints a free
           variable without its sort and [=]/[!=] alike at every sort, so
           [a = b \/ a = c \/ b = c] is one text whether it is valid (1-bit
           vectors) or not (integers). Bound variables are printed with their
           sorts in their binders, so the free term variables' sort
           environment is appended, in element order ([Set.to_list] does not
           depend on the tree's shape).

           The table keeps not that text but its 128-bit BLAKE2b digest
           followed by the text's length in bytes, and the text is dropped once
           digested.  So two questions share a key when their texts are equal,
           as before, or when two different texts collide in the digest and
           have the same length; a collision would return one question's answer
           for the other, and a [`Valid] so returned would be trusted as a
           proof.  That collisions do not occur is an ASSUMPTION, not a proof:
           for n distinct texts of one length the chance of any collision is
           about n^2 / 2^129 for a digest that behaves as a random function,
           below 2^-80 for n up to 2^24 (the memo held 2,241 entries in the
           largest run measured).  BLAKE2b is used rather than MD5 because no
           practical collision is known for it, so the assumption does not
           rest on the questions being non-adversarial; the length is a free
           second check that confines a collision to texts of equal length.
           Keeping the whole text would make the key exact, at the cost of
           the text's size for every decided question for the copy's whole
           life.  The text is built only for this key; it is not replaced by a
           digest of the formula's structure because structural equality is
           finer than equality of the printed text (it sees the [info]
           annotations the printer omits), so it would lose some of the hits
           the text gives. *)
        let raw_key =
          if config.houdini.questions.memo.before_simplify then
            Some
              (Common.PhaseTime.with_phase "raw-key" (fun () ->
                   let text =
                     Formula.str_of phi ^ " :: "
                     ^ str_of_sort_env_list Term.str_of_sort
                         (Set.to_list (Formula.term_sort_env_of phi))
                   in
                   Stdlib.Digest.BLAKE128.string text
                   ^ Int.to_string (String.length text)))
          else None
        in
        match Option.bind raw_key ~f:(Hashtbl.find raw_memo) with
        | Some (`Valid) ->
            last_model := None;
            last_timed_out := false;
            Debug.print @@ lazy "[houdini] question answered as before";
            true
        | Some (`Refuted m) ->
            last_model := m;
            last_timed_out := false;
            Debug.print @@ lazy "[houdini] question answered as before";
            false
        | None ->
        let phi =
          Common.PhaseTime.with_phase "simplify" (fun () ->
              if config.houdini.questions.simplify_shared_once then
                Evaluator.simplify_with_leaf_cache ~lookup:!leaf_lookup phi
              else
                match !simplify_memo with
                | Some memo -> Evaluator.simplify_in_memo memo phi
                | None -> Evaluator.simplify phi)
        in
        (* With COAR_DUMP_HOUDINI_QUESTIONS=<file> set, every question is
           appended to <file>, one per line, as it is asked, after the
           seconds since the epoch and a tab: an instrument for comparing the
           questions of two runs and the time taken to reach each *)
        (match Sys.getenv "COAR_DUMP_HOUDINI_QUESTIONS" with
        | None | Some "" -> ()
        | Some file ->
            Out_channel.with_file file ~append:true ~f:(fun oc ->
                Out_channel.output_string oc
                  (sprintf "%.3f\t%s\n"
                     (Time_float.to_span_since_epoch (Time_float.now ())
                     |> Time_float.Span.to_sec)
                     (Formula.str_of phi))));
        if Option.is_some SeqInstantiation.instr_file then (
          SeqInstantiation.instr_tag :=
            sprintf "p%d\tc%d\tq-" !houdini_instr_pass !houdini_instr_clause;
          SeqInstantiation.instr_line
            (sprintf "asked\tseq_exists=%b\tsize=%d"
               (binds_sequence_existentially phi) (Formula.ast_size phi)));
        (* each question gets at most what is left of the budget *)
        let timeout = cap_timeout (timeout_for phi) in
        last_model := None;
        houdini_judged_drops := None;
        houdini_pending_judge :=
          Option.map !atom_judge_next ~f:(fun judge -> (phi, judge));
        let res =
          match
            Exn.protect
              ~f:(fun () ->
                Common.PhaseTime.with_phase "check" (fun () ->
                    check_clause_nonparam ~timeout
                      ~verdict_only:config.houdini.questions.fixed_point_verdict_only fenv
                      phi))
              ~finally:(fun () -> houdini_pending_judge := None)
          with
          | `Unsat -> `Valid
          | `Sat model ->
              last_model := Some model;
              `Refuted
          | `Timeout -> `Undecided "timeout"
          | `Unknown r -> `Undecided r
          | exception exn_ when not (Common.Timer.is_async exn_) ->
              `Undecided (Exn.to_string exn_)
        in
        (match res with
        | `Valid -> ()
        | `Refuted -> Debug.print @@ lazy "[houdini] refuted"
        | `Undecided r -> Debug.print @@ lazy ("[houdini] undecided: " ^ r));
        last_timed_out := Stdlib.(res = `Undecided "timeout");
        Option.iter raw_key ~f:(fun key ->
            match res with
            | `Valid -> Hashtbl.set raw_memo ~key ~data:`Valid
            | `Refuted -> Hashtbl.set raw_memo ~key ~data:(`Refuted !last_model)
            | `Undecided _ -> ());
        Stdlib.(res = `Valid)
      in
      let valid uni_senv term =
        valid_old
        @@ Common.PhaseTime.with_phase "build" (fun () ->
               Logic.ExtTerm.to_old_fml Map.Poly.empty uni_senv term)
      in
      let questions = ref 0 in
      (* the clauses with the fewest unknowns in the body first: a fact
         clause refutes most generated atoms, and an atom it drops is not
         asked again in the same pass.  The order changes which questions are
         asked, not the fixed point, which is the largest inductive subset
         whatever the order when every question is decided *)
      let clauses =
        List.stable_sort (Set.to_list clauses)
          ~compare:(fun ((_, _, ns1, _) : Clause.t) (_, _, ns2, _) ->
            Int.compare (Set.length ns1) (Set.length ns2))
      in
      let fam_pass = ref 0 and fam_clause = ref 0 in
      let rec fix cur =
        Int.incr fam_pass;
        fam_clause := 0;
        houdini_instr_pass := !fam_pass;
        let sub =
          Common.PhaseTime.with_phase "pass-setup" (fun () ->
              CandSol.to_subst (CandSol.make (cand_map cur)))
        in
        let subst_linear =
          let f = lazy (Logic.Term.subst_rename_on_capture sub) in
          fun t -> (Lazy.force f) t
        in
        let cur' =
          List.fold clauses ~init:cur
            ~f:(fun cur ((uni_senv, ps, ns, phi) : Clause.t) ->
              (* set once a question about this clause ran out of its budget in
                 this pass ([houdini.questions.skip_clause_after_timeout]) *)
              let stalled = ref false in
              Int.incr fam_clause;
              houdini_instr_clause := !fam_clause;
              Set.fold ps ~init:cur ~f:(fun cur papp ->
                  let p = Logic.Term.pvar_of_atom papp in
                  match Map.Poly.find cur p with
                  | None | Some [] -> cur
                  | Some atoms ->
                      let rest =
                        Set.to_list (Set.remove ps papp)
                        @ List.map (Set.to_list ns) ~f:Logic.BoolTerm.neg_of
                      in
                      (* [phi] and [rest] are the same for every atom asked
                         here, and [sub] is fixed for the pass, so with
                         [houdini.questions.linear_subst] they are substituted once;
                         [Logic.BoolTerm.or_of_parts] then gives each
                         question the disjunction [or_of] would have built,
                         since the substitution sends a constant to itself
                         and distributes over [Or] *)
                      let shared =
                        lazy
                          (List.map (phi :: rest) ~f:(fun t ->
                               (t, subst_linear t)))
                      in
                      simplify_memo := Some (Evaluator.simplify_memo_create ());
                      (* the shared parts converted once, for
                         [houdini.questions.shared_conversion] *)
                      let shared_old =
                        lazy
                          (List.map (Lazy.force shared) ~f:(fun (t, t') ->
                               ( t,
                                 Logic.ExtTerm.to_old_fml Map.Poly.empty
                                   uni_senv t' )))
                      in
                      if config.houdini.questions.simplify_shared_once then (
                        let leaves =
                          lazy
                            (List.concat_map (Lazy.force shared_old)
                               ~f:(fun (_, part) ->
                                 List.map (Evaluator.disj_leaves [] part)
                                   ~f:(fun leaf ->
                                     ( leaf,
                                       lazy
                                         (Formula.disjuncts_of
                                            (Evaluator.simplify leaf)) ))))
                        in
                        leaf_lookup :=
                          fun leaf ->
                            if not (Lazy.is_val shared_old) then None
                            else
                              List.find_map (Lazy.force leaves)
                                ~f:(fun (l, d) ->
                                  if phys_equal l leaf then Some (Lazy.force d)
                                  else None));
                      let to_old = Logic.ExtTerm.to_old_fml Map.Poly.empty uni_senv in
                      (* [to_old (subst_linear head)], which a question
                         needs twice -- for the shared-body solver and for
                         the question asked after it -- computed once for the
                         last head met (by physical identity) when computing
                         it drew no fresh name, and otherwise computed again
                         as before: a conversion and a substitution that draw
                         no name are functions of their input and of the
                         environments, which asking a question does not
                         change, so the reused value is the one recomputing
                         gives and every later draw is unchanged *)
                      let head_old =
                        let last = ref None in
                        fun head ->
                          match !last with
                          | Some (h, r) when phys_equal h head -> r
                          | _ ->
                              let stamp = Ident.fresh_stamp () in
                              let r = to_old (subst_linear head) in
                              last :=
                                if Ident.fresh_stamp () = stamp then
                                  Some (head, r)
                                else None;
                              r
                      in
                      if Option.is_some SeqInstantiation.instr_file then
                        houdini_instr_premise :=
                          Some
                            (lazy
                              (to_old
                                 (subst_linear
                                    (Logic.BoolTerm.or_of (phi :: rest)))));
                      (* [houdini.questions.shared_body_session]: [head]'s question
                         decided against the body held in the fixed point's
                         solver, whose body of this clause and atom position
                         is set there at the first head asked: [`Proved] when
                         the body's other conjuncts and the head's negation
                         are unsatisfiable; [`Refuted] with a model of them
                         that every conjunct set aside holds under
                         ([WeakenedQuery.model_extends]), which is then a
                         countermodel of the whole question; [`Ask]
                         otherwise, when the question is asked as before --
                         and, when the solver found such a model that does
                         not extend, without the weakened question in front
                         of the forked one, which would ask the same thing
                         again *)
                      let owner = (Int.incr base_owners; !base_owners) in
                      let base = ref [] and refused = ref [] in
                      let shared_body_decides head =
                        if
                          (not config.houdini.questions.shared_body_session)
                          || out_of_budget ()
                        then `Ask
                        else
                        Common.PhaseTime.with_phase "shared-body" @@ fun () ->
                        let neg_head =
                          negation_asked (head_old head)
                        in
                        if Z3Smt.Z3interface.may_not_return neg_head then `Ask
                        else
                          let session = Lazy.force body_session in
                          if !base_owner <> owner then (
                            base_owner := owner;
                            Common.PhaseTime.with_phase "set" (fun () ->
                                let body =
                                  Formula.or_of
                                    (List.map (Lazy.force shared_old) ~f:snd)
                                in
                                let r, rest =
                                  List.partition_tf
                                    (Formula.conjuncts_list_of
                                       (negation_asked body))
                                    ~f:Z3Smt.Z3interface.may_not_return
                                in
                                refused := r;
                                base :=
                                  if
                                    (not (List.is_empty rest))
                                    && Z3Smt.Z3interface.base_session_set ~id
                                         session fenv rest
                                  then rest
                                  else []));
                          if List.is_empty !base then `Ask
                          else
                            let timeout =
                              cap_timeout
                                (timeout_for
                                   (Formula.and_of (neg_head :: !base)))
                            in
                            match
                              Common.PhaseTime.with_phase "ask" (fun () ->
                                  Z3Smt.Z3interface.base_session_check ~id
                                    session ~timeout fenv neg_head)
                            with
                            | `Unsat ->
                                Int.incr houdini_shared_body_proofs;
                                Common.PhaseTime.event_here "shared-body-proof";
                                last_model := None;
                                last_timed_out := false;
                                houdini_judged_drops := None;
                                `Proved
                            | `Sat model
                              when Common.PhaseTime.with_phase "extend"
                                     (fun () ->
                                       PCSatCommon.WeakenedQuery.model_extends
                                         ~id
                                         ~ms:(cap_ms
                                                (Option.value timeout
                                                   ~default:10000))
                                         fenv !refused model) ->
                                Int.incr houdini_shared_body_refutations;
                                Common.PhaseTime.event_here
                                  "shared-body-refutation";
                                last_model := Some model;
                                last_timed_out := false;
                                houdini_judged_drops :=
                                  Option.map !atom_judge_next ~f:(fun judge ->
                                      judge model);
                                `Refuted
                            | `Sat _ ->
                                houdini_skip_weakened_once := true;
                                `Ask
                            | `Unknown -> `Ask
                      in
                      let rec ask head =
                        match shared_body_decides head with
                        | `Proved -> true
                        | `Refuted -> false
                        | `Ask ->
                        Exn.protect
                          ~finally:(fun () ->
                            houdini_skip_weakened_once := false)
                          ~f:(fun () ->
                        if
                          config.houdini.questions.linear_subst
                          && config.houdini.questions.shared_conversion
                        then
                          match
                            Common.PhaseTime.with_phase "build" (fun () ->
                                Lazy.force shared_old)
                          with
                          | phi_part :: rest_parts ->
                              valid_old
                              @@ Common.PhaseTime.with_phase "build"
                              @@ fun () ->
                              Logic.BoolTerm.fold_or_of_parts
                                   ~bool:(fun b ->
                                     to_old (Logic.BoolTerm.mk_bool b))
                                   ~or_:(Formula.mk_binop Formula.Or)
                                   (phi_part
                                   :: (head, head_old head)
                                   :: rest_parts)
                          | [] -> assert false
                        else
                          valid uni_senv
                            (Common.PhaseTime.with_phase "build" (fun () ->
                                 question head)))
                      and question head =
                        if config.houdini.questions.linear_subst then
                          match Lazy.force shared with
                          | phi_part :: rest_parts ->
                              Logic.BoolTerm.or_of_parts
                                (phi_part :: (head, subst_linear head)
                               :: rest_parts)
                          | [] -> assert false
                        else
                          Logic.Term.subst sub
                          @@ Logic.BoolTerm.or_of (phi :: head :: rest)
                      in
                      (* [houdini.questions.drop_by_model]: the held atoms asked as one
                         conjunction ([HoudiniByModel.run]) *)
                      let fam_rank = ref 0 in
                      let fam ?rank event a =
                        houdini_family_event ~pass:!fam_pass ~clause:!fam_clause
                          ?rank event p a
                      in
                      let by_model atoms =
                        let instance a =
                          to_old
                          @@ Logic.Term.subst
                               (Map.Poly.singleton p (lam p [ a ]))
                               papp
                        in
                        let held, aside =
                          if (HoudiniConfig.Switch.drop_by_model_quantified_aside config.houdini) then
                            List.partition_tf atoms ~f:Formula.is_quantifier_free
                          else (atoms, [])
                        in
                        (* [houdini.questions.drop_by_model.batch_ms]: the verdicts
                           one forked copy gave, for the current countermodel,
                           on the atoms the substitution left undecided *)
                        let batch = ref [] in
                        let prejudge model atoms =
                          batch := [];
                          match (HoudiniConfig.Switch.drop_by_model_batch_ms config.houdini) with
                          | Some ms when not (out_of_budget ()) ->
                              Common.PhaseTime.with_phase "model-batch"
                                (fun () ->
                                  let open_ =
                                    List.filter atoms ~f:(fun a ->
                                        Stdlib.(
                                          HoudiniByModel.judge model (instance a)
                                          = `Undecided))
                                  in
                                  if not (List.is_empty open_) then
                                    let ms = cap_ms ms in
                                    let per = Int.min ms 500 in
                                    match
                                      PCSatCommon.ForkedQuery.run ~ms (fun () ->
                                          List.map open_ ~f:(fun a ->
                                              HoudiniByModel.judge_by_solver
                                                ~sat:(fun phi ->
                                                  match
                                                    Z3Smt.Z3interface.check_sat
                                                      ~id ~timeout:(Some per)
                                                      fenv [ phi ]
                                                  with
                                                  | `Unsat -> `Unsat
                                                  | `Sat _ -> `Sat
                                                  | _ -> `Unknown)
                                                model (instance a)))
                                    with
                                    | Some vs -> batch := List.zip_exn open_ vs
                                    | None -> ())
                          | _ -> ()
                        in
                        HoudiniByModel.run ~aside ~prejudge
                          ~stop:(fun () -> out_of_budget () || !stalled)
                          ~judge:(fun model a ->
                            (fun v ->
                              if Stdlib.(v = `False) then
                                fam ~rank:!fam_rank "model-drop" a;
                              v)
                            @@ Common.PhaseTime.with_phase "model-drop" (fun () ->
                                match (HoudiniConfig.Switch.drop_by_model_solver_ms config.houdini) with
                                | None -> (
                                    match HoudiniByModel.judge model (instance a) with
                                    | `Undecided -> (
                                        match
                                          List.find !batch ~f:(fun (b, _) ->
                                              phys_equal a b)
                                        with
                                        | Some (_, v) -> v
                                        | None -> `Undecided)
                                    | v -> v)
                                | Some ms ->
                                    HoudiniByModel.judge_by_solver
                                      ~sat:(fun phi ->
                                        if out_of_budget () then `Unknown
                                        else
                                          let ms = cap_ms ms in
                                          match
                                            PCSatCommon.ForkedQuery.run ~ms
                                              (fun () ->
                                                match
                                                  Z3Smt.Z3interface.check_sat
                                                    ~id ~timeout:(Some ms) fenv
                                                    [ phi ]
                                                with
                                                | `Unsat -> `Unsat
                                                | `Sat _ -> `Sat
                                                | _ -> `Unknown)
                                          with
                                          | Some r -> r
                                          | None -> `Unknown)
                                      model (instance a)))
                          ~ask:(fun held ->
                            Int.incr questions;
                            Debug.print
                            @@ lazy
                                 (sprintf "[houdini] %s: conjunction of %d atoms"
                                    (Ident.name_of_tvar p) (List.length held));
                            let head =
                              Common.PhaseTime.with_phase "head" (fun () ->
                                  Logic.Term.subst
                                    (Map.Poly.singleton p (lam p held))
                                    papp)
                            in
                            let proved =
                              in_houdini_conjunction_question := true;
                              Exn.protect
                                ~f:(fun () -> ask head)
                                ~finally:(fun () ->
                                  in_houdini_conjunction_question := false)
                            in
                            if
                              config.houdini.questions.skip_clause_after_timeout
                              && !last_timed_out
                            then stalled := true;
                            if proved then `Proved
                            else
                              match !last_model with
                              | Some model ->
                                  Int.incr fam_rank;
                                  `Refuted model
                              | None -> `Undecided)
                          held
                      in
                      let proved, refuted =
                        if (HoudiniConfig.Switch.drop_by_model config.houdini) then by_model atoms
                        else ([], [])
                      in
                      (* [houdini.questions.atom_countermodel_drops]: the positions of
                         [atoms] a countermodel of an earlier atom's question
                         in this pass made false, and each atom's ground
                         instance, built once per clause and pass *)
                      let model_dropped = Hash_set.create (module Int) in
                      let instances =
                        lazy
                          (Array.of_list
                             (List.map atoms ~f:(fun a ->
                                  to_old
                                  @@ Logic.Term.subst
                                       (Map.Poly.singleton p (lam p [ a ]))
                                       papp)))
                      in
                      let judge_after i model =
                        let insts = Lazy.force instances in
                        List.filter
                          (List.range (i + 1) (Array.length insts))
                          ~f:(fun j ->
                            (not (Hash_set.mem model_dropped j))
                            && Stdlib.(
                                 HoudiniByModel.judge model insts.(j) = `False))
                      in
                      let kept =
                        List.filteri atoms ~f:(fun i a ->
                            List.mem proved a ~equal:phys_equal
                            || (not (List.mem refuted a ~equal:phys_equal))
                               && (not
                                     (Hash_set.mem model_dropped i
                                     && (fam "atom-model-drop" a;
                                         Int.incr houdini_atom_model_drops;
                                         Common.PhaseTime.event_here
                                           "atom-model-drop";
                                         true)))
                               &&
                            (* a spent budget answers every question left as
                               undecided without asking it, which drops the
                               atom as a question the solver left undecided
                               would; so does a stalled clause
                               ([houdini.questions.skip_clause_after_timeout]), and each
                               atom dropped that way, with budget left, is
                               counted in [skipped].  The count is taken in
                               the conjunct that decides the drop, since any
                               earlier conjunct testing [!stalled] would
                               short-circuit it and leave [skipped] at 0. *)
                            (let go =
                               (not (out_of_budget ()))
                               && not
                                    (!stalled
                                    && (Int.incr skipped;
                                        true))
                             in
                             if not go then fam "unasked" a;
                             go)
                            &&
                            (Int.incr questions;
                            houdini_question_log :=
                              (p, a) :: !houdini_question_log;
                            Debug.print
                            @@ lazy
                                 (sprintf "[houdini] %s: %s"
                                    (Ident.name_of_tvar p) (Formula.str_of a));
                            let head =
                              Common.PhaseTime.with_phase "head" (fun () ->
                                  Logic.Term.subst
                                    (Map.Poly.singleton p (lam p [ a ]))
                                    papp)
                            in
                            if config.houdini.questions.atom_countermodel_drops then (
                              ignore (Lazy.force instances : Formula.t array);
                              atom_judge_next := Some (judge_after i));
                            let r =
                              in_houdini_atom_question := true;
                              Exn.protect
                                ~f:(fun () -> ask head)
                                ~finally:(fun () ->
                                  in_houdini_atom_question := false;
                                  atom_judge_next := None)
                            in
                            (* only a refutation's countermodel is read *)
                            (if
                               config.houdini.questions.atom_countermodel_drops
                               && (not r) && Option.is_some !last_model
                             then
                               match !houdini_judged_drops with
                               | Some drops ->
                                   List.iter drops ~f:(Hash_set.add model_dropped);
                                   if not (List.is_empty drops) then
                                     Debug.print
                                     @@ lazy
                                          (sprintf
                                             "[houdini] the countermodel also \
                                              refutes %d atom(s) still to be \
                                              asked"
                                             (List.length drops))
                               | None -> ());
                            houdini_judged_drops := None;
                            if not r then
                              fam
                                (if Option.is_none !last_model then "atom-undecided"
                                 else "atom-refuted")
                                a;
                            if
                              config.houdini.questions.skip_clause_after_timeout
                              && !last_timed_out
                            then stalled := true;
                            r))
                      in
                      Map.Poly.set cur ~key:p ~data:kept))
        in
        if
          Map.Poly.equal (fun a b -> List.length a = List.length b) cur cur'
        then cur
        else fix cur'
      in
      let cur =
        Common.PhaseTime.with_phase "fix" (fun () ->
            fix (Map.Poly.map declared ~f:snd))
      in
      Map.Poly.iteri cur ~f:(fun ~key ~data ->
          List.iter data ~f:(fun a -> houdini_family_event "kept" key a));
      houdini_last_questions := !questions;
      houdini_last_spent := !spent;
      houdini_last_skipped := !skipped;
      if !skipped > 0 then
        Debug.print
        @@ lazy
             (sprintf
                "[houdini] %d atom(s) dropped unasked after a clause's question \
                 ran out of its budget"
                !skipped);
      Debug.print
      @@ lazy
           (String.concat_map_list ~sep:"\n" (Map.Poly.to_alist cur)
              ~f:(fun (p, atoms) ->
                String.concat_map_list ~sep:"\n" atoms ~f:(fun a ->
                    sprintf "[houdini census-kept] %s: %s"
                      (Ident.name_of_tvar p) (Formula.str_of a))));
      Debug.print
      @@ lazy
           (sprintf "[houdini] %d questions in %.1f s; kept %s" !questions
              (Time_ns.Span.to_sec (Time_ns.diff (Common.Clock.now_ns ()) started))
              (String.concat_map_list ~sep:"; " (Map.Poly.to_alist cur)
                 ~f:(fun (p, atoms) ->
                   sprintf "%s: %s" (Ident.name_of_tvar p)
                     (Formula.str_of (Formula.and_of atoms)))));
      if !spent then (
        (* every atom the spent budget left unconfirmed was dropped, so there
           is nothing left to try *)
        Debug.print
        @@ lazy
             (sprintf "[houdini] budget spent after %d questions" !questions);
        None)
      else Some (CandSol.make (cand_map cur))

  (* One round of the pre-pass, and its outcome: [`Solution] when its fixed
     point passes the ordinary check against every clause,
     [`Counterexamples cexs] with exactly that check's counterexamples
     otherwise (never empty), and
     [`Not_applicable] when there is nothing to try (no declared atom, or an
     unknown of another kind than the ordinary one, or a budget that ran
     out).  [record] is given each counterexample's derivation, as an
     ordinary validation counterexample's is, only when the outcome is
     [`Counterexamples].

     With a budget ([budget_ms], which [houdini_outcome] passes as
     [houdini.budget_ms] or, for a second round, the round's own), one
     wall-clock budget covers the whole of this
     function: candidate generation, the fixed point and the final check.  Each
     solver question gets at most what is left of it, a clause the final check
     has not reached when it runs out is not asked, and a question it cut short
     comes back undecided.  When it has run out by the end of the check (to
     within 100 ms), the outcome is [`Not_applicable] -- nothing is
     reported and nothing is learnt, and the loop goes on as it would have
     without the pre-pass; a fixed point every clause was shown to hold for is
     still reported as a solution.  Only the parts outside a solver call
     (building, normalising, substituting and simplifying formulas, and one
     call into the qualifier generator) are not cut short, so the budget can be
     overrun by the longest of those.

     With [houdini.budget_ms], the pre-pass ([houdini_outcome]) is also not
     run at all inside a nested solve bounded by a deadline (the finite instantiation of a
     quantified sort): such a solve reports only a refutation, which the
     pre-pass cannot produce -- its solution would be discarded and its
     counterexamples are what the solve's first validation finds anyway --
     while its questions spend the deadline.  An input the loop refutes in
     2 s inside such a solve lost that answer to a pre-pass that used the
     whole of the solve's 10 s. *)
  (* With [houdini.final_check.retry_ms = Some ms], the final check's
     [retry_undecided]: a clause whose question timed out is asked once more,
     its [negation_asked] in a forked copy killed after [ms] with no solver
     timer, and [`Unsat] (the clause holds) is returned only when the copy
     answered so; every other answer, the copy's refutation included (its
     model does not survive the trip back), returns [res] unchanged.  Counted
     in [houdini_final_retries] (asked, proved), read by the tests. *)
  let houdini_final_retries = (ref 0, ref 0)

  (* With [houdini.final_check.by_pieces], an undecided clause [phi] of the
     final check asked by its pieces: [`Unsat] (the clause holds) when it has
     more than one piece and each piece's question is [`Unsat]; [res]
     unchanged otherwise, at the first piece that is not proved or once the
     pre-pass's budget is spent.  Counted in [houdini_final_pieces] (clauses
     split, clauses proved by their pieces), read by the tests. *)
  let houdini_final_pieces = (ref 0, ref 0)

  (* With [COAR_DUMP_HOUDINI_PIECES=dir] in the environment, each piece the
     final check asks is kept as [dir/qN-PID_native.smt2] (its validity
     question as SMT-LIB, written before it is asked, so that a piece cut
     short by the process's end can still be replayed in a process of its
     own; with [COAR_DUMP_VARIANTS] also its exact rewrites) and
     [dir/qN-PID_k.smt2] (the solver checks it makes), and one line per
     piece answered is appended to [dir/index.tsv].  A diagnostic; nothing is
     written and the answer is unchanged without the variable. *)
  let houdini_piece_dump_count = Atomic.make 0

  let check_piece_dumped ~timeout fenv p =
    Z3Smt.Z3interface.with_validity_dump ~native:false
      ~var:"COAR_DUMP_HOUDINI_PIECES" ~counter:houdini_piece_dump_count ~id
      ~timeout:(Option.value timeout ~default:0)
      ~outcome:(function
        | `Unsat -> "valid" | `Sat _ -> "invalid" | _ -> "undecided")
      fenv p
    @@ fun () ->
    Z3Smt.Z3interface.dump_native_question ~id fenv p;
    check_clause_nonparam ~timeout fenv p

  let houdini_final_by_pieces fenv phi res =
    match res with
    | (`Timeout | `Unknown _) when config.houdini.final_check.by_pieces -> (
        match ClausePieces.of_clause phi with
        | [] | [ _ ] -> res
        | ps ->
            incr (fst houdini_final_pieces);
            let n = List.length ps in
            let rec go k = function
              | [] ->
                  incr (snd houdini_final_pieces);
                  Debug.print
                  @@ lazy
                       (sprintf "[houdini] final check: valid by its %d pieces"
                          n);
                  `Unsat
              | p :: rest -> (
                  if houdini_budget_spent () then res
                  else
                    match check_piece_dumped ~timeout:(timeout_for p) fenv p
                    with
                    | `Unsat -> go (k + 1) rest
                    | _ ->
                        Debug.print
                        @@ lazy
                             (sprintf
                                "[houdini] final check: piece %d of %d not \
                                 proved: %s"
                                k n (Formula.str_of p));
                        res)
            in
            go 1 ps)
    | _ -> res

  let houdini_final_retry fenv phi res =
    let res = houdini_final_by_pieces fenv phi res in
    match (config.houdini.final_check.retry_ms, res) with
    | Some ms, `Timeout -> (
        incr (fst houdini_final_retries);
        let neg_phi = negation_asked phi in
        let started = Common.Clock.now_float () in
        let r =
          PCSatCommon.ForkedQuery.valid_within ~ms (fun () ->
              match
                Z3Smt.Z3interface.check_sat ~id ~timeout:None fenv [ neg_phi ]
              with
              | `Unsat -> `Valid
              | `Sat _ -> `Invalid ()
              | `Timeout -> `Timeout
              | `Unknown r -> `Unknown r)
        in
        Debug.print
        @@ lazy
             (sprintf "[houdini] final check: a timed-out clause asked again: %s in %.3f s (budget %d ms)"
                (match r with
                | `Valid -> "valid"
                | `Timeout -> "killed or timeout"
                | `Unknown r -> "undecided, " ^ r)
                (elapsed_since started) ms);
        match r with
        | `Valid ->
            incr (snd houdini_final_retries);
            `Unsat
        | _ -> res)
    | _ -> res

  let houdini_round ~record ~budget_ms fenv clauses =
    let saved = !in_houdini_seq_instantiation in
    in_houdini_seq_instantiation := config.houdini.questions.seq_instantiation;
    (fun f ->
      Exn.protect ~f ~finally:(fun () -> in_houdini_seq_instantiation := saved))
    @@ fun () ->
    with_houdini_deadline ~budget_ms @@ fun () ->
    match houdini_fixed_point ~budget_ms fenv clauses with
    | None -> `Not_applicable
    | Some cand ->
        let recorded = ref [] in
        let cexs =
          Common.PhaseTime.with_phase "final" @@ fun () ->
          houdini_in_final := true;
          Exn.protect
            ~finally:(fun () -> houdini_in_final := false)
            ~f:(fun () ->
              find_all_counterexamples
                ~record:(fun ex sub -> recorded := (ex, sub) :: !recorded)
                ~stop:houdini_budget_spent
                ~retry_undecided:(houdini_final_retry fenv)
                (if config.houdini.final_check.goals_only then
                   Set.filter clauses ~f:(fun ((_, ps, _, _) : Clause.t) ->
                       Set.is_empty ps)
                 else clauses)
                fenv cand)
        in
        let cut_short = houdini_budget_nearly_spent () in
        if Set.is_empty cexs then (
          Debug.print
          @@ lazy "[houdini] the fixed point satisfies every clause";
          `Solution cand)
        else if cut_short then (
          Debug.print
          @@ lazy
               "[houdini] budget spent in the final check of the fixed point; \
                nothing is reported";
          `Not_applicable)
        else (
          List.iter (List.rev !recorded) ~f:(fun (ex, sub) -> record ex sub);
          Debug.print
          @@ lazy
               (sprintf
                  "[houdini] the fixed point is not a solution (%d \
                   counterexamples); going on"
                  (Set.length cexs));
          `Counterexamples cexs)

  (* One round, or two under [houdini.candidates.inclusions.second_round]
     ([HoudiniCandidates.rounds] states which run): round 1 generates no
     inclusion and records no derivation, since its counterexamples are
     dropped whenever they arise (round 2 then runs); each round has its own
     budget, a fresh deadline set by [houdini_round]. *)
  (* [unbounded]: no budget, and yet a pre-pass window.  Whether a question is
     asked inside the pre-pass is read off [houdini_deadline] being set: the
     killed copy for a question that may not return, the memo of decided
     questions, the axiom-first final check's window.  With no deadline at all
     those are silently the outside-the-pre-pass forms, and on a Rust-derived
     [try_fold] the raced copy then asked every quantified question in process
     under a solver timer that does not hold over sequences (one question took
     79 s, the fixed point 165 s).  So an unbounded pre-pass runs under a
     deadline this far away instead -- about eleven days, past any run, and
     within a solver's millisecond budget -- which caps nothing and keeps the
     window. *)
  let houdini_unbounded_window_ms = 1_000_000_000

  let houdini_outcome_once ?(record = fun _ _ -> ()) ?(unbounded = false)
      ?(budget_ms = config.houdini.budget_ms) fenv clauses =
    houdini_last_rounds := 0;
    if Option.is_some budget_ms && PCSatCommon.SolveDeadline.active ()
    then (
      Debug.print
      @@ lazy "[houdini] not run inside a nested solve bounded by a deadline";
      `Not_applicable)
    else
      let budget_ms =
        match budget_ms with
        | None when unbounded -> Some houdini_unbounded_window_ms
        | b -> b
      in
      HoudiniCandidates.rounds ~second_round:houdini_two_rounds
        ~budget_ms
        ~round_budget_ms:(HoudiniConfig.Switch.inclusion_round_budget_ms config.houdini)
        ~round:(fun ~inclusions ~budget_ms ->
          Int.incr houdini_last_rounds;
          if houdini_two_rounds then
            Debug.print
            @@ lazy
                 (sprintf "[houdini] round %d (%s the inclusions)"
                    !houdini_last_rounds
                    (if inclusions then "with" else "without"));
          houdini_with_inclusions := inclusions;
          Exn.protect
            ~finally:(fun () -> houdini_with_inclusions := true)
            ~f:(fun () ->
              houdini_round
                ~record:
                  (if houdini_two_rounds && not inclusions then fun _ _ -> ()
                   else record)
                ~budget_ms fenv clauses))

  let houdini_outcome ?(record = fun _ _ -> ()) ?(unbounded = false)
      ?(budget_ms = config.houdini.budget_ms) fenv clauses =
    if config.houdini.declared_first && houdini_generates () then
      let first =
        houdini_declared_only := true;
        Exn.protect
          ~finally:(fun () -> houdini_declared_only := false)
          ~f:(fun () ->
            Common.PhaseTime.with_phase "houdini-declared-first" @@ fun () ->
            houdini_outcome_once ~unbounded ~budget_ms fenv clauses)
      in
      match first with
      | `Solution _ as sol ->
          Debug.print
          @@ lazy "[houdini] the declared atoms alone are a solution";
          sol
      | `Counterexamples _ | `Not_applicable ->
          houdini_outcome_once ~record ~unbounded ~budget_ms fenv clauses
    else houdini_outcome_once ~record ~unbounded ~budget_ms fenv clauses

  let houdini_candidate fenv clauses : CandSol.t option =
    match houdini_outcome fenv clauses with
    | `Solution cand -> Some cand
    | `Counterexamples _ | `Not_applicable -> None

  (* the recorder every validation counterexample goes through *)
  let record_in vs ex sub =
    VersionSpace.record_derivation vs ex ~rule:"instance" ~subst:(Some sub)

  (* A counterexample as it enters the example set: normalised, with its
     derivation copied onto the normal form, exactly as the counterexamples
     of a rejected sampled candidate are *)
  let normalize_counterexamples vs cexs =
    let unknowns = Map.key_set @@ PCSP.Problem.senv_of APCSP.problem in
    Set.Poly.map cexs ~f:(fun (ex, srcs) ->
        let ex' = ExClause.normalize_params unknowns @@ ExClause.normalize ex in
        VersionSpace.copy_derivation vs ~from:ex ~to_:ex';
        (ex', srcs))

  (* the pre-pass runs at most once per solve, before the first synthesis or
     inside the first validation *)
  let houdini_done = ref false

  (* Asked by the coordinator once, before the first synthesis.  [None]: the
     loop starts as it would have (the switch is off, the pre-pass has run, the
     state is not a continuing one, there is nothing to try, or the fixed point
     is not a solution and no feedback is asked for).  [Some (Sat sol)]: the
     fixed point is a solution.  [Some (Continue ...)]: the version space with
     the fixed point's counterexamples added as examples, which the phases
     following validation are to process before the first synthesis. *)
  (* What the pre-pass's outcome makes of the version space [vs] before the
     first synthesis: the answer for a solution; with
     [houdini.feedback_counterexamples], [vs] with exactly the outcome's
     counterexamples added (normalised as a validation round's are) and nothing
     else; otherwise [None], leaving [vs] untouched. *)
  let state_of_houdini_outcome vs = function
    | `Solution sol ->
        Debug.print
        @@ lazy "*** a genuine solution is found (houdini, before synthesis): ";
        Debug.print @@ lazy (CandSol.str_of sol);
        Some (State.Sat sol)
    | `Counterexamples cexs when config.houdini.feedback_counterexamples ->
        let examples = normalize_counterexamples vs cexs in
        Debug.print
        @@ lazy
             (sprintf
                "[houdini] %d counterexamples of the fixed point added before \
                 the first synthesis"
                (Set.length examples));
        Some (State.of_examples vs examples)
    | `Counterexamples _ | `Not_applicable -> None

  let run_houdini_prepass (e : State.u) : State.u option =
    if (not (HoudiniConfig.Switch.before_synthesis config.houdini)) || !houdini_done then None
    else
      match e with
      | State.Continue (vs, ()) -> (
          houdini_done := true;
          let clauses =
            Set.union (PCSP.Problem.clauses_of APCSP.problem)
            @@ Set.Poly.of_list
            @@ Hash_set.to_list vs.learned_clauses
          in
          state_of_houdini_outcome vs
          @@ houdini_outcome ~record:(record_in vs) vs.fenv clauses)
      | _ -> None

  let houdini_in_parallel =
    (HoudiniConfig.Switch.in_parallel config.houdini) && (HoudiniConfig.Switch.before_synthesis config.houdini)

  (* Run in the forked copy of [houdini.schedule = Parallel _] (the process never calls
     it; it only skips the sequential forms).  Contract: [Some (Sat sol)] for
     a fixed point the ordinary check showed every clause to hold for -- the
     outcome the sequential pre-pass reports as [Sat]; [Some st] with [st] the
     state [state_of_houdini_outcome] makes of a failed fixed point's
     counterexamples, only with [houdini.feedback_counterexamples] and only
     when the outcome came within [houdini.budget_ms] of the pre-pass's start
     (the sequential budget; always, when that is [None]); [None] otherwise.
     So every non-[None] result is a state the sequential pre-pass under
     [houdini.budget_ms] could have returned, or a solution found later, and
     the copy that goes on with it runs what the sequential mode runs.  A
     late failed fixed point gives [None]: taking over then would discard the
     loop's progress for examples the sequential mode would not have had. *)
  let houdini_parallel_prepass (e : State.u) : State.u option =
    if !houdini_done then None
    else (
      houdini_done := true;
      match e with
      | State.Continue (vs, ()) ->
          let clauses =
            Set.union (PCSP.Problem.clauses_of APCSP.problem)
            @@ Set.Poly.of_list
            @@ Hash_set.to_list vs.learned_clauses
          in
          let budget_ms =
            if (HoudiniConfig.Switch.parallel_unbounded config.houdini) then None
            else
              match (HoudiniConfig.Switch.parallel_budget_ms config.houdini) with
              | Some _ as b -> b
              | None -> config.houdini.budget_ms
          in
          let started = Common.Clock.now_ns () in
          let outcome =
            houdini_outcome ~record:(record_in vs)
              ~unbounded:(HoudiniConfig.Switch.parallel_unbounded config.houdini) ~budget_ms vs.fenv
              clauses
          in
          let in_sequential_budget =
            match config.houdini.budget_ms with
            | None -> true
            | Some ms ->
                Time_ns.Span.(
                  Time_ns.diff (Common.Clock.now_ns ()) started <= of_int_ms ms)
          in
          (match outcome with
          | `Counterexamples _ when not in_sequential_budget ->
              Debug.print
              @@ lazy
                   "[houdini] in parallel: the fixed point is not a solution \
                    and came after the sequential budget; nothing fed back"
          | _ -> ());
          (match outcome with
          | `Solution sol ->
              Debug.print
              @@ lazy "*** a genuine solution is found (houdini, in parallel): ";
              Debug.print @@ lazy (CandSol.str_of sol)
          | _ -> ());
          if in_sequential_budget then state_of_houdini_outcome vs outcome
          else (
            match outcome with
            | `Solution sol -> Some (State.Sat sol)
            | `Counterexamples _ | `Not_applicable -> None)
      | _ -> None)

  (* The eager form: before the first round, unless the pre-pass is lazy. *)
  let houdini_before_synthesis (e : State.u) : State.u option =
    if houdini_in_parallel then None
    else
    match HoudiniConfig.Switch.after_ms config.houdini with
    | Some _ -> None
    | None -> run_houdini_prepass e

  (* The lazy form: at a later round boundary, once [t] milliseconds have passed.
     [run_houdini_prepass] sets [houdini_done], so it runs at most once, and
     not at all once the pre-pass inside the first validation has run. *)
  let houdini_at_round_boundary ~elapsed_s (e : State.u) : State.u option =
    match HoudiniConfig.Switch.after_ms config.houdini with
    | Some _ when houdini_in_parallel -> None
    (* [t] is in milliseconds; [of_int t / 1000.] is exact for every [t] a
       whole number of seconds, so the old seconds-valued test is unchanged *)
    | Some t when Float.(elapsed_s >= of_int t / 1000.) ->
        Debug.print
        @@ lazy
             (sprintf "[houdini] lazy pre-pass at a round boundary, %.1f s in"
                elapsed_s);
        run_houdini_prepass e
    | _ -> None

  let houdini_seq_instantiation = config.houdini.questions.seq_instantiation
end
