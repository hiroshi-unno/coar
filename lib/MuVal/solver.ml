(* MuVal: validity checking for muCLP, fixpoint logic over first-order theories,
   by reduction to predicate constraint solving.  The problem is simplified,
   existential quantifiers are Skolemised, and the result is reduced to a pfwCSP
   whose well-founded predicates stand for the least fixpoints (or, with the
   parity-progress-measure reduction, for the alternation) and handed to a
   constraint solver: a solution proves the query valid and a refutation proves
   it invalid.  The dual problem (the negated query) is solved the same way and
   its verdict flipped.  The [task] chooses proving, disproving, both in
   parallel domains, or both with learned partial solutions exchanged between
   the primal and the dual run, the method of Hiroshi Unno, Tachio Terauchi, Yu
   Gu and Eric Koskinen, "Modular Primal-Dual Fixpoint Logic Solving for
   Temporal Verification", POPL 2023.  [solve_pcsp] reads a CHC problem as a
   muCLP query and solves that; it refuses every predicate kind but the ordinary
   one, since a fixpoint problem cannot carry it, and its [sat] carries no
   solution.  [solve_qfl] is the quantitative solver. *)
open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open Preprocessing

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  (** validity checking for muCLP *)

  (* [use_dwf = false] is MuVal's method, not a choice a configuration makes,
     which is why it is fixed here rather than read from [config]: each least
     fixpoint becomes a [WF] unknown over the copied arguments of a recursive
     call, solved by PCSat's well-founded template, whose every instance is a
     ranking function and so well-founded by construction.  MuStrat builds
     the same reducer with [true] because its strategy refinement reads the
     rank unknowns back as [DWF] keys and disjoins pieces onto them.  The
     parity-progress-measure reduction does not read the flag. *)
  module Reducer = MuCLP.Reducer.Make (
    struct
      let config =
        MuCLP.Reducer.Config.
          {
            verbose = config.verbose;
            use_dwf = false;
            reduction = config.fixpoint_reduction;
          }
    end :
      MuCLP.Reducer.Config.ConfigType)

  (* [ad_primal_reduction]: the reduction of the second primal of
     [alternation_depth_primal], or [None] when that primal is not to run.  It
     is the configured reduction with the loop-hierarchy priorities carried as
     a switch ([First_shape_failure]): every family is then generated with
     alternation depth's priorities, exactly as with [loop_levels] off, and a
     family whose two priority functions differ is marked by its switch, which
     [pfwcsp_of] removes before the search and reads as "this primal differs
     from the loop-level one". *)
  let ad_primal_reduction =
    match (config.task, config.fixpoint_reduction) with
    | ( Config.ParallelExc,
        MuCLP.Reducer.Config.Parity_progress_measure
          ({ alternation_depth = true; loop_levels = true; _ } as ppm) )
      when config.alternation_depth_primal ->
        Some
          (MuCLP.Reducer.Config.Parity_progress_measure
             {
               ppm with
               loop_levels_from = MuCLP.Reducer.Config.First_shape_failure;
             })
    | _ -> None

  module ReducerAD = MuCLP.Reducer.Make (
    struct
      let config =
        MuCLP.Reducer.Config.
          {
            verbose = config.verbose;
            use_dwf = false;
            reduction =
              Option.value ad_primal_reduction
                ~default:config.fixpoint_reduction;
          }
    end :
      MuCLP.Reducer.Config.ConfigType)

  module Qelim = MuCLP.Qelim.Make (struct
    let config = config.qelim
  end)

  (* The Skolemising elimination, exact for every sort: what [check] uses
     when [config.qelim] asks for a stepping one ([Mu], [Mu'], [Mus], [Nu])
     that cannot state the problem's existentials. *)
  module Qelim_skolem = MuCLP.Qelim.Make (struct
    let config = { config.qelim with elimination = MuCLP.Qelim.SkolemPred }
  end)

  (* [stepping_elim_applies muclp]: whether every existential binder of
     [muclp]'s query and bodies, read in negation normal form (where the
     eliminator reads them), has a sort the stepping eliminations can walk:
     an integer, or a bit-vector, which they read over the integers.  They
     search for a witness by adding and subtracting the integer one, so a
     real or Boolean binder gives an ill-sorted problem: [exists r : real.
     r + r = 1 /\ P r] stopped MuVal with an uncaught failure of the
     polynomial normaliser under a [Nu] elimination. *)
  let stepping_elim_applies muclp =
    let rec ok = function
      | Formula.Bind (Formula.Exists, senv, body, _) ->
          List.for_all senv ~f:(fun (_, sort) ->
              match sort with T_int.SInt | T_bv.SBV _ -> true | _ -> false)
          && ok body
      | Formula.Bind (_, _, body, _)
      | Formula.UnaryOp (_, body, _)
      | Formula.LetFormula (_, _, _, body, _)
      | Formula.LetRec (_, body, _) ->
          ok body
      | Formula.BinaryOp (_, phi1, phi2, _) -> ok phi1 && ok phi2
      | Formula.Atom _ -> true
    in
    List.for_all
      (muclp.MuCLP.Problem.query
      :: List.map muclp.preds ~f:(fun (pred : MuCLP.Pred.t) -> pred.body))
      ~f:(Formula.nnf_of >> ok)

  (* whether the side that answers keeps what the certificate is written from *)
  let want_certificate =
    match config.print_certificates with
    | Config.No_certificates -> false
    | Unchecked_certificates | Checked_certificates -> true

  (* The primal's constraint solver; when a certificate is wanted, a PCSat
     one records a definition for every predicate its preprocessor resolves
     away ([witness.sat]).  Without it such a predicate has no entry of its
     own in the solution, and the certificate's invariant for it would be
     missing or wrong: a function called with a constant argument (an
     assertion helper applied to [0] and [1]) is resolved into its callers,
     and the post-fixpoint check of the whole assignment then fails on it,
     withholding every invariant.  The definitions are built only when the
     answer is assembled, so the verdict and the search are those of the
     configuration as written. *)
  let pcsp_solver ~primal =
    let open Or_error in
    ExtFile.unwrap
      (if primal then config.pcsp_solver_primal else config.pcsp_solver_dual)
    >>= fun cfg ->
    let cfg =
      match cfg with
      | PCSPSolver.Config.PCSat c when primal && want_certificate ->
          PCSPSolver.Config.PCSat
            { c with witness = { c.witness with sat = true } }
      | cfg -> cfg
    in
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  let optimizer_cfg = ExtFile.unwrap config.optimizer

  (* [preprocess ?erased_constants muclp]: the optimized problem; with
     [erased_constants], the argument positions the optimizer removed as
     constant are added to it (see [MuCLP.Optimizer.OptimizerType]) *)
  let preprocess ?(id = None) ?(elim_forall = true) ?(elim_exists = true)
      ?(elim_pvar_args = true) ?erased_constants muclp =
    let open Or_error in
    optimizer_cfg >>= fun optimizer_cfg ->
    Ok (MuCLP.Optimizer.make optimizer_cfg)
    >>= fun (module Optimizer : MuCLP.Optimizer.OptimizerType) ->
    (* always: a predicate applied without a definition would otherwise reach
       the reducer, which dies on its arity lookup with an internal error that
       does not say the input is at fault; the check is one pass over the
       problem's formulas *)
    let muclp =
      Common.PhaseTime.with_phase "muval-check-problem" @@ fun () ->
      MuCLP.Problem.check_problem muclp
    in
    Debug.print ~id
    @@ lazy (sprintf "before optimization: %s\n" @@ MuCLP.Problem.str_of muclp);
    (* with COAR_SHARE_CENSUS set, the sharing of the muCLP before and after
       each step of the optimization (an instrument: prints only) *)
    Common.DagCensus.report "muval-optimize: input" muclp;
    let muclp =
      Common.PhaseTime.with_phase "muval-optimize" @@ fun () ->
      let muclp = MuCLP.Problem.simplify muclp in
      Common.DagCensus.report "muval-optimize: after simplify" muclp;
      Optimizer.f ~id ~elim_forall ~elim_exists ~elim_pvar_args ?erased_constants
        muclp
    in
    Common.DagCensus.report "muval-optimize: output" muclp;
    Debug.print ~id
    @@ lazy (sprintf "after optimization: %s\n" @@ MuCLP.Problem.str_of muclp);
    Ok muclp

  (* [reduction_stats ~side ~muclp pfwcsp]: one line describing the parity
     unknowns of [pfwcsp], read off its kind map.  A family is one [Kind.nwf]
     (one per strongly connected component reduced, or one for the whole
     problem); its ranked predicates are the tags its relations relate, and
     each holds [max_pri] ranking functions, shared by every relation of the
     family that mentions it, over that predicate's arguments.  [named_parts]
     counts the unknowns that name a part of a clause and that no elimination
     may remove (those [name_multiplied_parts] added), with their arities
     summed.  The last fields describe [muclp], the problem the reduction
     received ([Reducer.scc_alternation_depths]): its [predicates]; [sccs],
     the strongly connected components of its call graph, an acyclic single
     predicate included; [nontrivial_sccs], those with a cycle; [ranked_sccs],
     the nontrivial ones holding a least-fixpoint predicate (on this side);
     [alternation_depth], the largest alternation depth of a predicate, each
     computed within its component (0 without predicates), a [MuOrNu]
     predicate adding no alternation, so that a problem and its dual report
     the same value; [ad_per_scc], each nontrivial component's largest one,
     [/]-separated ([-] for none); [alternation_depth_as_nu], the largest
     with [MuOrNu] read as [Nu], the reading the reduction assigns priorities
     from where it reads the alternation depth.  These are fields of the
     problem, whatever the reduction configured. *)
  let reduction_stats ~side ~muclp pfwcsp =
    let fams =
      Map.Poly.fold (PCSP.Problem.kind_map_of pfwcsp) ~init:Map.Poly.empty
        ~f:(fun ~key:_ ~data acc ->
          match data with
          | Kind.Parity (nwf, (l, r)) ->
              Map.Poly.update acc (Ident.name_of_tvar nwf.Kind.name)
                ~f:(function
                | None -> (nwf, 1, Set.Poly.of_list [ l; r ])
                | Some (nwf, n, tags) -> (nwf, n + 1, Set.add (Set.add tags l) r))
          | _ -> acc)
    in
    let data = Map.Poly.data fams in
    let arity_of nwf tag =
      List.length (Hashtbl.Poly.find_exn nwf.Kind.sorts_map tag)
    in
    (* the unknowns [name_multiplied_parts] added (none without it): the
       protected names present in this problem, and their arities summed *)
    let named =
      PCSP.Parser.premise_unknowns_of (PCSP.Problem.senv_of pfwcsp)
    in
    let named_args =
      Set.sum (module Int) named ~f:(fun v ->
          List.length
            (Logic.Sort.args_of
               (Map.Poly.find_exn (PCSP.Problem.senv_of pfwcsp) v)))
    in
    (* the well-foundedness unknowns of the well-foundedness reduction, and
       the widest unknown of each kind, other unknowns' arity counting every
       argument the reduction prepended *)
    let wf_count, widest_wf, widest_other =
      let kind_map = PCSP.Problem.kind_map_of pfwcsp in
      Map.Poly.fold (PCSP.Problem.senv_of pfwcsp) ~init:(0, 0, 0)
        ~f:(fun ~key ~data (n, w, o) ->
          let a = List.length (Logic.Sort.args_of data) in
          match Map.Poly.find kind_map key with
          | Some Kind.WF -> (n + 1, max w a, o)
          | _ -> (n, w, max o a))
    in
    let sccs = Reducer.scc_alternation_depths muclp in
    let nontrivial = List.filter sccs ~f:(fun (_, cyclic, _, _, _) -> cyclic) in
    sprintf
      "reduction-stats: side=%s parity_families=%d parity_relations=%d \
       ranked_predicates=%d ranking_functions=%d ranking_function_args=%d \
       components=%s named_parts=%d named_part_args=%d fn_unknowns=%d \
       wf_unknowns=%d widest_wf_args=%d widest_other_args=%d predicates=%d \
       sccs=%d nontrivial_sccs=%d ranked_sccs=%d alternation_depth=%d \
       ad_per_scc=%s alternation_depth_as_nu=%d"
      side (List.length data)
      (List.sum (module Int) data ~f:(fun (_, n, _) -> n))
      (List.sum (module Int) data ~f:(fun (_, _, t) -> Set.length t))
      (List.sum
         (module Int)
         data
         ~f:(fun (nwf, _, t) -> nwf.Kind.max_pri * Set.length t))
      (List.sum
         (module Int)
         data
         ~f:(fun (nwf, _, t) ->
           nwf.Kind.max_pri * Set.sum (module Int) t ~f:(arity_of nwf)))
      (String.concat_map_list ~sep:"/" data ~f:(fun (nwf, _, _) ->
           string_of_int nwf.Kind.max_pri))
      (Set.length named) named_args
      (Map.Poly.count (PCSP.Problem.kind_map_of pfwcsp) ~f:(function
         | Kind.FN -> true
         | _ -> false))
      wf_count widest_wf widest_other
      (List.length muclp.MuCLP.Problem.preds)
      (List.length sccs) (List.length nontrivial)
      (List.count nontrivial ~f:(fun (_, _, has_mu, _, _) -> has_mu))
      (List.fold sccs ~init:0 ~f:(fun m (_, _, _, a, _) -> max m a))
      (match nontrivial with
      | [] -> "-"
      | _ ->
          String.concat_map_list ~sep:"/" nontrivial ~f:(fun (_, _, _, a, _) ->
              string_of_int a))
      (List.fold sccs ~init:0 ~f:(fun m (_, _, _, _, a) -> max m a))

  (* [~ad:true] reduces with [ReducerAD] (the second primal of
     [alternation_depth_primal]); the families then still carry their
     switches, which [check] removes. *)
  let pfwcsp_of ?(id = None) ?(ad = false) ?layout ~side ~messenger ~exc_info
      unknowns muclp =
    let muclp =
      MuCLP.Problem.complete_psort (Kind.pred_sort_env_map_of unknowns)
      @@ MuCLP.Problem.complete_tsort
      @@ MuCLP.Problem.aconv_tvar muclp
    in
    (*Debug.print ~id @@ lazy (sprintf "Preprocessed muCLP: %s\n" @@ str_of muclp);*)
    Common.DagCensus.report ("muval-reduce: input " ^ side) muclp;
    let pfwcsp =
      let pfwcsp, _ =
        let exchange = Option.is_some exc_info in
        Common.PhaseTime.with_phase "muval-reduce" @@ fun () ->
        let name_shared_args =
          match config.name_args with
          | Shared_args -> true
          | All_free_args -> false
        in
        let name_gain =
          match config.name_rule with
          | Gaining_parts -> true
          | Fewest_to_bound -> false
        in
        (* [side] is "dual" for the query's negation and "primal" or
           "primal-ad" otherwise *)
        let name_bound =
          let dual = String.equal side "dual" in
          match config.name_sides with
          | Both_sides -> config.name_multiplied_parts
          | Dual_only -> if dual then config.name_multiplied_parts else None
          | Primal_only -> if dual then None else config.name_multiplied_parts
        in
        let factor_guards =
          match config.guarded_disjunctions with
          | As_reduced -> false
          | Factor_exclusive_guards | Merge_witnesses_and_factor -> true
        in
        let merge_witness_vars =
          match config.guarded_disjunctions with
          | Merge_witnesses_and_factor -> true
          | As_reduced | Factor_exclusive_guards -> false
        in
        if ad then
          ReducerAD.f ~id ~factor_guards ~merge_witness_vars ?layout ?name_bound ~name_gain
            ~name_shared_args ~exchange ~messenger muclp unknowns
        else
          Reducer.f ~id ~factor_guards ~merge_witness_vars ?layout ?name_bound ~name_gain
            ~name_shared_args ~exchange ~messenger muclp unknowns
      in
      match exc_info with
      | None -> pfwcsp
      | Some (partial_sol_targets, dep_graph) ->
          PCSP.Problem.update_params pfwcsp
          @@ PCSP.Problem.
               { (params_of pfwcsp) with partial_sol_targets; dep_graph }
    in
    if Common.DagCensus.enabled then (
      let phis = PCSP.Problem.formulas_of ~full_clauses:false pfwcsp in
      Common.DagCensus.report ~items:(Set.length phis)
        ("muval-reduce: output " ^ side) phis);
    Debug.print ~id
    @@ lazy
         (sprintf "******* Generated pfwCSP:\n%s" @@ PCSP.Problem.str_of pfwcsp);
    (* one write per line: the primal and the dual are reduced in two domains
       at once, so a line written in two parts (text, then newline) can be
       split by the other side's line *)
    if config.output_reduction_stats then (
      Out_channel.output_string stderr
        (reduction_stats ~side ~muclp pfwcsp ^ "\n");
      Out_channel.flush stderr);
    pfwcsp

  (* [check ~ad:true] is the second primal of [alternation_depth_primal]
     (with [~primal:true]): its families keep alternation depth's priorities
     throughout, and when no family's loop-hierarchy priorities differ from
     them the problem is the loop-level primal's own, so it answers [Unknown]
     at once without solving. *)
  (* [check] answers the verdict of [muclp] (the query's, with [~primal];
     else that of the dual problem it is given, not yet flipped), the CEGIS
     iteration count, and, with [want_certificate], what the certificate of
     that answer is written from: the problem reduced, the solution or
     refutation, the ranking certificates and the prepended positions.
     Without [want_certificate] the third component is [None] and the run is
     the one it always was. *)
  let check ~primal ?(ad = false) ?(id = None) ~messenger ~exc_info muclp =
    let check_forall_only (exi_senv, kind_map) muclp :
        (Verdict.t * int * Certificate.evidence option) Or_error.t =
      let open Or_error.Monad_infix in
      pcsp_solver ~primal >>= fun (module PCSPSolver) ->
      let layout =
        if want_certificate then Some (Hashtbl.Poly.create ()) else None
      in
      let pcsp =
        muclp
        |> pfwcsp_of ~id ~ad ?layout
             ~side:(if ad then "primal-ad" else if primal then "primal" else "dual")
             ~messenger ~exc_info (exi_senv, kind_map)
        |> PCSP.Problem.map ~f:Logic.Term.refresh
      in
      let evidence solution kind_certs =
        if not want_certificate then None
        else
          Some
            Certificate.
              {
                side = (if ad then Primal_ad else if primal then Primal else Dual);
                solved = Some muclp;
                solution = Some solution;
                kind_certs;
                extended = Option.value_exn layout;
                wf_reduction =
                  (match config.fixpoint_reduction with
                  | MuCLP.Reducer.Config.Wf_reduction _ -> not ad
                  | Parity_progress_measure _ -> false);
              }
      in
      let pcsp, differs =
        if ad then
          let params = PCSP.Problem.params_of pcsp in
          let kind_map, differs = Kind.drop_priority_switches params.kind_map in
          (PCSP.Problem.update_params pcsp PCSP.Params.{ params with kind_map }, differs)
        else (pcsp, true)
      in
      if not differs then (
        Debug.print ~id
        @@ lazy
             "the alternation-depth primal coincides with the loop-level one: \
              not solved";
        Ok (Verdict.Unknown, 0, None))
      else
      (if want_certificate then
         PCSPSolver.solve_with_kind_certificates pcsp
         >>= fun (sol, info, certs) -> Ok ((sol, info), certs)
       else PCSPSolver.solve pcsp >>= fun r -> Ok (r, Map.Poly.empty))
      >>= function
      | (PCSP.Problem.Sat sol, info), certs -> (
          match config.output_certificates with
          | Some filename ->
              Debug.print
              @@ lazy (sprintf "Outputting certificates to %s" filename);
              let file = Out_channel.create ~binary:false filename in
              Map.Poly.iteri sol ~f:(fun ~key ~data ->
                  try
                    let prefix = "U_state_" in
                    let plen = String.length prefix in
                    let slen = String.length (Ident.name_of_tvar key) in
                    if slen < plen + 1 then invalid_arg "too short";
                    if not (String.is_prefix ~prefix (Ident.name_of_tvar key))
                    then invalid_arg "invalid prefix";
                    if Stdlib.((Ident.name_of_tvar key).[slen - 1] <> '_') then
                      invalid_arg "missing trailing underscore";
                    let pid =
                      String.sub (Ident.name_of_tvar key) ~pos:plen
                        ~len:(slen - plen - 1)
                    in
                    let fml =
                      let args, term = Logic.ExtTerm.let_lam data in
                      let fml =
                        Logic.ExtTerm.to_old_formula Map.Poly.empty
                          (Map.Poly.of_alist_exn args)
                          term []
                      in
                      let ren =
                        let args' =
                          Map.Poly.find_exn
                            (PCSP.Problem.params_of pcsp).arg_original_names
                            (Ident.Pvar ("state_" ^ pid))
                        in
                        Map.Poly.of_alist_exn
                        @@ List.map2_exn args args' ~f:(fun (v, _) orig_name ->
                            (v, orig_name))
                      in
                      Formula.rename ren fml
                    in
                    Out_channel.output_string file
                    @@ sprintf "%s, %s\n" pid (Formula.str_of ~c_style:true fml)
                  with exn_ when not (Common.Timer.is_async exn_) ->
                    (* an unknown that is not a location's, or whose
                       solution does not match its name table, has no line
                       in this file; say which and why *)
                    Debug.print ~id
                    @@ lazy
                         (sprintf "output_certificates: %s not written: %s"
                            (Ident.name_of_tvar key) (Exn.to_string exn_)));
              Out_channel.flush file;
              Out_channel.close file;
              Ok (Verdict.Valid, info, evidence (PCSP.Problem.Sat sol) certs)
          | None -> Ok (Verdict.Valid, info, evidence (PCSP.Problem.Sat sol) certs))
      | (Unsat r, info), _ -> Ok (Invalid, info, evidence (PCSP.Problem.Unsat r) Map.Poly.empty)
      | (Unknown, info), _ -> Ok (Unknown, info, None)
      | (OutSpace _, _), _ -> failwith "out of space" (* TODO *)
      | (Timeout, info), _ -> Ok (Timeout, info, None)
    in
    (* [bounded_exists]: the existentials of [muclp] are eliminated by
       [MuCLP.Qelim]'s [Nu range] encoding, which replaces [exists x. F x] by
       a search for a witness in [-range, range] only.  The existentials
       occur positively (the eliminator works on the negation normal form),
       so the encoded problem implies [muclp] and is not implied by it: a
       solution of the encoded problem is one of [muclp], a refutation is
       not.  [exists x. x > 120 /\ P x] with [P] true at every non-negative
       [x] is valid, yet with range 100 the encoded primal was refuted and
       printed [invalid]; on the dual side the same refutation was flipped
       into a wrong [valid].  So on such a side [Invalid] (not yet flipped) is
       read as [Unknown]; every other mode of elimination is exact.
       [skolem_instead]: a stepping elimination asked for on a problem whose
       existentials it cannot state ([stepping_elim_applies]) is replaced by
       the exact Skolemising one, so that side is not bounded. *)
    let skolem_instead =
      (match config.qelim.MuCLP.Qelim.Config.elimination with
       | MuCLP.Qelim.(Mu | Mu' | Mus | Nu _) -> true
       | SkolemFun | SkolemPred -> false)
      && not (stepping_elim_applies muclp)
    in
    let bounded_exists =
      (match config.qelim.MuCLP.Qelim.Config.elimination with
       | MuCLP.Qelim.Nu _ -> not skolem_instead
       | Mu | Mu' | Mus | SkolemFun | SkolemPred -> false)
      && not (MuCLP.Problem.has_only_forall muclp)
    in
    let muclp, unknowns =
      let unknowns = (Map.Poly.empty, Map.Poly.empty) in
      if MuCLP.Problem.has_only_forall muclp then
        (* Skolemization is not required *)
        (muclp, unknowns)
      else (
        (* Skolemize existential quantifiers *)
        if false then
          Debug.print ~id
          @@ lazy (sprintf "Input muCLP: %s\n" @@ MuCLP.Problem.str_of muclp);
        let muclp, unknowns =
          if skolem_instead then (
            Debug.print ~id
            @@ lazy
                 "an existential is neither an integer nor a bit-vector: \
                  Skolemised instead of the configured stepping elimination";
            Qelim_skolem.elim_exists (muclp, unknowns))
          else Qelim.elim_exists (muclp, unknowns)
        in
        Debug.print ~id
        @@ lazy (sprintf "Skolemized: %s\n" @@ MuCLP.Problem.str_of muclp);
        (muclp, unknowns))
    in
    (* [real_witness]: a Skolem witness predicate ([FN], witness last) of an
       existential over the reals.  The constraint solver searched such a
       witness among the integers only: [exists r : real. r + r = 1 /\ P r]
       with [P x =nu x >= 0] (witness 1/2) was refuted at the first
       iteration, and with [r + r = 2] (witness 1) proved.  That refutation
       came from the strategy game that eliminates the witness predicate,
       whose opponent moves were declared integers, and the game now plays
       over the reals; the guard is kept because the witness templates still
       have integer argument coefficients and nothing yet shows that no other
       step refutes from an integer-only space.  A solution is still one of
       the problem; a refutation is read as [Unknown] like
       [bounded_exists]'s. *)
    let real_witness =
      let exi_senv, kind_map = unknowns in
      Map.Poly.existsi exi_senv ~f:(fun ~key ~data ->
          Kind.is_fn (Kind.kind_of kind_map key)
          &&
          match List.last (Logic.Sort.args_of data) with
          | Some s -> Logic.ExtTerm.is_real_sort s
          | None -> false)
    in
    Or_error.map (check_forall_only unknowns muclp) ~f:(function
      | Verdict.Invalid, info, _ when bounded_exists ->
          Debug.print ~id
          @@ lazy
               "refuted with existential witnesses searched in a bounded \
                range only: not a refutation of the problem, answered unknown";
          (Verdict.Unknown, info, None)
      | Verdict.Invalid, info, _ when real_witness ->
          Debug.print ~id
          @@ lazy
               "refuted with a real-sorted existential witness the \
                constraint solver searches among the integers only: not a \
                refutation of the problem, answered unknown";
          (Verdict.Unknown, info, None)
      | res -> res)

  (* [ground_decide muclp]: with [ground_query_solve = Ground_solve], the
     verdict of a ground query decided on its finite reachable part
     ([MuCLP.GroundSolve.run]), or [None] when the problem is outside that
     class, an evaluation is refused, or the reachable atoms exceed the
     budget; the caller then solves [muclp] as it would have.  Called on the
     optimized problem the reduction would receive: the decision is exact for
     that problem, and the optimizer is equivalence-preserving.  With
     [output_reduction_stats], one stderr line says what happened. *)
  let ground_decide ?(id = None) muclp =
    MuCLP.GroundSolve.run ~phase:"muval-ground-solve"
      ~report:(fun line ->
        Debug.print ~id @@ lazy line;
        if config.output_reduction_stats then (
          Out_channel.output_string stderr (line ^ "\n");
          Out_channel.flush stderr))
      config.ground_query_solve muclp

  (* the evidence of an answer [ground_decide] gave on [muclp]: the problem it
     decided, from whose reached atoms a valid answer's invariants are read
     (no constraint solver's solution) *)
  let ground_evidence muclp =
    if not want_certificate then None
    else
      Some
        Certificate.
          {
            side = Ground;
            solved = Some muclp;
            solution = None;
            kind_certs = Map.Poly.empty;
            extended = Hashtbl.Poly.create ();
            wf_reduction = false;
          }

  (* [witness_constant data]: a value [c] with [data c] true, when [data] (a
     candidate of an [FN] unknown, [fun x1 ... xk -> phi]) does not depend on
     its leading arguments [x1 ... x(k-1)] and its witness [xk] is an
     integer; [None] otherwise.  [c] is read off an equation [t1 = t2] of
     [phi] linear in [xk] with coefficient +-1 (two evaluations), and kept
     only if [phi] evaluates true at it; so [c] is a value the candidate
     allows, but not necessarily the only one.  Heuristic only: any value is
     sound for [witness_refute], which never trusts it. *)
  let witness_constant data =
    try
      let params =
        List.mapi (fst @@ Logic.ExtTerm.let_lam data) ~f:(fun i (_, s) ->
            (Ident.Tvar (sprintf "x%d" (i + 1)), s))
      in
      match List.last params with
      | None -> None
      | Some (x, s) ->
          let phi =
            Logic.ExtTerm.to_old_formula Map.Poly.empty
              (Map.Poly.of_alist_exn params) data
              (List.map params ~f:(fst >> Logic.ExtTerm.mk_var))
          in
          let sort = Logic.ExtTerm.to_old_sort s in
          if
            (not (Term.is_int_sort sort))
            || not
                 (Set.for_all (Formula.tvs_of phi) ~f:(Ident.tvar_equal x))
          then None
          else
            let at v t =
              match
                Evaluator.eval_term
                  ~env:(Map.Poly.singleton x (Value.Int (Z.of_int v)))
                  t
              with
              | Value.Int z -> Some z
              | _ -> None
            in
            let holds z =
              Evaluator.eval ~env:(Map.Poly.singleton x (Value.Int z)) phi
            in
            let from_eq t1 t2 =
              let d = T_int.mk_sub t1 t2 in
              match (at 0 d, at 1 d, at 2 d) with
              | Some d0, Some d1, Some d2
                when Z.equal (Z.sub d1 d0) (Z.sub d2 d1)
                     && Z.equal (Z.abs (Z.sub d1 d0)) Z.one ->
                  let c = Z.neg (Z.mul d0 (Z.sub d1 d0)) in
                  if holds c then Some c else None
              | _ -> None
            in
            let rec find = function
              | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _)
                ->
                  from_eq t1 t2
              | Formula.BinaryOp ((Formula.And | Formula.Or), p1, p2, _) -> (
                  match find p1 with Some c -> Some c | None -> find p2)
              | _ -> None
            in
            find phi
    with exn when not (Common.Timer.is_async exn) -> None

  (* [witness_refute muclp sol]: with [dual_witness_refutation =
     Witness_refutation], [Some Invalid] when the primal [muclp] (the
     problem the dual was built from by [MuCLP.Util.get_dual]) is refuted on
     the instance [sol] suggests, [None] otherwise.  [sol] is a candidate of
     the dual's constraint problem; its [FN_<owner>_<x>_] entries (with an
     optional numeric suffix: [MuCLP.Qelim]'s naming of the Skolem predicate
     of the existential [x] in the dual body of [owner], ["query"] for the
     query) whose candidates are constants ([witness_constant]) give [x] its
     value.  Sound for every [sol]: [MuCLP.GroundSolve.refute_instance] only
     refutes when the query is false under a weakening of [muclp], whatever
     the values; the name matching only chooses values.  [tried] holds the
     constant sets already tried, so each is tried once. *)
  let witness_refute ~tried muclp sol =
    match config.dual_witness_refutation with
    | No_witness_refutation | Seed_primal_labeling _ -> None
    | Witness_refutation { atom_budget; max_combos; choice_values } ->
        let consts =
          Map.Poly.filter_mapi sol ~f:(fun ~key ~data ->
              if String.is_prefix (Ident.name_of_tvar key) ~prefix:"FN_" then
                witness_constant data
              else None)
        in
        let key =
          String.concat ~sep:","
          @@ List.map (Map.Poly.to_alist consts) ~f:(fun (k, c) ->
              Ident.name_of_tvar k ^ "=" ^ Z.to_string c)
        in
        if Map.Poly.is_empty consts || Hash_set.mem tried key then None
        else (
          Hash_set.add tried key;
          let nullary =
            Set.Poly.of_list
            @@ "query"
               :: List.filter_map muclp.MuCLP.Problem.preds ~f:(fun p ->
                   if List.is_empty p.MuCLP.Pred.args then
                     Some (Ident.name_of_pvar p.MuCLP.Pred.name)
                   else None)
          in
          (* the constants of [FN_<owner>_<x>_] and its numbered copies *)
          let consts_of owner x =
            let base = "FN_" ^ owner ^ "_" ^ Ident.name_of_tvar x ^ "_" in
            Map.Poly.fold consts ~init:[] ~f:(fun ~key ~data acc ->
                let n = Ident.name_of_tvar key in
                if
                  String.is_prefix n ~prefix:base
                  && String.for_all
                       (String.drop_prefix n (String.length base))
                       ~f:Char.is_digit
                then Value.Int data :: acc
                else acc)
            |> List.dedup_and_sort ~compare:Stdlib.compare
          in
          let inst ~owner x sort =
            if Term.is_bool_sort sort then
              Some [ Value.Bool true; Value.Bool false ]
            else if not (Term.is_int_sort sort) then None
            else
              let cs = consts_of owner x in
              if Set.mem nullary owner && not (List.is_empty cs) then Some cs
              else
                Some
                  (List.dedup_and_sort ~compare:Stdlib.compare
                     (cs
                     @ List.map choice_values ~f:(fun v -> Value.Int (Z.of_int v))
                     ))
          in
          let t0 = Common.PhaseTime.now () in
          let res, stats =
            Common.PhaseTime.with_phase "muval-witness-refute" @@ fun () ->
            MuCLP.GroundSolve.refute_instance ~atom_budget ~max_combos ~inst
              muclp
          in
          let line =
            sprintf "witness-refute: %s atoms=%d constants=%d time=%.3f [%s]"
              (match res with
              | `Refuted -> "refuted"
              | `Not_refuted why -> "not refuted, " ^ why)
              stats.MuCLP.GroundSolve.atoms (Map.Poly.length consts)
              (Common.PhaseTime.now () -. t0)
              key
          in
          Debug.print @@ lazy line;
          if config.output_reduction_stats then (
            Out_channel.output_string stderr (line ^ "\n");
            Out_channel.flush stderr);
          match res with `Refuted -> Some Verdict.Invalid | `Not_refuted _ -> None)

  (* [witness_seeds ~tried muclp sol]: with [dual_witness_refutation =
     Seed_primal_labeling], the seeds [sol] suggests for the primal's
     constraint solver, or [None] (another configuration, no constant
     witness, or a set of constants already sent).  Each [FN_<owner>_<x>_<n>]
     entry of [sol] whose candidate is a constant [c] ([witness_constant])
     seeds the binder [x] of [owner] (the longest owner name that prefixes
     the entry, ["query"] or a predicate of [muclp]) with [c] alone when
     [owner] is the query or a nullary predicate (the program's inputs) and
     with [c] and [choice_values] otherwise (and such a non-input constant
     also joins the choice values the message carries, since the receiver's
     clauses may have renamed the binder); and each predicate application
     in the body of such an input owner gives an atom pattern, its arguments
     evaluated with the seeded binders at their constants (an argument that
     does not evaluate is left open).  Nothing here is trusted: the receiver
     uses the seeds only to choose which ground instances of its own clauses
     it holds as examples. *)
  let witness_seeds ~tried muclp sol =
    match config.dual_witness_refutation with
    | No_witness_refutation | Witness_refutation _ -> None
    | Seed_primal_labeling
        {
          atom_budget;
          max_combos;
          choice_values;
          seed_scope;
          seed_keep;
          stop_after_fruitless;
        } ->
        let consts =
          Map.Poly.filter_mapi sol ~f:(fun ~key ~data ->
              if String.is_prefix (Ident.name_of_tvar key) ~prefix:"FN_" then
                witness_constant data
              else None)
        in
        let key =
          String.concat ~sep:","
          @@ List.map (Map.Poly.to_alist consts) ~f:(fun (k, c) ->
              Ident.name_of_tvar k ^ "=" ^ Z.to_string c)
        in
        if Map.Poly.is_empty consts || Hash_set.mem tried key then None
        else (
          Hash_set.add tried key;
          (* each owner with its body and whether it is the query or a
             nullary predicate *)
          let owners =
            ("query", muclp.MuCLP.Problem.query, true)
            :: List.map muclp.MuCLP.Problem.preds ~f:(fun p ->
                ( Ident.name_of_pvar p.MuCLP.Pred.name,
                  p.MuCLP.Pred.body,
                  List.is_empty p.MuCLP.Pred.args ))
          in
          let choice = List.map choice_values ~f:(fun v -> Value.Int (Z.of_int v)) in
          (* (owner, binder, constant) of each constant [FN] entry *)
          let entries =
            Map.Poly.fold consts ~init:[] ~f:(fun ~key ~data acc ->
                let n = Ident.name_of_tvar key in
                let owner =
                  List.filter owners ~f:(fun (o, _, _) ->
                      String.is_prefix n ~prefix:("FN_" ^ o ^ "_"))
                  |> List.max_elt ~compare:(fun (o1, _, _) (o2, _, _) ->
                      Int.compare (String.length o1) (String.length o2))
                in
                match owner with
                | None -> acc
                | Some ((o, _, _) as owner) ->
                    let rest = String.drop_prefix n (String.length o + 4) in
                    let x =
                      String.rstrip rest ~drop:Char.is_digit
                      |> String.chop_suffix_if_exists ~suffix:"_"
                    in
                    if String.is_empty x then acc else (owner, x, data) :: acc)
          in
          let seeds =
            List.map entries ~f:(fun ((_, _, inputs), x, c) ->
                (x, if inputs then [ Value.Int c ] else Value.Int c :: choice))
          in
          (* the constants of the binders that are not inputs (a choice inside
             a transition) join every unnamed variable's values: the
             receiver's clauses keep no binder name to put them on *)
          let choice =
            List.dedup_and_sort ~compare:Stdlib.compare
              (choice
              @ List.filter_map entries ~f:(fun ((_, _, inputs), _, c) ->
                  if inputs then None else Some (Value.Int c)))
          in
          (* the applications in the body of an input owner (the query or a
             nullary predicate) with its seeded binders at their constants:
             an argument that evaluates is given, any other is open.  The
             receiver's clauses may have renamed the binders, never the
             predicates' argument positions, so these patterns find the
             seeded instance where the names do not. *)
          let atoms =
            List.concat_map owners ~f:(fun (o, body, inputs) ->
                let env =
                  List.filter_map entries ~f:(fun ((o', _, _), x, c) ->
                      if String.equal o o' then
                        Some (Ident.Tvar x, Value.Int c)
                      else None)
                in
                if (not inputs) || List.is_empty env then []
                else
                  let env = Map.Poly.of_alist_reduce env ~f:(fun v _ -> v) in
                  Set.to_list (fst (Formula.atoms_of ~nrec:true body))
                  |> List.filter_map ~f:(function
                    | Atom.App (Predicate.Var (q, _), ts, _) ->
                        let vs =
                          List.map ts ~f:(fun t ->
                              try Some (Evaluator.eval_term ~env t)
                              with exn when not (Common.Timer.is_async exn) ->
                                None)
                        in
                        if List.exists vs ~f:Option.is_some then
                          Some (Ident.name_of_pvar q, vs)
                        else None
                    | _ -> None))
          in
          if List.is_empty seeds then None
          else (
            if config.output_reduction_stats then (
              Out_channel.output_string stderr
                (sprintf "ground-seeds: sent %d binder(s), %d atom(s) [%s]\n"
                   (List.length seeds) (List.length atoms) key);
              Out_channel.flush stderr);
            Some
              PCSP.Problem.
                {
                  seeds;
                  atoms;
                  choice_values = choice;
                  atom_budget;
                  max_combos;
                  trace = config.output_reduction_stats;
                  synthesis_reads =
                    (match seed_scope with
                    | Labeling_and_synthesis -> true
                    | Labeling_only -> false);
                  refutation_cone =
                    (match seed_keep with
                    | All_instances -> false
                    | Refutation_cone -> true);
                  stop_after_fruitless;
                }))

  let rec solve_primal ?(id = None) ~messenger ~exc_info flip_on_failure muclp =
    Or_error.Monad_infix.(
      check ~primal:true ~id ~messenger ~exc_info muclp >>= function
      | ((Unknown | Timeout) as r), info, ev ->
          if flip_on_failure then
            solve_dual ~id ~messenger ~exc_info false muclp
          else Ok (r, info, ev)
      | x ->
          Debug.print @@ lazy "primal finished";
          Ok x)

  and solve_dual ?(id = None) ~messenger ~exc_info flip_on_failure muclp =
    Or_error.Monad_infix.(
      check ~primal:false ~id ~messenger ~exc_info (MuCLP.Util.get_dual muclp)
      >>= function
      | ((Unknown | Timeout) as r), info, ev ->
          if flip_on_failure then
            solve_primal ~id ~messenger ~exc_info false muclp
          else Ok (r, info, ev)
      | res, info, ev ->
          Debug.print @@ lazy "dual finished";
          Ok (Verdict.flip res, info, ev))

  (* [number_of_pairs] primal/dual pairs, each in its own domains; the first
     task to decide answers.  Requires [number_of_pairs >= 1]. *)
  let solve_primal_dual ~number_of_pairs muclp =
    let open Or_error.Monad_infix in
    assert (number_of_pairs >= 1);
    let pool =
      Util.Task.setup_pool ~num_additional_domains:(2 * number_of_pairs)
    in
    let rec gen_tasks i =
      if i < number_of_pairs then
        let task_primal =
          let id = Some ((i * 2) + 1) in
          Util.Task.async pool (fun () ->
              Debug.print @@ lazy "task_prove";
              solve_primal ~id ~messenger:None ~exc_info:None false muclp)
        in
        let task_dual =
          let id = Some ((i * 2) + 2) in
          Util.Task.async pool (fun () ->
              Debug.print @@ lazy "task_disprove";
              solve_dual ~id ~messenger:None ~exc_info:None false muclp)
        in
        task_primal :: task_dual :: gen_tasks (i + 1)
      else []
    in
    (* the first task that decides ([Valid] or [Invalid]) answers; an
       undecided task ([Unknown], [Timeout]) leaves the run to the others, and
       only when every task has ended undecided does one of them answer (the
       first in task order).
       Reading the first task to end, whatever it said, lost the other side's
       answer whenever one side gave up early -- as a side whose refutation is
       not trusted does.  An error ends the run at once, as before. *)
    let await_decided promises =
      let rec loop () =
        ignore @@ Core_unix.nanosleep 0.1;
        let ended = List.filter_map promises ~f:Atomic.get in
        match
          List.find ended ~f:(function
            | Ok (Ok ((Verdict.Valid | Verdict.Invalid), _, _)) -> true
            | Ok (Ok ((Verdict.Unknown | Verdict.Timeout), _, _)) -> false
            | Ok (Error _) | Error _ -> true)
        with
        | Some (Ok v) -> v
        | Some (Error (e, bt)) -> Stdlib.Printexc.raise_with_backtrace e bt
        | None -> (
            if List.length ended < List.length promises then loop ()
            else
              match List.find_map promises ~f:Atomic.get with
              | Some (Ok v) -> v
              | Some (Error (e, bt)) -> Stdlib.Printexc.raise_with_backtrace e bt
              | None -> assert false)
      in
      loop ()
    in
    try
      gen_tasks 0 |> await_decided >>= function
      | sol, info, ev ->
          Debug.print @@ lazy "task over";
          Ok (sol, info, ev)
    with err when not (Common.Timer.is_async err) ->
      (* the backtrace of the raise, which [Util.Task] carries over from the
         worker domain: without it an exception from a task is reported with
         no location *)
      Or_error.of_exn ~backtrace:`Get err

  (*
  type info += Examples of ExClauseSet.t

  let send_examples messenger id exs =
    send_boardcast messenger id @@ Examples exs

  let receive_examples messenger_opt id =
    match messenger_opt with
    | None -> Set.Poly.empty
    | Some messenger ->
        receive_all_infos_with messenger id ~filter:(function
          | Examples _ -> true
          | _ -> false)
        |> List.map ~f:(function _, Examples exs -> exs | _ -> Set.Poly.empty)
        |> Set.Poly.union_list
  *)

  let receive_candidate_solutions messenger_opt mean_id cache =
    match messenger_opt with
    | None -> ()
    | Some messenger ->
        Messenger.receive_all_infos_with messenger mean_id ~filter:(function
          | PCSP.Problem.CandidateSolution _ -> true
          | _ -> false)
        |> List.iter ~f:(function
          | _, PCSP.Problem.CandidateSolution sol -> Hash_set.add cache sol
          | _ -> assert false)

  let send_records : (int option, int) Hashtbl.Poly.t = Hashtbl.Poly.create ()

  (* [send_partial_solutions messenger_from messengers_to main_id from_id
     to_ids ...]: the bounds read off the sending side's candidate partial
     solutions in [cache] are sent as upper bounds to every side of
     [messengers_to] (the other side's runs: one, or the two primals of
     [alternation_depth_primal]), and, with [send_lower_bounds], as lower bounds
     back to the sender.  [to_ids] names the receivers in the trace only.
     A bound is a fact about the muCLP's predicates, not about a reduction, so
     it holds for every primal however its parity families were prioritised. *)
  let send_partial_solutions messenger_from messengers_to main_id from_id to_ids
      arity_map target_pvars history cache =
    Hash_set.iter cache
      ~f:(fun (sol, sol_before_red, violated_clauses, full_clauses, lbs_opt) ->
        Debug.print
        @@ lazy
             (sprintf "*** A new candidate partial solution from [%d]:\n%s"
                (Option.value_exn from_id)
                (Logic.str_of_term_subst Logic.ExtTerm.str_of sol));
        let interm =
          let fast_checked =
            Map.Poly.filter_mapi sol ~f:(fun ~key ~data ->
                match Map.Poly.find arity_map key with
                | None -> None
                | Some (dep_pvars, arity) ->
                    let (uni_params, lambda_params), upper_bound =
                      let params =
                        List.mapi ~f:(fun i (_, s) ->
                            (Ident.Tvar (sprintf "x%d" (i + 1)), s))
                        @@ fst @@ Logic.ExtTerm.let_lam data
                      in
                      ( List.split_n params (List.length params - arity),
                        Normalizer.normalize @@ Evaluator.simplify_neg
                        @@ Logic.ExtTerm.to_old_formula Map.Poly.empty
                             (Map.Poly.of_alist_exn params)
                             data
                        @@ List.map params ~f:(fst >> Logic.ExtTerm.mk_var) )
                    in
                    Debug.print
                    @@ lazy
                         (sprintf "*** fast partial solution checking for [%s]"
                         @@ Ident.name_of_tvar key);
                    if not (Hash_set.mem history (key, upper_bound)) then
                      (* ToDo: check if [is_qualified_partial_solution] is indeed sufficient for partial solution checking
                         [violated_clauses] may contain clauses that do not define [key] but such clauses will be ignored *)
                      if
                        not
                          (PCSP.Problem.is_qualified_partial_solution
                             ~print:Debug.print dep_pvars target_pvars
                             violated_clauses)
                      then (
                        Debug.print @@ lazy "no";
                        None)
                      else (
                        Debug.print @@ lazy "yes!";
                        Some (arity, (uni_params, lambda_params), upper_bound))
                    else (
                      Debug.print @@ lazy "yes!!";
                      Some (arity, (uni_params, lambda_params), upper_bound)))
          in
          Map.force_merge fast_checked
          @@
          match lbs_opt with
          | Some (senv, fenv, lbs) ->
              Debug.print
              @@ lazy "*** partial solution checking using lower bounds";
              let pvs =
                ClauseSet.partial_sols_of ~print:Debug.print
                  (Z3Smt.Z3interface.is_valid ~id:main_id fenv)
                  senv sol_before_red lbs full_clauses target_pvars
                  (Map.key_set fast_checked)
              in
              Map.Poly.filter_mapi sol ~f:(fun ~key ~data ->
                  if not @@ Set.mem pvs key then None
                  else
                    match Map.Poly.find arity_map key with
                    | None -> failwith "send_partial_solutions"
                    | Some (_dep_pvars, arity) ->
                        let (uni_params, lambda_params), upper_bound =
                          let params =
                            List.mapi ~f:(fun i (_, s) ->
                                (Ident.Tvar (sprintf "x%d" (i + 1)), s))
                            @@ fst @@ Logic.ExtTerm.let_lam data
                          in
                          ( List.split_n params (List.length params - arity),
                            Normalizer.normalize @@ Evaluator.simplify_neg
                            @@ Logic.ExtTerm.to_old_formula Map.Poly.empty
                                 (Map.Poly.of_alist_exn params)
                                 data
                            @@ List.map params ~f:(fst >> Logic.ExtTerm.mk_var)
                          )
                        in
                        Some (arity, (uni_params, lambda_params), upper_bound))
          | None -> Map.Poly.empty
        in
        (* A candidate's entry for an unknown the constraint solver's
           preprocessing removed (by resolution, or by fixing it to a bound) is
           not a value the solver checked: it is a definition recorded at the
           removal and read under the remaining unknowns' candidate values, and
           it was chosen to satisfy the removed unknown's clauses together with
           its CALLERS -- the occurrences it was resolved against -- not only
           with the unknowns it depends on.  The clauses the removal leaves
           behind mention the callers and the removed unknown's callees but no
           longer the removed unknown, so a violated one is not seen by the
           test above as touching the removed unknown's dependency set.  On a
           fixpoint problem whose greatest fixpoints [A5 = A3, A3 = false]
           were removed, a caller's wrong candidate made the recorded
           definition of [A5] read [true]; the test passed, the bound
           [A5 => false] reached the other side, and that side then refuted a
           valid problem.  So a target whose dependency set holds such an
           unknown is never sent: a bound is sound only when every unknown it
           depends on carries a value the candidate itself proposed and that
           the clauses defining it were checked against. *)
        let interm =
          let removed =
            Set.diff (Map.key_set sol) (Map.key_set sol_before_red)
          in
          if Set.is_empty removed then interm
          else
            Map.Poly.filter_keys interm ~f:(fun key ->
                match Map.Poly.find arity_map key with
                | None -> false
                | Some (dep_pvars, _) ->
                    not
                    @@ Set.exists removed ~f:(fun removed_pvar ->
                        Set.exists dep_pvars
                          ~f:(Ident.is_related_tvar removed_pvar)))
        in
        let bounds =
          Map.Poly.filter_mapi interm
            ~f:(fun
                ~key ~data:(arity, (uni_params, lambda_params), upper_bound) ->
              if Hash_set.mem history (key, upper_bound) then (
                Debug.print
                @@ lazy
                     (sprintf "the upper bound [%s] is not new"
                     @@ Formula.str_of
                     @@ Evaluator.simplify_neg upper_bound);
                None)
              else if
                Evaluator.is_valid
                  (Z3Smt.Z3interface.is_valid ~id:main_id @@ get_fenv ())
                  upper_bound
              then (
                Debug.print
                @@ lazy
                     (sprintf "the upper bound [%s] is trivial"
                     @@ Formula.str_of
                     @@ Evaluator.simplify_neg upper_bound);
                Hash_set.Poly.add history (key, upper_bound);
                None)
              else (
                Hash_set.Poly.add history (key, upper_bound);
                Debug.print
                @@ lazy
                     (sprintf "send %d -> %s : forall %s. %s (%s) => %s"
                        (Option.value_exn from_id)
                        (String.concat_map_list ~sep:"," to_ids
                           ~f:(fun id -> string_of_int (Option.value_exn id)))
                        (String.concat_map_list ~sep:"," uni_params
                           ~f:(fst >> Ident.name_of_tvar))
                        (Ident.name_of_tvar key)
                        (String.concat_map_list ~sep:"," lambda_params
                           ~f:(fst >> Ident.name_of_tvar))
                        (Formula.str_of upper_bound));
                let fresh_uni_params =
                  fst @@ refresh_sort_env_list ~prefix:None uni_params
                in
                let sub =
                  Map.Poly.of_alist_exn
                  @@ List.map2_exn uni_params fresh_uni_params
                       ~f:(fun (v1, _) (v2, _) -> (v1, Logic.ExtTerm.mk_var v2))
                in
                let lb_pred =
                  ( Map.Poly.of_alist_exn @@ fresh_uni_params,
                    Logic.ExtTerm.mk_lambda lambda_params
                    @@ Logic.ExtTerm.subst sub @@ Logic.ExtTerm.of_old_formula
                    @@ Evaluator.simplify_neg upper_bound )
                in
                let ub_pred =
                  ( Map.Poly.of_alist_exn @@ fresh_uni_params,
                    Logic.ExtTerm.mk_lambda lambda_params
                    @@ Logic.ExtTerm.subst sub
                    @@ Logic.ExtTerm.of_old_formula upper_bound )
                in
                Hashtbl.Poly.update send_records from_id ~f:(function
                  | None -> 1
                  | Some times -> times + 1);
                Some (arity, lb_pred, ub_pred)))
        in
        if Fn.non Map.Poly.is_empty bounds then (
          List.iter messengers_to ~f:(function
            | Some messenger_to ->
                Messenger.send_boardcast messenger_to main_id
                @@ PCSP.Problem.UpperBounds
                     (Map.Poly.map bounds ~f:(fun (ar, _, ub) -> (ar, ub)))
            | None -> ());
          match messenger_from with
          | Some messenger_from ->
              if config.send_lower_bounds then
                Messenger.send_boardcast messenger_from main_id
                @@ PCSP.Problem.LowerBounds
                     (Map.Poly.map bounds ~f:(fun (ar, lb, _) -> (ar, lb)))
              else ()
          | None -> ()));
    Hash_set.clear cache

  let id_mean = Some 0
  let id_primal = Some 1
  let id_dual = Some 2
  let id_primal_ad = Some 3

  let solve_primal_dual_exc ?erased_constants muclp =
    let open Or_error.Monad_infix in
    Hashtbl.Poly.set send_records ~key:id_primal ~data:0;
    Hashtbl.Poly.set send_records ~key:id_dual ~data:0;
    (* [solve] has already preprocessed [muclp]; this second preprocessing is
       not a no-op.  One run of the optimizer is one round of a shrinking
       fixpoint iteration (its inlining decides eligibility on the input's call
       graph, its validity replacement asks an outer binder before the inner
       ones are replaced, and the later steps leave predicates unreached and
       arguments irrelevant for the earlier ones), and on the POPL 2023 muCLP
       corpus the second round still changed half of the problems.  Removing it
       changes what the solver receives.  With COAR_OPTIMIZER_IDEMPOTENCE set,
       one stderr line says whether this round changed the problem
       (COAR_OPTIMIZER_IDEMPOTENCE_EXIT then exits, ..._DUMP=<prefix> writes
       both problems when they differ); unset, nothing is computed. *)
    let input = muclp in
    preprocess ~elim_forall:true ~elim_exists:true ~elim_pvar_args:true
      ?erased_constants muclp
    >>= fun muclp ->
    (* [second_round_growth_limit]: an enlarged second round is undone, which
       gives the solver the problem [solve] already optimized once -- the
       problem every other task receives *)
    let muclp =
      match config.second_round_growth_limit with
      | None -> muclp
      | Some factor ->
          let n_in = MuCLP.Problem.ast_size_of input
          and n_out = MuCLP.Problem.ast_size_of muclp in
          let keep = Float.(of_int n_out <= factor * of_int n_in) in
          Debug.print
          @@ lazy
               (sprintf "second optimizer round: %d -> %d formula nodes, %s"
                  n_in n_out
                  (if keep then "kept" else "undone"));
          if config.output_reduction_stats then (
            Out_channel.output_string stderr
              (sprintf "second-round: nodes_in=%d nodes_out=%d %s\n" n_in
                 n_out
                 (if keep then "kept" else "undone"));
            Out_channel.flush stderr);
          if keep then muclp else input
    in
    (if Option.is_some (Sys.getenv "COAR_OPTIMIZER_IDEMPOTENCE") then (
       let s_in = MuCLP.Problem.str_of input in
       let s_out = MuCLP.Problem.str_of muclp in
       let structural =
         try if Stdlib.( = ) input muclp then "same" else "differs"
         with Invalid_argument _ -> "incomparable"
       in
       Out_channel.eprintf
         "[optimizer-idempotence] %s structural=%s preds=%d->%d chars=%d->%d\n%!"
         (if String.equal s_in s_out then "same" else "differs")
         structural (List.length input.preds) (List.length muclp.preds)
         (String.length s_in) (String.length s_out);
       (match Sys.getenv "COAR_OPTIMIZER_IDEMPOTENCE_DUMP" with
       | Some prefix when not (String.equal s_in s_out) ->
           Out_channel.write_all (prefix ^ ".in") ~data:s_in;
           Out_channel.write_all (prefix ^ ".out") ~data:s_out
       | _ -> ());
       if Option.is_some (Sys.getenv "COAR_OPTIMIZER_IDEMPOTENCE_EXIT") then
         Common.ProcessExit.exit 0));
    match ground_decide ~id:id_mean muclp with
    | Some sol -> Ok (sol, 0, ground_evidence muclp)
    | None ->
    let arity_map =
      let open Reducer.DepGraph in
      let g = transitive_closure @@ gen_init_graph muclp.query muclp.preds in
      let reached_pvs pv =
        Set.Poly.map ~f:Ident.pvar_to_tvar
        @@ Set.add (Map.Poly.find_exn g pv).reachable pv
      in
      Debug.print @@ lazy ("dep_pvars_graph:\n" ^ Reducer.DepGraph.str_of g);
      Map.Poly.of_alist_exn
      @@ List.map muclp.preds ~f:(fun pred ->
          ( Ident.pvar_to_tvar pred.name,
            (reached_pvs pred.name, List.length pred.args) ))
    in
    let exc_info =
      match config.extra_partial_sols with
      | No_extra -> Some (Map.Poly.empty, Map.Poly.empty)
      | Random_examples { bound; size } ->
          Some
            ( Map.Poly.filter_mapi arity_map ~f:(fun ~key ~data:(_, arity) ->
                  if arity = 0 then None
                  else
                    Option.some @@ Set.Poly.singleton
                    @@ PCSP.Params.mk_random_info (Ident.uninterp key) bound
                         size),
              Map.Poly.map ~f:fst arity_map )
    in
    (* [target_pvars] must stay the raw muCLP predicate names: the pfwCSP
       names [U_p_]/[WF_p_] are matched against them by [Ident.is_related_tvar],
       which never matches an [uninterp]'d key -- a refactor that passed the
       [uninterp]'d names here left the primal/dual exchange sending nothing
       for two years.  [arity_map] is keyed by the pfwCSP
       names because candidate solutions are. *)
    let target_pvars = Map.key_set arity_map in
    let arity_map = Map.change_keys arity_map ~f:Ident.uninterp in
    let messenger_primal = Some (Messenger.create 2) in
    let messenger_dual = Some (Messenger.create 2) in
    let ad_primal = Option.is_some ad_primal_reduction in
    let messenger_primal_ad =
      if ad_primal then Some (Messenger.create 2) else None
    in
    let pool =
      Util.Task.setup_pool ~num_additional_domains:(if ad_primal then 3 else 2)
    in
    let task_primal =
      let id = id_primal in
      let messenger = messenger_primal in
      Util.Task.async pool (fun () ->
          Common.PhaseTime.with_phase "primal" @@ fun () ->
          check ~primal:true ~id ~messenger ~exc_info muclp)
    in
    let task_dual =
      let id = id_dual in
      let messenger = messenger_dual in
      Util.Task.async pool (fun () ->
          Common.PhaseTime.with_phase "dual" @@ fun () ->
          check ~primal:false ~id ~messenger ~exc_info
            (MuCLP.Util.get_dual muclp)
          >>= function
          | res, info, ev -> Ok (Verdict.flip res, info, ev))
    in
    (* the second primal of [alternation_depth_primal]; its answer ends the run
       only when it is valid or invalid (see [ad_decided] below) *)
    let task_primal_ad =
      if ad_primal then
        let id = id_primal_ad in
        let messenger = messenger_primal_ad in
        Some
          (Util.Task.async pool (fun () ->
               Common.PhaseTime.with_phase "primal-ad" @@ fun () ->
               check ~primal:true ~ad:true ~id ~messenger ~exc_info muclp))
      else None
    in
    (* [ad_decided ()]: the second primal's answer when it has one that decides
       the query.  An undecided answer ([Unknown], [Timeout], or the immediate
       [Unknown] of a primal that coincides with the loop-level one) and an
       error leave the run to the other two tasks: the second primal is an
       extra chance to refute or prove, never the only one, so its failure must
       not end a run the loop-level primal or the dual may still answer. *)
    let ad_ignored = ref false in
    let ad_decided () =
      if !ad_ignored then None
      else
        match task_primal_ad with
        | None -> None
        | Some task -> (
            match Atomic.get task with
            | None -> None
            | Some (Ok (Ok ((Verdict.Valid | Verdict.Invalid), _, _)) as sol) ->
                Some sol
            | Some res ->
                ad_ignored := true;
                Debug.print
                @@ lazy
                     (sprintf "the alternation-depth primal ended undecided%s"
                        (match res with
                        | Ok (Ok (v, _, _)) -> ": " ^ Verdict.str_of v
                        | Ok (Error e) -> ": " ^ Error.to_string_hum e
                        | Error (e, _) -> ": " ^ Exn.to_string e));
                None)
    in
    let sol_cache_primal = Hash_set.Poly.create () in
    let sol_cache_primal_ad = Hash_set.Poly.create () in
    let send_history_primal_ad = Hash_set.Poly.create () in
    let sol_cache_dual = Hash_set.Poly.create () in
    let send_history_primal = Hash_set.Poly.create () in
    let send_history_dual = Hash_set.Poly.create () in
    let witness_tried = Hash_set.Poly.create () in
    (* with [output_reduction_stats], one stderr line naming the task whose
       result ends the run: the line after the verdict does not say *)
    let answered side sol =
      if config.output_reduction_stats then (
        Out_channel.output_string stderr (sprintf "answered-by: %s\n" side);
        Out_channel.flush stderr);
      sol
    in
    (* the primal and the dual end the run as soon as one of them decides or
       fails; one that ends undecided ([Unknown], [Timeout]) leaves the run to
       the other, and the primal's undecided answer is the run's only when the
       dual has ended undecided too.  Taking whichever ended first lost the
       other side's answer whenever one side gave up early. *)
    let undecided = function
      | Some (Ok (Ok ((Verdict.Unknown | Verdict.Timeout), _, _))) -> true
      | _ -> false
    in
    let rec inner () =
      let primal = Atomic.get task_primal and dual = Atomic.get task_dual in
      match (primal, dual) with
      | Some sol, _ when not (undecided primal) -> answered "primal" sol
      | _, Some sol when not (undecided dual) -> answered "dual" sol
      | Some sol, Some _ -> answered "primal" sol
      | _ -> (
      match ad_decided () with
      | Some sol -> answered "primal-ad" sol
      | None ->
          receive_candidate_solutions messenger_primal id_mean
            sol_cache_primal;
          receive_candidate_solutions messenger_dual id_mean
            sol_cache_dual;
          receive_candidate_solutions messenger_primal_ad id_mean
            sol_cache_primal_ad;
          (* [dual_witness_refutation = Seed_primal_labeling]: each dual
             candidate's witness constants sent once to the primals'
             constraint solvers as seeds; under any other value nothing is
             computed or sent *)
          (match config.dual_witness_refutation with
          | Seed_primal_labeling _ ->
              Hash_set.iter sol_cache_dual ~f:(fun (sol, _, _, _, _) ->
                  match witness_seeds ~tried:witness_tried muclp sol with
                  | None -> ()
                  | Some seeds ->
                      List.iter [ messenger_primal; messenger_primal_ad ]
                        ~f:(function
                        | Some m ->
                            Messenger.send_boardcast m id_mean
                              (PCSP.Problem.GroundSeeds seeds)
                        | None -> ()))
          | No_witness_refutation | Witness_refutation _ -> ());
          (* [dual_witness_refutation]: each dual candidate's
             witness constants tried once on the primal *)
          let refuted =
            Hash_set.find_map sol_cache_dual
              ~f:(fun (sol, _, _, _, _) ->
                witness_refute ~tried:witness_tried muclp sol)
          in
          match refuted with
          | Some v ->
              answered "dual-witness" (Ok (Ok (v, 0, ground_evidence muclp)))
          | None ->
          if
            Hash_set.is_empty sol_cache_primal
            && Hash_set.is_empty sol_cache_dual
            && Hash_set.is_empty sol_cache_primal_ad
          then ignore @@ Core_unix.nanosleep 0.1
          else (
            send_partial_solutions messenger_primal [ messenger_dual ]
              id_mean id_primal [ id_dual ] arity_map target_pvars
              send_history_primal sol_cache_primal;
            send_partial_solutions messenger_primal_ad
              [ messenger_dual ] id_mean id_primal_ad [ id_dual ]
              arity_map target_pvars send_history_primal_ad
              sol_cache_primal_ad;
            send_partial_solutions messenger_dual
              (if ad_primal then [ messenger_primal; messenger_primal_ad ]
               else [ messenger_primal ])
              id_mean id_dual
              (if ad_primal then [ id_primal; id_primal_ad ]
               else [ id_primal ])
              arity_map target_pvars send_history_dual sol_cache_dual);
          inner ())
    in
    match inner () with
    | Ok sol -> sol
    | Error (err, bt) ->
        Or_error.of_exn
          ~backtrace:(`This (Stdlib.Printexc.raw_backtrace_to_string bt))
          err

  let resolve_auto muclp mode =
    if Stdlib.(mode = Config.Auto) then
      if MuCLP.Problem.has_only_forall muclp then (
        if MuCLP.Problem.has_only_nu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only forall-nu"
        else if MuCLP.Problem.has_only_mu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only forall-mu"
        else Debug.print @@ lazy "vvvv muCLP shape: only forall";
        Config.Prove)
      else if MuCLP.Problem.has_only_exists muclp then (
        if MuCLP.Problem.has_only_nu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only exists-nu"
        else if MuCLP.Problem.has_only_mu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only exists-mu"
        else Debug.print @@ lazy "vvvv muCLP shape: only exists";
        Config.Disprove)
      else (
        if MuCLP.Problem.has_only_nu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only nu"
        else if MuCLP.Problem.has_only_mu muclp then
          Debug.print @@ lazy "vvvv muCLP shape: only mu"
        else Debug.print @@ lazy "vvvv muCLP shape: otherwise";
        Config.Prove)
    else mode

  (* [solve_witnessed ?print_sol muclp]: [solve]'s answer, and the grounds of
     the side that decided it as a [Witness.t] ([None] unless
     [print_certificates] asks for them: without it nothing is collected and
     the run is the one it always was).  With [print_sol] the verdict line is
     printed, followed by the witness's lines. *)
  let solve_witnessed ?(print_sol = false) muclp =
    let open Or_error.Monad_infix in
    Debug.print @@ lazy "======== MuVal ========";
    Hashtbl.Poly.clear send_records;
    let received = muclp in
    let erased_constants = if want_certificate then Some (ref []) else None in
    let preprocess = preprocess ?erased_constants in
    (match resolve_auto muclp config.task with
      | Config.Auto -> failwith "not reachable here"
      | Config.Prove ->
          Debug.print @@ lazy "-=-=-=-= proving -=-=-=-=";
          preprocess ~elim_forall:true ~elim_exists:true ~elim_pvar_args:true
            muclp
          >>= fun muclp ->
          (match ground_decide muclp with
          | Some sol -> Ok (sol, 0, ground_evidence muclp)
          | None -> solve_primal ~messenger:None ~exc_info:None true muclp)
      | Config.Disprove ->
          Debug.print @@ lazy "-=-=-=-= disproving -=-=-=-=";
          preprocess ~elim_forall:true ~elim_exists:true ~elim_pvar_args:true
            muclp
          >>= fun muclp ->
          (match ground_decide muclp with
          | Some sol -> Ok (sol, 0, ground_evidence muclp)
          | None -> solve_dual ~messenger:None ~exc_info:None true muclp)
      | Config.Parallel { number_of_pairs } ->
          Debug.print @@ lazy "-=-=-=-= proving/disproving -=-=-=-=";
          Debug.set_id id_mean;
          preprocess ~id:id_mean ~elim_forall:true ~elim_exists:true
            ~elim_pvar_args:true muclp
          >>= fun muclp ->
          (match ground_decide ~id:id_mean muclp with
          | Some sol -> Ok (sol, 0, ground_evidence muclp)
          | None -> solve_primal_dual ~number_of_pairs muclp)
      | Config.ParallelExc ->
          Debug.print
          @@ lazy
               "-=-=-=-= proving/disproving exchange learned clauses -=-=-=-=";
          Debug.set_id id_mean;
          preprocess ~id:id_mean ~elim_forall:true ~elim_exists:true
            ~elim_pvar_args:true muclp
          >>= solve_primal_dual_exc ?erased_constants)
    >>= function
    | sol, info, ev ->
        Debug.print @@ lazy "=========================";
        let str_sol =
          MuCLP.Problem.(
            if config.output_yes_no then lts_str_of_solution
            else str_of_solution)
            sol
        in
        (* [info] is the CEGIS iteration count of the side that answered: in the
           parallel modes, whichever of the primal and dual tasks returned first,
           which this line does not name.  The two send counts are keyed by the
           sending side: partial solutions the primal sent, then the dual. *)
        let str_info =
          match
            ( Hashtbl.Poly.find send_records id_primal,
              Hashtbl.Poly.find send_records id_dual )
          with
          | Some primal_num_sent, Some dual_num_sent ->
              sprintf "%d,%d|%d" info primal_num_sent dual_num_sent
          | _ (*ToDo*) -> sprintf "%d" info
        in
        let witness =
          match ev with
          | None -> None
          | Some ev ->
              Common.PhaseTime.with_phase "muval-certificate" @@ fun () ->
              Option.some
              @@ Certificate.witness ~id:id_mean
                   ~print:(Debug.print ~id:id_mean)
                   ~ground_paths:
                     (match config.violation_sources with
                     | Config.Refutation_and_ground -> true
                     | Refutation_only -> false)
                   ?ground_budget:
                     (match config.ground_query_solve with
                     | MuCLP.GroundSolve.Config.Ground_solve { atom_budget } ->
                         Some atom_budget
                     | No_ground_solve -> None)
                   ~invalid:(match sol with Verdict.Invalid -> true | _ -> false)
                ~check_inductive:
                  (match config.print_certificates with
                  | Config.Checked_certificates -> true
                  | No_certificates | Unchecked_certificates -> false)
                ~erased:
                  (match erased_constants with Some r -> List.rev !r | None -> [])
                received ev
        in
        if print_sol then (
          print_endline
          @@
          if config.output_iteration then sprintf "%s,%s" str_sol str_info
          else sprintf "%s" str_sol;
          Option.iter witness ~f:(fun w ->
              List.iter (Witness.lines w) ~f:print_endline));
        Or_error.return (sol, str_info, info, witness)

  (* [solve_certified ?print_sol muclp]: [solve_witnessed] with the witness
     as its certificate lines (empty unless [print_certificates] asks) *)
  let solve_certified ?(print_sol = false) muclp =
    Or_error.map (solve_witnessed ~print_sol muclp)
      ~f:(fun (sol, str_info, info, w) ->
        (sol, str_info, info, Option.value_map w ~default:[] ~f:Witness.lines))

  let solve ?(print_sol = false) muclp =
    Or_error.map (solve_certified ~print_sol muclp)
      ~f:(fun (sol, str_info, info, _) -> (sol, str_info, info))

  let solve_pcsp ?(print_sol = false) pcsp =
    (* This backend reduces a predicate constraint problem to fixpoint logic,
       and a fixpoint problem has no place to carry a predicate's KIND: the
       reduction makes every predicate an ordinary least fixpoint.  Every kind
       but the ordinary one states an obligation the clauses do not -- a
       functional predicate must be total and deterministic, a well-founded one
       may not contain a cycle, a non-empty one may not be false everywhere --
       so dropping it answers a weaker question, and the answer comes back
       "satisfiable" on inputs the kind is what refutes.  Measured over the
       eighteen shipped `.clp` files that declare such a kind, the predicate
       constraint solver refutes four and this path answered satisfiable on
       seventeen of them, among them a three-line file whose two clauses force one
       functional predicate to take two values at the same argument.

       The problem constructor is shared -- the class name on the command line
       documents the input and nothing checks it -- so the compatibility table
       cannot refuse the pairing and the check has to happen here.  Naming the
       one kind that IS supported cannot go stale the way a list of kinds to
       refuse did: the kinds nobody thought of were accepted by such a list. *)
    PCSP.Problem.refuse_non_ord_kinds ~backend:"MuVal" pcsp;
    let (module Preprocessor : Preprocessor.PreprocessorType) =
      Preprocessor.(make @@ Config.make true config.verbose 4 4 true)
    in
    Debug.print
    @@ lazy "************* converting pfwCSP to muCLP ***************";
    Preprocessor.solve
      (fun ?oracle pcsp ->
        ignore oracle;
        let open Or_error.Monad_infix in
        solve ~print_sol:false (MuCLP.Util.of_chc ~print:Debug.print pcsp)
        >>= fun (sol, str_info, info) ->
        let sol =
          match sol with
          | Valid -> PCSP.Problem.Sat Map.Poly.empty (* ToDo *)
          | Invalid -> PCSP.Problem.Unsat None (* ToDo *)
          | Unknown -> PCSP.Problem.Unknown
          | Timeout -> PCSP.Problem.Timeout
        in
        if print_sol then
          print_endline
          @@
          if config.output_iteration then
            sprintf "%s,%s" (PCSP.Problem.str_of_solution sol) str_info
          else sprintf "%s" (PCSP.Problem.str_of_solution sol);
        Or_error.return
          ( sol,
            {
              PCSatCommon.State.num_cegis_iters = info;
              unsat_witness = None;
              kind_certificates = Map.Poly.empty;
            } ))
      pcsp

  let solve_interactive muclp =
    let pre_primal, muclp_primal =
      let bounds, phi, _ =
        if Formula.is_forall muclp.MuCLP.Problem.query then
          Formula.let_forall muclp.query
        else ([], muclp.query, Dummy)
      in
      let _, sorts, args, _ =
        try Atom.let_pvar_app @@ fst @@ Formula.let_atom phi
        with exn_ when not (Common.Timer.is_async exn_) ->
          failwith @@ "unsupported shape of query: " ^ Formula.str_of phi
      in
      let senv = Map.Poly.of_alist_exn @@ Logic.(of_old_sort_env_list bounds) in
      let pre =
        Formula.mk_atom @@ Atom.mk_pvar_app (Ident.Pvar "PrePrimal") sorts args
      in
      ( (senv, pre),
        MuCLP.Problem.make muclp.preds
        @@ Formula.(forall bounds @@ mk_imply pre phi) )
    in
    let pre_dual, muclp_dual =
      let muclp = MuCLP.Util.get_dual muclp in
      let bounds, phi, _ =
        if Formula.is_exists muclp.query then Formula.let_exists muclp.query
        else ([], muclp.query, Dummy)
      in
      let _, sorts, args, _ =
        Atom.let_pvar_app @@ fst @@ Formula.let_atom phi
      in
      let senv = Map.Poly.of_alist_exn @@ Logic.(of_old_sort_env_list bounds) in
      let pre =
        Formula.mk_atom @@ Atom.mk_pvar_app (Ident.Pvar "PreDual") sorts args
      in
      ( (senv, pre),
        MuCLP.Problem.make muclp.preds
        @@ Formula.(forall bounds @@ mk_imply pre phi) )
    in
    let ord_pvs_primal = Formula.pred_sort_env_of @@ snd pre_primal in
    let ord_pvs_dual = Formula.pred_sort_env_of @@ snd pre_dual in
    let pcsp_primal =
      let muclp_primal, unknowns =
        Qelim.elim_exists_in_preds
          (muclp_primal, (Map.Poly.empty, Map.Poly.empty))
      in
      PCSP.Problem.add_non_emptiness (Set.choose_exn ord_pvs_primal)
      @@ pfwcsp_of ~side:"primal" ~messenger:None ~exc_info:None
           (Kind.add_pred_env_set unknowns Kind.Ord ord_pvs_primal)
           muclp_primal
    in
    let pcsp_dual =
      let muclp_dual, unknowns =
        Qelim.elim_exists_in_preds (muclp_dual, (Map.Poly.empty, Map.Poly.empty))
      in
      PCSP.Problem.add_non_emptiness (Set.choose_exn ord_pvs_dual)
      @@ pfwcsp_of ~side:"dual" ~messenger:None ~exc_info:None
           (Kind.add_pred_env_set unknowns Kind.Ord ord_pvs_dual)
           muclp_dual
    in
    Debug.print
    @@ lazy
         (sprintf "pfwCSP for Primal Problem:\n%s\n"
         @@ PCSP.Problem.str_of pcsp_primal);
    Debug.print
    @@ lazy
         (sprintf "pfwCSP for Dual Problem:\n%s\n"
         @@ PCSP.Problem.str_of pcsp_dual);
    let open Or_error.Monad_infix in
    pcsp_solver ~primal:true
    (*ToDo:dual config is not used*) >>= fun (module PCSPSolver) ->
    Out_channel.output_string Out_channel.stdout "timeout in sec: ";
    Out_channel.flush Out_channel.stdout;
    let timeout =
      try Some (int_of_string @@ In_channel.input_line_exn In_channel.stdin)
      with exn_ when not (Common.Timer.is_async exn_) -> None
    in
    let rec refine primal dual unknown pos neg =
      Out_channel.output_string Out_channel.stdout
        "action (primal/dual/unknown/pos/neg/end): ";
      Out_channel.flush Out_channel.stdout;
      match In_channel.input_line_exn In_channel.stdin with
      | "primal" -> (
          let phi =
            let pre = Logic.ExtTerm.of_old_formula @@ snd pre_primal in
            Logic.BoolTerm.and_of
              [
                Logic.BoolTerm.imply_of pre
                @@ Logic.ExtTerm.of_old_formula
                @@ Formula.mk_and unknown (Formula.mk_neg neg);
                Logic.BoolTerm.imply_of (Logic.ExtTerm.of_old_formula pos) pre;
              ]
          in
          let pcsp =
            PCSP.Problem.add_formula (fst pre_primal, phi) pcsp_primal
          in
          let bpvs =
            Set.Poly.map ord_pvs_primal ~f:(fst >> Ident.pvar_to_tvar)
          in
          (match timeout with
            | None -> PCSPSolver.solve ~bpvs pcsp
            | Some tm ->
                Timer.enable_timeout tm Fn.id ignore
                  (fun () -> PCSPSolver.solve ~bpvs pcsp)
                  (fun _ res -> res)
                  (fun _ -> function
                    | Timer.Timeout -> Or_error.return (PCSP.Problem.Timeout, -1)
                    | e -> raise e))
          >>= function
          | PCSP.Problem.Sat sol, _ ->
              (*Out_channel.print_endline @@ CandSol.str_of sol;*)
              let phi =
                Z3Smt.Z3interface.simplify (get_fenv ()) ~id:None
                @@ Evaluator.simplify
                @@ Logic.ExtTerm.to_old_fml Map.Poly.empty (fst pre_primal)
                     Logic.(
                       Term.subst sol @@ ExtTerm.of_old_formula
                       @@ snd pre_primal)
              in
              let primal =
                Z3Smt.Z3interface.simplify ~id:None (get_fenv ())
                @@ Evaluator.simplify
                @@ Formula.or_of [ phi; primal ]
              in
              let unknown =
                Z3Smt.Z3interface.simplify ~id:None (get_fenv ())
                @@ Evaluator.simplify
                @@ Formula.and_of [ Formula.mk_neg phi; unknown ]
              in
              Out_channel.print_endline @@ Formula.str_of primal;
              if Z3Smt.Z3interface.is_sat ~id:None (get_fenv ()) unknown then
                refine primal dual unknown (Formula.mk_false ())
                  (Formula.mk_false ())
              else (
                Out_channel.print_endline "maximality is guaranteed";
                Or_error.return (Verdict.Unknown, -1) (*Dummy*))
          | Unsat _, _ ->
              if Formula.is_false pos && Formula.is_false neg then (
                Out_channel.print_endline
                  "maximally weak precondition for dual property:";
                Out_channel.print_endline @@ Formula.str_of unknown;
                Or_error.return (Verdict.Unknown, -1) (*Dummy*))
              else (
                Out_channel.print_endline
                  "the specified constraints for positive and negative \
                   examples are incorrect";
                refine primal dual unknown (Formula.mk_false ())
                  (Formula.mk_false ()))
          | (Unknown | Timeout), _ ->
              refine primal dual unknown (Formula.mk_false ())
                (Formula.mk_false ())
          | OutSpace _, _ -> assert false)
      | "dual" -> (
          let phi =
            let pre = Logic.ExtTerm.of_old_formula @@ snd pre_dual in
            Logic.BoolTerm.and_of
              [
                Logic.BoolTerm.imply_of pre
                @@ Logic.ExtTerm.of_old_formula
                @@ Formula.mk_and unknown (Formula.mk_neg neg);
                Logic.BoolTerm.imply_of (Logic.ExtTerm.of_old_formula pos) pre;
              ]
          in
          let pcsp = PCSP.Problem.add_formula (fst pre_dual, phi) pcsp_dual in
          let bpvs = Set.Poly.map ord_pvs_dual ~f:(fst >> Ident.pvar_to_tvar) in
          (match timeout with
            | None -> PCSPSolver.solve ~bpvs pcsp
            | Some tm ->
                Timer.enable_timeout tm Fn.id ignore
                  (fun () -> PCSPSolver.solve ~bpvs pcsp)
                  (fun _ res -> res)
                  (fun _ -> function
                    | Timer.Timeout -> Or_error.return (PCSP.Problem.Timeout, -1)
                    | e -> raise e))
          >>= function
          | PCSP.Problem.Sat sol, _ ->
              (*Out_channel.print_endline @@ Ast.CandSol.str_of sol;*)
              let phi =
                Z3Smt.Z3interface.simplify ~id:None (get_fenv ())
                @@ Evaluator.simplify
                @@ Logic.ExtTerm.to_old_fml Map.Poly.empty (fst pre_dual)
                     Logic.(
                       Term.subst sol @@ ExtTerm.of_old_formula @@ snd pre_dual)
              in
              let dual =
                Z3Smt.Z3interface.simplify ~id:None (get_fenv ())
                @@ Evaluator.simplify
                @@ Formula.or_of [ phi; dual ]
              in
              let unknown =
                Z3Smt.Z3interface.simplify ~id:None (get_fenv ())
                @@ Evaluator.simplify
                @@ Formula.and_of [ Formula.mk_neg phi; unknown ]
              in
              Out_channel.print_endline @@ Formula.str_of dual;
              if Z3Smt.Z3interface.is_sat ~id:None (get_fenv ()) unknown then
                refine primal dual unknown (Formula.mk_false ())
                  (Formula.mk_false ())
              else (
                Out_channel.print_endline "maximality is guaranteed";
                Or_error.return (Verdict.Unknown, -1) (*Dummy*))
          | Unsat _, _ ->
              if Formula.is_false pos && Formula.is_false neg then (
                Out_channel.print_endline
                  "maximally weak precondition for primal property:";
                Out_channel.print_endline @@ Formula.str_of unknown;
                Or_error.return (Verdict.Unknown, -1) (*Dummy*))
              else (
                Out_channel.print_endline
                  "the specified constraints for positive and negative \
                   examples are incorrect";
                refine primal dual unknown (Formula.mk_false ())
                  (Formula.mk_false ()))
          | (Unknown | Timeout), _ ->
              refine primal dual unknown (Formula.mk_false ())
                (Formula.mk_false ())
          | OutSpace _, _ -> assert false)
      | "pos" -> (
          Out_channel.output_string Out_channel.stdout "positive examples: ";
          Out_channel.flush Out_channel.stdout;
          match
            MuCLP.Util.query_from_string ~print:Debug.print
            @@ In_channel.(input_line_exn stdin)
          with
          | Ok phi -> refine primal dual unknown (Formula.mk_or pos phi) neg
          | Error msg -> failwith (Error.to_string_hum msg))
      | "neg" -> (
          Out_channel.output_string Out_channel.stdout "negative examples: ";
          Out_channel.flush Out_channel.stdout;
          match
            MuCLP.Util.query_from_string ~print:Debug.print
            @@ In_channel.(input_line_exn stdin)
          with
          | Ok phi -> refine primal dual unknown pos (Formula.mk_or neg phi)
          | Error msg -> failwith (Error.to_string_hum msg))
      | "unknown" ->
          Out_channel.print_endline @@ Formula.str_of unknown;
          refine primal dual unknown pos neg
      | "end" -> Or_error.return (Verdict.Unknown, -1) (*Dummy*)
      | _ -> refine primal dual unknown pos neg
    in
    refine (Formula.mk_false ()) (Formula.mk_false ()) (Formula.mk_true ())
      (Formula.mk_false ()) (Formula.mk_false ())

  (* the QFL / supermartingale solver is [QflSolver], re-exported here so
     that the top-level dispatcher reaches every MuVal entry point through
     this module *)
  module Qfl = QflSolver.Make (Cfg)

  let solve_qfl = Qfl.solve_qfl
end
