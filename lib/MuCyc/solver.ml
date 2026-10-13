open Core
open Common
open Common.Util
open Preprocessing
open Ast

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let pcsp_solver () (* ToDo *) =
    let open Or_error in
    ExtFile.unwrap config.pcsp_solver >>= fun cfg ->
    Ok
      PCSPSolver.(
        (module Solver.Make (struct
          let config = cfg
        end) : Solver.SolverType))

  let preprocess ~print problem =
    problem
    |> (if config.simplify then Problem.simplify else Fn.id)
    |> (if config.reduce then Problem.reduce else Fn.id)
    |> (if config.slice_forward then Problem.slice_forward else Fn.id)
    |> (if config.slice_backward then Problem.slice_backward else Fn.id)
    |> (if config.gen_lemmas_with_ai then Problem.gen_lemmas ~print else Fn.id)
    |>
    if config.gen_determ_conjs then Problem.gen_determ_conjs ~print ~config
    else Fn.id
  (*|> Problem.infer |> snd*)

  let solve_chc_shaped ~dtenv muclp =
    let open Or_error.Monad_infix in
    (Problem.of_muclp ~dtenv muclp
    |> preprocess ~print:Debug.print
    |>
    (* Instead of storing it inside Problem.t, pass it directly to ProofSearch here *)
    (* ToDo: Pass everything from pCSP to muCLP *)
    if true then ProofSearch.solve ~dtenv ~print:Debug.print ~config pcsp_solver
    else RelProofSearch.solve ~print:Debug.print ~config pcsp_solver)
    >>= fun (sol, _) -> Ok sol

  (* [ProofSearch] is a Spacer-style frame search whose frames over-approximate
     the least fixpoints; that is sound only for goals in which the predicates
     occur negatively (CHC shape: [body => false]).  A positive occurrence would
     be "proved" by the over-approximation, and greatest fixpoints are not
     supported at all.  [polarity_of_query]
     reports whether the universally closed query has free variables, negative
     occurrences and positive occurrences. *)
  let polarity_of_query muclp =
    let exi_senv =
      LogicOld.Term.pred_to_sort_env_map @@ MuCLP.Problem.penv_of muclp
    in
    let senv, query =
      LogicOld.Formula.rm_quant ~forall:true
      @@ LogicOld.Formula.aconv_tvar muclp.MuCLP.Problem.query
    in
    let seqs = Set.to_list @@ Sequent.of_formula exi_senv query in
    ( Set.is_empty senv,
      List.exists seqs ~f:(fun s -> Fn.non List.is_empty s.Sequent.left_atms),
      List.exists seqs ~f:(fun s -> Fn.non List.is_empty s.Sequent.right_atms)
    )

  let solve ?(print_sol = false) ?(dtenv = Map.Poly.empty) muclp =
    let open Or_error.Monad_infix in
    (* A muCLP predicate carries one of three fixpoint kinds, [Mu], [Nu] and
       [Fix].  This guard used to test [= Nu], so a [Fix] predicate slipped
       through and died deeper down in [ProofSearch.def_of], whose lookup
       matches [Some (Mu, _, _)] only, with the message "ProofSearch.def_of"
       and nothing else -- which is what every `-p ltsterm`/`ltsnsafe` run with
       this backend hit, because the LTS-to-muCLP reduction marks every
       non-cut-point location [Fix].  Refusing anything that is not [Mu] gives
       those runs the explanation this branch was written to give.
       ([Fix] means "not a genuine fixpoint": a non-cut-point location cannot
       lie on a cycle, so its least and greatest fixpoints coincide and the
       search could in principle treat it as [Mu].  That is a change to what
       this solver attempts, not to what it says, so it is left alone.) *)
    (if
       List.exists muclp.MuCLP.Problem.preds ~f:(fun (p : MuCLP.Pred.t) ->
           Stdlib.(p.kind <> LogicOld.Predicate.Mu))
     then
       Or_error.error_string
         "MuCyc supports only least-fixpoint (mu) predicates; use MuVal or \
          MuStrat for this problem"
     else
       let closed, has_neg, has_pos = polarity_of_query muclp in
       if not has_pos then solve_chc_shaped ~dtenv muclp
       else if closed && not has_neg then
         (* a closed query in which every predicate occurs positively:
            [lfp |= phi] iff the CHC [{defs} + {phi => false}] is unsat iff the
            query [not phi] is invalid, and [not phi] is CHC-shaped *)
         let muclp' =
           {
             muclp with
             query = LogicOld.Formula.mk_neg muclp.MuCLP.Problem.query;
           }
         in
         let _, _, has_pos' = polarity_of_query muclp' in
         if has_pos' then
           Or_error.error_string
             "MuCyc cannot handle this query: the negated query still has a \
              positive predicate occurrence; use MuVal or MuStrat"
         else (
           Debug.print
           @@ lazy
                "[MuCyc] the query has only positive predicate occurrences; \
                 solving the negated query and flipping the verdict";
           solve_chc_shaped ~dtenv muclp' >>= fun sol ->
           Ok
             (match sol with
             | Verdict.Valid -> Verdict.Invalid
             | Verdict.Invalid -> Verdict.Valid
             | sol -> sol))
       else
         Or_error.error_string
           "MuCyc cannot handle a query with a positive predicate occurrence \
            under a universal quantifier or mixed with negative occurrences \
            (its frame search is sound only for CHC-shaped goals); use MuVal \
            or MuStrat")
    >>= fun sol ->
    if print_sol then print_endline @@ Verdict.str_of sol;
    Ok sol

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
       all eighteen of them, among them a three-line file whose two clauses force one
       functional predicate to take two values at the same argument.

       The problem constructor is shared -- the class name on the command line
       documents the input and nothing checks it -- so the compatibility table
       cannot refuse the pairing and the check has to happen here.  Naming the
       one kind that IS supported cannot go stale the way a list of kinds to
       refuse did: the kinds nobody thought of were accepted by such a list. *)
    PCSP.Problem.refuse_non_ord_kinds ~backend:"MuCyc" pcsp;
    let (module Preprocessor : Preprocessor.PreprocessorType) =
      Preprocessor.(
        make @@ Config.make config.enable_pvar_elim config.verbose 4 4 true)
    in
    Debug.print
    @@ lazy "************* converting pfwCSP to muCLP ***************";
    Preprocessor.solve
      (fun ?oracle pcsp ->
        ignore oracle;
        let open Or_error.Monad_infix in
        solve ~print_sol:false
          ~dtenv:(PCSP.Problem.dtenv_of pcsp)
          (MuCLP.Util.of_chc ~print:Debug.print ~only_pos:false pcsp)
        >>= fun sol ->
        let sol =
          match sol with
          | Verdict.Valid -> PCSP.Problem.Sat Map.Poly.empty (* ToDo *)
          | Verdict.Invalid -> PCSP.Problem.Unsat None (*ToDo*)
          | Verdict.Unknown -> PCSP.Problem.Unknown
          | Verdict.Timeout -> PCSP.Problem.Timeout
        in
        if print_sol then print_endline (PCSP.Problem.str_of_solution sol);
        Or_error.return
          ( sol,
            {
              PCSatCommon.State.num_cegis_iters = -1 (*ToDo*);
              unsat_witness = None;
              kind_certificates = Map.Poly.empty;
            } ))
      pcsp

  let solve_smt ?(print_sol = false) g =
    Debug.print
    @@ lazy (sprintf "original input: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      let senv = Set.to_list @@ LogicOld.Formula.sort_env_of g in
      LogicOld.Formula.mk_exists_if_bounded senv g
    in
    Debug.print @@ lazy (sprintf "closed: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      LogicOld.Formula.move_quantifiers_to_front @@ Normalizer.normalize
      @@ Evaluator.simplify @@ LogicOld.Formula.elim_ite @@ Normalizer.normalize
      @@ LogicOld.Formula.elim_let
      @@ Normalizer.normalize_let ~rename:true
      @@ Typeinf.typeinf_formula
           ~print:(*Debug.print*) (fun _ -> ())
           ~default:(Some LogicOld.T_int.SInt (*ToDo*))
      @@ LogicOld.Formula.aconv_tvar g
    in
    Debug.print
    @@ lazy (sprintf "prenex normal form: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      Normalizer.normalize @@ Evaluator.simplify @@ LogicOld.Formula.rm_div_mod
      @@ LogicOld.Formula.elim_redundant_quantifiers g
    in
    Debug.print @@ lazy (sprintf "input: %s\n" (LogicOld.Formula.str_of g));
    let quantifiers, f = LogicOld.Formula.split_quantifiers g in
    let res =
      match Qsat.decide_theory quantifiers with
      | QBF ->
          let open Qsat.QSAT (Mbp.Boolean) in
          `Res (solve ~config ~print:Debug.print quantifiers f)
      | LRA ->
          let open Qsat.QSAT (Mbp.LRA) in
          `Res (solve ~config ~print:Debug.print quantifiers f)
      | LIA ->
          let open Qsat.QSAT (Mbp.LIA) in
          `Res (solve ~config ~print:Debug.print quantifiers f)
      | BV ->
          let open Qsat.QSAT (Mbp.BV) in
          `Res (solve ~config ~print:Debug.print quantifiers f)
    in
    let solution =
      match res with
      | `Res SAT -> SMT.Problem.Sat [ (*ToDo*) ]
      | `Res UNSAT -> SMT.Problem.Unsat
    in
    if print_sol then
      print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
    Ok solution
end
