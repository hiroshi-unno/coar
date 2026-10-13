open Core

module Config = struct
  type t =
    (* SAT solvers *)
    | Z3Sat of Z3Sat.Config.t  (** configuration of Z3Sat *)
    | MiniSat of MiniSat.Config.t  (** configuration of MiniSat *)
    | HOMCSat of HOMCSat.Config.t  (** configuration of HOMCSat *)
    (* SMT solvers *)
    | Z3Smt of Z3Smt.Config.t  (** configuration of Z3Smt *)
    (* HOMC solvers *)
    | TRecS of TRecS.Config.t  (** configuration of TRecS *)
    | HorSat2 of HorSat2.Config.t  (** configuration of HorSat2 *)
    (* CHC/pCSP/pfwCSP solvers *)
    | PCSat of PCSat.Config.t  (** configuration of PCSat *)
    | SPACER of SPACER.Config.t  (** configuration of SPACER *)
    | Hoice of Hoice.Config.t  (** configuration of Hoice *)
    (* CHC optimizers *)
    | OptPCSat of OptPCSat.Config.t
    (* PQE solvers *)
    | PolyQEnt of PolyQEnt.Config.t
    (* muCLP solvers *)
    | MuVal of MuVal.Config.t  (** configuration of MuVal *)
    | MuCyc of MuCyc.Config.t  (** configuration of MuCyc *)
    | MuStrat of MuStrat.Config.t  (** configuration of MuStrat *)
    (* Refinement Type Inference and Checking Tools for OCaml *)
    | RCaml of RCaml.Config.t  (** configuration of RCaml *)
    (* Verifier of effectful OCaml programs based on CPS transformation *)
    | EffCaml of EffCaml.Config.t  (** configuration of EffCaml *)
    (* printers *)
    | Printer of Printer.Config.t
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files =
    let open Or_error in
    function
    | Z3Sat cfg ->
        Z3Sat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Z3Sat cfg)
    | MiniSat cfg ->
        MiniSat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (MiniSat cfg)
    | HOMCSat cfg ->
        HOMCSat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (HOMCSat cfg)
    | Z3Smt cfg ->
        Z3Smt.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Z3Smt cfg)
    | TRecS cfg ->
        TRecS.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (TRecS cfg)
    | HorSat2 cfg ->
        HorSat2.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (HorSat2 cfg)
    | PCSat cfg ->
        PCSat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (PCSat cfg)
    | SPACER cfg ->
        SPACER.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (SPACER cfg)
    | Hoice cfg ->
        Hoice.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Hoice cfg)
    | OptPCSat cfg ->
        OptPCSat.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (OptPCSat cfg)
    | PolyQEnt cfg ->
        PolyQEnt.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (PolyQEnt cfg)
    | MuVal cfg ->
        MuVal.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (MuVal cfg)
    | MuCyc cfg ->
        MuCyc.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (MuCyc cfg)
    | MuStrat cfg ->
        MuStrat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (MuStrat cfg)
    | RCaml cfg ->
        RCaml.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (RCaml cfg)
    | EffCaml cfg ->
        EffCaml.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (EffCaml cfg)
    | Printer cfg ->
        Printer.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Printer cfg)

  let load_config filename =
    let open Or_error in
    try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
    match of_yojson raw_json with
    | Ok x -> instantiate_ext_files x
    | Error msg ->
        error_string
        @@ sprintf "Invalid Solver Configuration (%s): %s" filename msg
end

(* Which backends solve which problem class — the one table behind
   [main.ml]'s compatibility check.  It lists exactly the [Config.t]
   constructors the corresponding [solve_*] function below has an arm for,
   with one deliberate exception: [solve_lts]/[solve_plts] have a [PCSat] arm
   that calls [PCSP.Problem.of_lts], which refuses every input,
   so [PCSat] is not offered for LTS problems.
   Keep this table and the [solve_*] arms in step: a pair accepted here
   without an arm ends in [unimplemented], and an arm missing here is
   refused before it is reached. *)
let supports (cfg : Config.t) (p : ProblemKind.t) =
  let open ProblemKind in
  let sat_backends = function
    | Config.Z3Sat _ | MiniSat _ | HOMCSat _ | Printer _ -> true
    | _ -> false
  in
  let pcsp_backends = function
    | Config.PCSat _ | SPACER _ | Hoice _ | PolyQEnt _ | MuVal _ | MuCyc _
    | MuStrat _ | Printer _ ->
        true
    | _ -> false
  in
  let muclp_backends = function
    | Config.MuVal _ | MuCyc _ | MuStrat _ | Printer _ -> true
    | _ -> false
  in
  match p with
  | PSAT -> sat_backends cfg
  | PDQSAT | PHOSAT -> (
      match cfg with Config.HOMCSat _ | Printer _ -> true | _ -> false)
  | PSMT -> (
      match cfg with
      | Config.Z3Smt _ | MuCyc _ | MuStrat _ | Printer _ -> true
      | _ -> false)
  | PHOMC -> (
      match cfg with
      | Config.TRecS _ | HorSat2 _ | Printer _ -> true
      | _ -> false)
  | PSyGuS | PPCSP -> pcsp_backends cfg
  | PCHCMax -> ( match cfg with Config.OptPCSat _ -> true | _ -> false)
  | PMuCLP | PCLTL | PCCTL -> muclp_backends cfg
  | PMuCLPInter | PQFL | PPGCL | PSGCL | PLTSTermInter _ -> (
      match cfg with Config.MuVal _ -> true | _ -> false)
  | PLTSSafe _ | PLTSNSafe _ | PLTSTerm _ | PLTSNTerm _ | PLTSMuCal _
  | PLTSRel _ | PPLTSTerm | PPLTSNTerm ->
      muclp_backends cfg
  | POCaml -> (
      match cfg with Config.RCaml _ | EffCaml _ -> true | _ -> false)
  | PBTOR2 -> (
      match cfg with
      | Config.PCSat _ | SPACER _ | MuCyc _ | Printer _ -> true
      | _ -> false)

module type SolverType = sig
  val solve_sat : SAT.Problem.t -> unit Or_error.t
  val solve_dqsat : DQSAT.Problem.t -> unit Or_error.t
  val solve_hosat : HOSAT.Problem.t -> unit Or_error.t
  val solve_smt : SMT.Problem.t -> unit Or_error.t
  val solve_homc : HOMC.Problem.t -> unit Or_error.t

  val solve_sygus :
    ?filename:string option ->
    SyGuS.Problem.Make(SyGuS.Problem.ExtTerm).t ->
    unit Or_error.t

  val solve_pcsp :
    ?bpvs:Ast.Ident.tvar_set ->
    ?filename:string option ->
    ?require_context_model:bool ->
    PCSP.Problem.t ->
    unit Or_error.t

  val solve_chcopt :
    ?filename:string option -> CHCOpt.Problem.t -> unit Or_error.t

  val solve_muclp : MuCLP.Problem.t -> unit Or_error.t
  val solve_muclp_interactive : MuCLP.Problem.t -> unit Or_error.t
  val solve_qfl : QFL.Problem.t list -> unit Or_error.t

  val solve_lts :
    print:(string lazy_t -> unit) -> LTS.Problem.t -> unit Or_error.t

  val solve_lts_interactive :
    print:(string lazy_t -> unit) -> LTS.Problem.lts -> unit Or_error.t

  val solve_plts :
    print:(string lazy_t -> unit) -> PLTS.Problem.t -> unit Or_error.t

  val solve_ml : string -> unit Or_error.t
  val solve_btor2 :
    print:(string lazy_t -> unit) ->
    ?witness:BTOR2.Witness.target ->
    ?strict:bool ->
    BTOR2.Problem.ts ->
    unit Or_error.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  open Or_error.Monad_infix

  let solve_sat cnf =
    match Config.config with
    | Z3Sat cfg ->
        let module Z3Sat = Z3Sat.Solver.Make (struct
          let config = cfg
        end) in
        Z3Sat.solve ~print_sol:true cnf >>= fun _ -> Ok ()
    | MiniSat cfg ->
        let module MiniSat = MiniSat.Solver.Make (struct
          let config = cfg
        end) in
        MiniSat.solve ~print_sol:true cnf >>= fun _ -> Ok ()
    | HOMCSat cfg ->
        let module HOMCSat = HOMCSat.Solver.Make (struct
          let config = cfg
        end) in
        HOMCSat.solve ~print_sol:true cnf >>= fun _ -> Ok ()
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_sat cnf;
        Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_sat"

  let solve_dqsat dqsat =
    match Config.config with
    | HOMCSat cfg ->
        let module HOMCSat = HOMCSat.Solver.Make (struct
          let config = cfg
        end) in
        HOMCSat.solve_dqsat ~print_sol:true dqsat >>= fun _ -> Ok ()
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_dqsat dqsat;
        Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_dqsat"

  let solve_hosat hosat =
    match Config.config with
    | HOMCSat cfg ->
        let module HOMCSat = HOMCSat.Solver.Make (struct
          let config = cfg
        end) in
        HOMCSat.solve_hosat ~print_sol:true hosat >>= fun _ -> Ok ()
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_hosat hosat;
        Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_hosat"

  let solve_smt phi =
    match Config.config with
    | Z3Smt cfg ->
        let module Z3Smt = Z3Smt.Solver.Make (struct
          let config = cfg
        end) in
        Z3Smt.solve ~print_sol:true phi >>= fun _ -> Ok ()
    | MuCyc cfg ->
        let module MuCyc = MuCyc.Solver.Make (struct
          let config = cfg
        end) in
        MuCyc.solve_smt ~print_sol:true phi >>= fun _ -> Ok ()
    | MuStrat cfg ->
        let module MuStrat = MuStrat.Solver.Make (struct
          let config = cfg
        end) in
        MuStrat.solve_smt ~print_sol:true phi >>= fun _ -> Ok ()
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_smt phi;
        Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_smt"

  let solve_homc homc =
    match Config.config with
    | TRecS cfg ->
        let module TRecS = TRecS.Solver.Make (struct
          let config = cfg
        end) in
        TRecS.solve ~print_sol:true homc >>= fun _ -> Ok ()
    | HorSat2 cfg ->
        let module HorSat2 = HorSat2.Solver.Make (struct
          let config = cfg
        end) in
        HorSat2.solve ~print_sol:true homc >>= fun _ -> Ok ()
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_homc homc;
        Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_homc"

  (* The same treatment as [solve_pcsp] below: a backend that cannot carry a
     predicate kind refuses the problem with [NoTemplate], and a refusal is an
     unsupported input, reported as the ordinary verdict [unknown].  An [Int]- or
     [Real]-returning [synth-fun] is a function to synthesise and gets such a
     kind, so every backend but PCSat and PolyQEnt refuses it. *)
  let rec solve_sygus ?(filename = None) sygus =
    try solve_sygus_aux ~filename sygus
    with PCSP.Problem.NoTemplate reason ->
      print_endline "unknown";
      prerr_endline ("unsupported input: " ^ reason);
      Ok ()

  and solve_sygus_aux ~filename sygus =
    let pcsp = PCSP.Problem.of_sygus sygus in
    match Config.config with
    | PCSat cfg ->
        let module PCSat = PCSat.Solver.Make (struct
          let config = cfg
        end) in
        PCSat.solve ~filename ~print_sol:true pcsp >>= fun (solution, _) ->
        Out_channel.print_endline (PCSP.Problem.str_of_solution solution);
        Out_channel.flush stdout;
        Ok ()
    | SPACER cfg ->
        let module SPACER = SPACER.Solver.Make (struct
          let config = cfg
        end) in
        SPACER.solve pcsp >>= fun solution ->
        Out_channel.print_endline (PCSP.Problem.str_of_solution solution);
        Out_channel.flush stdout;
        Ok ()
    | Hoice cfg ->
        let module Hoice = Hoice.Solver.Make (struct
          let config = cfg
        end) in
        Hoice.solve pcsp >>= fun solution ->
        Out_channel.print_endline (PCSP.Problem.str_of_solution solution);
        Out_channel.flush stdout;
        Ok ()
    | MuVal cfg ->
        let module MuVal = MuVal.Solver.Make (struct
          let config = cfg
        end) in
        MuVal.solve_pcsp ~print_sol:true pcsp >>= fun (solution, _) ->
        Out_channel.print_endline (PCSP.Problem.str_of_solution solution);
        Out_channel.flush stdout;
        Ok ()
    | MuStrat cfg ->
        let module MuStrat = MuStrat.Solver.Make (struct
          let config = cfg
        end) in
        MuStrat.solve_pcsp ~print_sol:true pcsp >>= fun (solution, _) ->
        Out_channel.print_endline (PCSP.Problem.str_of_solution solution);
        Out_channel.flush stdout;
        Ok ()
    | MuCyc cfg ->
        let module MuCyc = MuCyc.Solver.Make (struct
          let config = cfg
        end) in
        MuCyc.solve_pcsp ~print_sol:true pcsp >>= fun _ -> Ok ()
    | PolyQEnt cfg ->
        let module PolyQEnt = PolyQEnt.Solver.Make (struct
          let config = cfg
        end) in
        PolyQEnt.solve ~print_sol:true pcsp >>= fun _ -> Ok ()
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_pcsp pcsp >>= fun _ -> Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_sygus"

  (* A backend that cannot carry this problem's predicate kinds refuses it, and a
     refusal is an UNSUPPORTED INPUT rather than an internal error: it is reported
     as the ordinary verdict [unknown], with the reason on the diagnostic stream.
     Delivered as an escaping exception instead, it would reach the user as a
     backtrace with nothing on the verdict stream, and a harness reads a non-zero
     exit with no verdict as the tool CRASHING, so a backend behaving correctly
     would be recorded as the one outcome a dispatch check exists to catch.  The constraint solver catches the same
     exception inside its own coordinator and answers the same way; this is that
     treatment for the backends that raise it at the entry the dispatcher calls. *)
  let rec solve_pcsp ?(bpvs = Set.Poly.empty) ?(filename = None)
      ?(require_context_model = false) pcsp =
    try
      (* SMT-LIB file contexts require a model of definitions AND assertions.
         Clause validity alone is vacuous for an inconsistent environment.
         Internal pCSP calls keep their per-background-structure semantics;
         the file entry explicitly requests this additional obligation.
         Check the full environment before any backend preprocessing/pruning.
         A body can constrain an unknown also constrained by a clause; checking
         definitions alone misses that contradiction if preprocessing drops the
         clause. Close each original clause's own universal environment, leaving
         definition-site globals free. Ordinary first-order satisfiability is
         only a necessary relaxation of kind/dependency/uniformity obligations,
         not a solution or a pruning certificate. *)
      let fenv = PCSP.Problem.fenv_of pcsp in
      let original_phis () =
        (* Conversion must use this problem's known signatures, even when an
           API caller restored the parser's process-global environment. Keep
           those signatures out of the original universal closure. *)
        let known_senv = Ast.Logic.of_old_sort_env_map
            (Map.Poly.map fenv ~f:(fun (formals,sret,_,_,_) ->
                 Ast.LogicOld.Sort.mk_fun (List.map formals ~f:snd @ [sret]))) in
        PCSP.Problem.formulas_of pcsp
        |> Set.to_list
        |> List.map ~f:(fun (uni_senv, phi) ->
            Ast.LogicOld.Formula.mk_forall_if_bounded
              (Map.Poly.to_alist @@ Ast.Logic.to_old_sort_env_map uni_senv)
              (Ast.Logic.ExtTerm.to_old_fml
                 (PCSP.Problem.senv_of pcsp)
                 (Map.Poly.merge known_senv uni_senv ~f:(fun ~key:_ -> function
                      | `Left sort | `Right sort -> Some sort
                      | `Both (_,sort) -> Some sort)) phi))
      in
      let total_context = lazy (Z3Smt.Z3interface.has_total_defining_context ~id:None fenv) in
      let context_has_globals =
        List.exists (Map.Poly.data fenv) ~f:(fun (params, _, body, _, _) ->
            let references = Set.union (Ast.LogicOld.Term.fvs_of body)
                (Set.Poly.filter_map (Ast.LogicOld.Term.fvar_apps_of body) ~f:(function
                   | Ast.LogicOld.Term.FunApp (Ast.LogicOld.FVar (var, _, _), _, _) -> Some var
                   | _ -> None)) in
            Set.exists references ~f:(fun var ->
                not (Map.Poly.mem fenv var)
                && not (List.exists params ~f:(fun (formal, _) -> Poly.(formal = var)))))
      in
      (* Over Boolean signatures, the full equation model supplies finite
         predicate tables. For a relation on the two Boolean states, WF is
         exactly the absence of the two self-loops and the two-state cycle.
         These conditions certify a joint witness, not just clause validity. *)
      let finite_boolean_constraints = lazy (
        if not (Z3Smt.Z3interface.supports_boolean_equations fenv) then None
        else
        let open Ast.LogicOld in
        let params = PCSP.Problem.params_of pcsp in
        let unknowns = Ast.Logic.to_old_sort_env_map (PCSP.Problem.senv_of pcsp) in
        let allowed var = Map.Poly.mem unknowns var || Map.Poly.mem fenv var in
        let rec boolean_signature = function
          | Sort.SArrow (arg, c) -> Term.is_bool_sort arg
              && Sort.is_pure_triple c && boolean_signature c.val_type
          | sort -> Term.is_bool_sort sort in
        let boolean_terms term =
          Set.for_all (Term.filtered_terms_of term ~f:(fun _ -> true))
            ~f:(fun term -> Term.is_bool_sort (Term.sort_of term)
                && match term with
                   | Term.FunApp (FVar (var, _, _), _, _) -> allowed var
                   | _ -> true) in
        let kinds = PCSP.Problem.kind_map_of pcsp in
        let kind_supported var = function
          | Ast.Kind.Ord -> true
          | Ast.Kind.WF -> (match Map.Poly.find unknowns var with
              | Some sort -> List.length (Sort.args_of sort) = 2
                  && boolean_signature sort
              | None -> false)
          | _ -> false in
        if Map.Poly.for_all unknowns ~f:boolean_signature
           && Map.Poly.for_alli kinds ~f:(fun ~key ~data -> kind_supported key data)
           && Map.Poly.is_empty params.dep_graph
           && Map.Poly.is_empty params.sol_space
           && Map.Poly.is_empty params.sol_for_eliminated
           && Map.Poly.is_empty params.sol_for_resolved
           && Map.Poly.is_empty params.partial_sol_targets
           && List.for_all (Map.Poly.data fenv) ~f:(fun (formals, _, body, _, _) ->
                boolean_terms body
                && Set.for_all (Term.fvs_of body) ~f:(fun var ->
                    allowed var || List.exists formals ~f:(fun (formal, _) -> Poly.(formal = var))))
           && List.for_all (original_phis ()) ~f:(fun phi ->
                Set.for_all (Formula.filtered_terms_of phi ~f:(fun _ -> true)) ~f:boolean_terms
                && Set.for_all (Formula.fvs_of phi) ~f:allowed)
        then Some (Map.Poly.to_alist kinds |> List.concat_map ~f:(fun (var,kind) ->
             match kind with
             | Ast.Kind.WF ->
                 let app x y = Formula.of_bool_term
                     (Term.mk_fsym_app (FVar (var,[T_bool.SBool;T_bool.SBool],T_bool.SBool))
                        [T_bool.make x;T_bool.make y]) in
                 [Formula.mk_neg (app false false); Formula.mk_neg (app true true);
                  Formula.mk_neg (Formula.and_of [app false true;app true false])]
             | _ -> []))
        else None)
      in
      let finite_constraints =
        if require_context_model then Lazy.force finite_boolean_constraints else None in
      let context_has_unknowns =
        let unknowns = PCSP.Problem.senv_of pcsp in
        List.exists (Map.Poly.data fenv) ~f:(fun (formals, _, body, _, _) ->
            let open Ast.LogicOld in
            let refs = Set.union (Term.fvs_of body)
                (Set.Poly.filter_map (Term.fvar_apps_of body) ~f:(function
                    | Term.FunApp (FVar (var, _, _), _, _) -> Some var
                    | _ -> None)) in
            Set.exists refs ~f:(fun var -> Map.Poly.mem unknowns var
                && not (List.exists formals ~f:(fun (formal, _) -> Poly.(formal = var))))) in
      let admission =
        if
          require_context_model
          && Z3Smt.Z3interface.supports_defining_equations fenv
        then
          Some
            (Z3Smt.Z3interface.check_sat_base ~timeout:(Some 5000)
               ~fresh_solver:true ~defining_equations:true ~id:None fenv
               (original_phis () @ Option.value finite_constraints ~default:[]))
        else if
          require_context_model
          && Z3Smt.Z3interface.supports_defining_equation_instances fenv
          && (try
                Z3Smt.Z3interface.refutes_defining_context_by_instances
                  ~phis:(original_phis ()) ~id:None fenv
              with exn when not (Common.Timer.is_async exn) -> false)
        then Some `Unsat
        else if require_context_model && not (Map.Poly.is_empty fenv) then
          (try
             match Z3Smt.Z3interface.defining_context_projection_model
                     ~id:None fenv (original_phis ()) with
             | Some _ -> None
             | None when Lazy.force total_context -> None
             | None -> Some (`Unknown "no verified known-function context model")
           with exn when not (Common.Timer.is_async exn) ->
             Some (`Unknown "known-function context model conversion refused"))
        else None
      in
      match admission with
      | Some `Unsat ->
          Common.ForkGuard.before_verdict ();
          print_endline "unsat";
          Ok ()
      | Some (`Unknown reason) ->
          Common.ForkGuard.before_verdict ();
          print_endline "unknown";
          prerr_endline ("known-function context check: " ^ reason);
          Ok ()
      | Some `Timeout ->
          Common.ForkGuard.before_verdict ();
          print_endline "unknown";
          prerr_endline "known-function context check: timeout";
          Ok ()
      | Some (`Sat _) when Option.is_some finite_constraints ->
          (* A joint model is not validity in every defining model. Over this
             Boolean fragment, totality gives unique known interpretations for
             each chosen predicate table. Otherwise the clauses must not read
             the potentially underdetermined known functions. *)
          let clauses_read_known = List.exists (original_phis ()) ~f:(fun phi ->
              not (Set.is_empty (Ast.LogicOld.Formula.filtered_terms_of phi ~f:(function
                  | Ast.LogicOld.Term.Var (var,_,_)
                  | Ast.LogicOld.Term.FunApp (Ast.LogicOld.FVar (var,_,_),_,_) ->
                      Map.Poly.mem fenv var
                  | _ -> false)))) in
          Common.ForkGuard.before_verdict ();
          if not clauses_read_known || Lazy.force total_context then
            print_endline "sat"
          else (
            print_endline "unknown";
            prerr_endline "joint context model does not certify every defining interpretation");
          Ok ()
      | None | Some (`Sat _) ->
          (* An ordinary model may choose globals that the backend's kinded or
             uniform witness cannot choose. Prevent vacuous validity for the
             actual witness by requiring a defining model for every background
             interpretation when known bodies depend on such globals. *)
          if require_context_model && context_has_unknowns then (
            Common.ForkGuard.before_verdict ();
            print_endline "unknown";
            prerr_endline "known-function context needs a joint admissible predicate model";
            Ok ())
          else if require_context_model && context_has_globals
             && not (Lazy.force total_context)
             && Option.is_none
                  (Z3Smt.Z3interface.defining_context_projection_model
                     ~id:None fenv [Ast.LogicOld.Formula.mk_true ()])
          then (
            Common.ForkGuard.before_verdict ();
            print_endline "unknown";
            prerr_endline "known-function context needs a model for every background interpretation";
            Ok ())
          else solve_pcsp_aux ~bpvs ~filename pcsp
    with PCSP.Problem.NoTemplate reason ->
      Common.ForkGuard.before_verdict ();
      print_endline "unknown";
      prerr_endline ("unsupported input: " ^ reason);
      Ok ()

  and solve_pcsp_aux ?(bpvs = Set.Poly.empty) ?(filename = None) pcsp =
    match Config.config with
    | PCSat cfg ->
        let module PCSat = PCSat.Solver.Make (struct
          let config = cfg
        end) in
        PCSat.solve ~bpvs ~filename ~print_sol:true ~solution_read:false pcsp
        >>= fun _ -> Ok ()
    | SPACER cfg ->
        let module SPACER = SPACER.Solver.Make (struct
          let config = cfg
        end) in
        SPACER.solve ~print_sol:true pcsp >>= fun _ -> Ok ()
    | Hoice cfg ->
        let module Hoice = Hoice.Solver.Make (struct
          let config = cfg
        end) in
        Hoice.solve ~print_sol:true pcsp >>= fun _ -> Ok ()
    | PolyQEnt cfg ->
        let module PolyQEnt = PolyQEnt.Solver.Make (struct
          let config = cfg
        end) in
        PolyQEnt.solve ~print_sol:true pcsp >>= fun _ -> Ok ()
    | MuVal cfg ->
        let module MuVal = MuVal.Solver.Make (struct
          let config = cfg
        end) in
        MuVal.solve_pcsp ~print_sol:true pcsp >>= fun _ -> Ok ()
    | MuCyc cfg ->
        let module MuCyc = MuCyc.Solver.Make (struct
          let config = cfg
        end) in
        MuCyc.solve_pcsp ~print_sol:true pcsp >>= fun _ -> Ok ()
    | MuStrat cfg ->
        let module MuStrat = MuStrat.Solver.Make (struct
          let config = cfg
        end) in
        MuStrat.solve_pcsp ~print_sol:true pcsp >>= fun _ -> Ok ()
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_pcsp pcsp >>= fun _ -> Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_pcsp"

  let solve_chcopt ?(filename = None) chcopt =
    match Config.config with
    | OptPCSat cfg ->
        let module OptPCSat = OptPCSat.Solver.Make (struct
          let config = cfg
        end) in
        OptPCSat.solve ~filename ~print_sol:true chcopt |> fun _ -> Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_chcopt"

  let solve_muclp muclp =
    match Config.config with
    | MuVal cfg ->
        let module MuVal = MuVal.Solver.Make (struct
          let config = cfg
        end) in
        MuVal.solve ~print_sol:true muclp >>= fun _ -> Ok ()
    | MuCyc cfg ->
        let module MuCyc = MuCyc.Solver.Make (struct
          let config = cfg
        end) in
        MuCyc.solve ~print_sol:true muclp >>= fun _ -> Ok ()
    | MuStrat cfg ->
        let module MuStrat = MuStrat.Solver.Make (struct
          let config = cfg
        end) in
        MuStrat.solve ~print_sol:true muclp >>= fun _ -> Ok ()
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_muclp muclp;
        Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_muclp"

  let solve_muclp_interactive muclp =
    match Config.config with
    | MuVal cfg ->
        let module MuVal = MuVal.Solver.Make (struct
          let config = cfg
        end) in
        MuVal.solve_interactive muclp >>= fun _ -> Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_muclp_interactive"

  let solve_qfl qfl =
    match Config.config with
    | MuVal cfg ->
        let module MuVal = MuVal.Solver.Make (struct
          let config = cfg
        end) in
        MuVal.solve_qfl ~print_sol:true qfl >>= fun _ -> Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_qfl"

  let solve_lts ~print (lts, mode) =
    match Config.config with
    | PCSat cfg ->
        let module PCSat = PCSat.Solver.Make (struct
          let config = cfg
        end) in
        PCSat.solve ~print_sol:false (PCSP.Problem.of_lts (lts, mode))
        >>= fun (sol, _) ->
        print_endline @@ PCSP.Problem.lts_str_of_solution sol;
        Ok ()
    | MuVal _ | MuCyc _ | MuStrat _ -> (
        let muclp =
          let lvs, cps, lts = LTS.Problem.analyze ~print lts in
          print @@ lazy "************* converting LTS to muCLP ***************";
          MuCLP.Util.of_lts ~print ~live_vars:(Some lvs) ~cut_points:(Some cps)
            (lts, mode)
        in
        match Config.config with
        | MuVal cfg ->
            let module MuVal = MuVal.Solver.Make (struct
              let config = cfg
            end) in
            MuVal.solve ~print_sol:false muclp >>= fun (solution, _, _) ->
            print_endline @@ Common.Verdict.lts_str_of solution;
            Ok ()
        | MuCyc cfg ->
            let module MuCyc = MuCyc.Solver.Make (struct
              let config = cfg
            end) in
            MuCyc.solve ~print_sol:false muclp >>= fun solution ->
            print_endline @@ Common.Verdict.lts_str_of solution;
            Ok ()
        | MuStrat cfg ->
            let module MuStrat = MuStrat.Solver.Make (struct
              let config = cfg
            end) in
            MuStrat.solve ~print_sol:false muclp >>= fun (solution, _, _) ->
            print_endline @@ Common.Verdict.lts_str_of solution;
            Ok ()
        | _ -> assert false)
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_lts (lts, mode);
        Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_lts"

  let solve_lts_interactive ~print lts =
    match Config.config with
    | MuVal cfg ->
        let muclp =
          let lvs, cps, lts = LTS.Problem.analyze ~print lts in
          print @@ lazy "************* converting LTS to muCLP ***************";
          MuCLP.Util.of_lts ~print ~live_vars:(Some lvs) ~cut_points:(Some cps)
            (lts, LTS.Problem.Term)
        in
        let module MuVal = MuVal.Solver.Make (struct
          let config = cfg
        end) in
        MuVal.solve_interactive muclp >>= fun _ -> Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_lts_interactive"

  let solve_plts ~print (plts, mode) =
    let lts = PLTS.Problem.lts_of ~print plts in
    let mode = PLTS.Problem.lts_mode_of mode in
    match Config.config with
    | PCSat cfg ->
        let module PCSat = PCSat.Solver.Make (struct
          let config = cfg
        end) in
        PCSat.solve ~print_sol:true (PCSP.Problem.of_lts (lts, mode))
        >>= fun _ -> Ok ()
    | MuVal _ | MuCyc _ | MuStrat _ -> (
        let muclp =
          let lvs, cps, lts = LTS.Problem.analyze ~print lts in
          print @@ lazy "************* converting LTS to muCLP ***************";
          MuCLP.Util.of_lts ~print ~live_vars:(Some lvs) ~cut_points:(Some cps)
            (lts, mode)
        in
        match Config.config with
        | MuVal cfg ->
            let module MuVal = MuVal.Solver.Make (struct
              let config = cfg
            end) in
            MuVal.solve ~print_sol:false muclp >>= fun (solution, _, _) ->
            print_endline @@ Common.Verdict.lts_str_of solution;
            Ok ()
        | MuCyc cfg ->
            let module MuCyc = MuCyc.Solver.Make (struct
              let config = cfg
            end) in
            MuCyc.solve ~print_sol:false muclp >>= fun solution ->
            print_endline @@ Common.Verdict.lts_str_of solution;
            Ok ()
        | MuStrat cfg ->
            let module MuStrat = MuStrat.Solver.Make (struct
              let config = cfg
            end) in
            MuStrat.solve ~print_sol:false muclp >>= fun (solution, _, _) ->
            print_endline @@ Common.Verdict.lts_str_of solution;
            Ok ()
        | _ -> assert false)
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_lts (lts, mode);
        Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_plts"

  let solve_ml filename =
    match Config.config with
    | RCaml cfg ->
        let module RCaml = RCaml.Solver.Make (struct
          let config = cfg
        end) in
        RCaml.solve_from_file ~print_sol:true filename >>= fun _ -> Ok ()
    | EffCaml cfg ->
        let module EffCaml = EffCaml.Solver.Make (struct
          let config = cfg
        end) in
        EffCaml.solve_from_file ~print_sol:true filename >>= fun _ -> Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_ml"

  (* A BTOR2 safety question is answered in the Hardware Model Checking Competition's form:
     one line, [sat] when a bad state is reachable and [unsat] when none is, which is the
     reverse of the constraint problem's answer, and nothing at all when the backend
     settles neither.  The Printer backend prints the constraint problem instead.

     With [witness], a [sat] answer also gets a counterexample in the BTOR2 witness format,
     and nothing about it is computed without: the witness is found by a bounded unrolling of
     its own after the backend has answered.  On standard output the witness replaces the
     [sat] line, since its own first line is [sat], so the output is one well-formed witness;
     into a file it goes beside the [sat] line.  A witness that cannot be built (an array
     value to write, no trace within the depth bound, a query the solver does not settle)
     is reported on standard error; the answer is then still [sat], unless [strict], where it
     is withheld: a competition penalises a [sat] whose certificate is missing more than no
     answer. *)
  let solve_btor2 ~print ?witness ?(strict = false) ts =
    match BTOR2.Chc.pcsp_of ~print ts with
    | exception BTOR2.Chc.Unsupported reason ->
        prerr_endline ("unsupported input: " ^ reason);
        exit 1
    | pcsp -> (
        let reachable () =
          match witness with
          | None -> print_endline "sat"
          | Some target -> (
              let written =
                Result.bind (BTOR2.Witness.build ts) ~f:(fun lines ->
                    match (target : BTOR2.Witness.target) with
                    | Stdout ->
                        List.iter lines ~f:print_endline;
                        Ok ()
                    | File path -> (
                        match Out_channel.write_lines path lines with
                        | () ->
                            print_endline "sat";
                            Ok ()
                        | exception Sys_error reason -> Error reason))
              in
              match written with
              | Ok () -> ()
              | Error reason ->
                  prerr_endline ("BTOR2: no witness: " ^ reason);
                  if not strict then print_endline "sat")
        in
        let answer = function
          | PCSP.Problem.Sat _ -> print_endline "unsat"
          | PCSP.Problem.Unsat _ -> reachable ()
          | PCSP.Problem.Unknown | OutSpace _ | Timeout -> ()
        in
        match Config.config with
        | PCSat cfg ->
            let module PCSat = PCSat.Solver.Make (struct
              let config = cfg
            end) in
            PCSat.solve ~print_sol:false pcsp >>= fun (sol, _) -> Ok (answer sol)
        | SPACER cfg ->
            let module SPACER = SPACER.Solver.Make (struct
              let config = cfg
            end) in
            SPACER.solve ~print_sol:false pcsp >>= fun sol -> Ok (answer sol)
        | MuCyc cfg ->
            let module MuCyc = MuCyc.Solver.Make (struct
              let config = cfg
            end) in
            MuCyc.solve_pcsp ~print_sol:false pcsp >>= fun (sol, _) -> Ok (answer sol)
        | Printer cfg ->
            let module Printer = Printer.Solver.Make (struct
              let config = cfg
            end) in
            Printer.print_pcsp pcsp
        | _ -> Or_error.unimplemented "Solver.solve_btor2")
end
