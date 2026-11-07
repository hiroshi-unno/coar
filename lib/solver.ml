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
    (* pfwCSP solver: one-shot templates for the predicate unknowns, PolyQEnt
       for their parameters *)
    | PolyQEntTempl of PolyQEntTempl.Config.t
    (* muCLP solvers *)
    | MuVal of MuVal.Config.t  (** configuration of MuVal *)
    | MuCyc of MuCyc.Config.t  (** configuration of MuCyc *)
    | MuStrat of MuStrat.Config.t  (** configuration of MuStrat *)
    (* Refinement Type Inference and Checking Tools for OCaml *)
    | RCaml of RCaml.Config.t  (** configuration of RCaml *)
    (* Verifier of effectful OCaml programs based on CPS transformation *)
    | EffCaml of EffCaml.Config.t  (** configuration of EffCaml *)
    (* HFL validity checkers built on RCaml's lambda-HFL modes *)
    | MuValHFL of MuValHFL.Config.t  (** configuration of MuValHFL *)
    | MuValQHFL of MuValQHFL.Config.t  (** configuration of MuValQHFL *)
    (* C programs to MuVal through Frama-C, clang 19 and LLVM IR *)
    | Athena of Athena.Config.t  (** configuration of Athena *)
    (* printers *)
    | Printer of Printer.Config.t
    (* several of the above, tried one after another *)
    | Portfolio of portfolio
  [@@deriving yojson]

  (* A sequential portfolio: the stages run one after another, each in a
     forked copy of this program, until one gives a definite answer
     (Common.SequentialPortfolio states what is printed).  Read from
     [["Portfolio", {"stages": [stage, ...]}]].  Invariants established by
     [instantiate_ext_files]: at least one stage, every stage's solver
     loaded (an [Instance]) and not itself a portfolio, every time limit
     finite and positive. *)
  and portfolio = { stages : stage list }

  and stage = {
    solver : t Common.Util.ext_file;
        (** the stage's configuration, a file of [config/solver/] or one
            written inline *)
    time_limit_s : float option; [@default None]
        (** seconds of wall-clock time the stage may run before it is stopped;
            [None]: until it ends, an outside limit on the whole run still
            applying *)
  }

  module type ConfigType = sig
    val config : t
  end

  let rec instantiate_ext_files cfg =
    let open Or_error in
    match cfg with
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
    | PolyQEntTempl cfg ->
        PolyQEntTempl.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (PolyQEntTempl cfg)
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
    | MuValHFL cfg ->
        MuValHFL.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (MuValHFL cfg)
    | MuValQHFL cfg ->
        MuValQHFL.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (MuValQHFL cfg)
    | Athena cfg ->
        Athena.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Athena cfg)
    | Printer cfg ->
        Printer.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Printer cfg)
    | Portfolio { stages } ->
        (if List.is_empty stages then
           error_string "a Portfolio configuration needs at least one stage"
         else return ())
        >>= fun () ->
        all
          (List.map stages ~f:(fun stage ->
               (match stage.time_limit_s with
               | Some t when not (Float.is_finite t && Float.(t > 0.)) ->
                   error_string
                   @@ sprintf "a Portfolio stage's time_limit_s must be \
                               finite and positive (got %g)" t
               | _ -> return ())
               >>= fun () ->
               (match stage.solver with
               | Common.Util.ExtFile.Filename filename -> load_config filename
               | Instance cfg -> instantiate_ext_files cfg)
               >>= function
               | Portfolio _ ->
                   error_string "a Portfolio stage cannot be a Portfolio"
               | cfg ->
                   return
                     { stage with solver = Common.Util.ExtFile.Instance cfg }))
        >>= fun stages -> Ok (Portfolio { stages })

  (* the one reader of a solver configuration file, a portfolio's stages
     included *)
  and load_config filename =
    let open Or_error in
    try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
    match of_yojson raw_json with
    | Ok x -> instantiate_ext_files x
    | Error msg ->
        error_string
        @@ sprintf "Invalid Solver Configuration (%s): %s" filename msg

  (* the backend's name, as a configuration file's first word writes it *)
  let name_of cfg =
    match to_yojson cfg with
    | `List (`String name :: _) -> name
    | _ -> "?"

  (* The configuration a plain run of this process solves with: [cfg]
     itself, unless it is a portfolio.  A portfolio's stages are run by
     Common.SequentialPortfolio, which forks a copy of this process per stage
     and returns only in a copy, with that copy's stage, so the caller goes on
     to solve as a plain run of the stage would; the calling process itself
     prints the portfolio's answer and ends there.  Assumes [cfg] is
     instantiated ([load_config]), and, for a portfolio, what
     SequentialPortfolio.run assumes: no domain spawned yet and nothing
     pending on standard output. *)
  let stage_to_run ~print = function
    | Portfolio { stages } ->
        let solver_of stage =
          Common.Util.ExtFile.unwrap_or_abort stage.solver
        in
        let i =
          Common.SequentialPortfolio.run ~print
            (List.map stages ~f:(fun stage ->
                 (name_of (solver_of stage), stage.time_limit_s)))
        in
        solver_of (List.nth_exn stages i)
    | cfg -> cfg
end

(* Which backends solve which problem class — the one table behind
   [main.ml]'s compatibility check.  It lists exactly the [Config.t]
   constructors the corresponding [solve_*] function below has an arm for,
   with one deliberate exception: [solve_lts]/[solve_plts] have a [PCSat] arm
   that calls [PCSP.Problem.of_lts], which refuses every input,
   so [PCSat] is not offered for LTS problems.  A second exception:
   [solve_sygus]/[solve_pcsp] have a [PolyQEnt] arm, but PolyQEnt decides
   polynomial quantified entailments, whose unknowns are real-valued template
   coefficients, and a predicate (or function) constraint problem is a
   different problem; it declined every such input with an [error:] line.
   Reaching that problem through PolyQEnt is a template reduction, which
   would be a configuration of the predicate constraint solver, not this
   backend, so [PolyQEnt] is offered for no class here and the pairing is
   refused up front; the arms are kept, though no command line reaches them.
   That reduction is [PolyQEntTempl], offered for [-p pcsp] only: it declines
   (answers [unknown]) every problem whose unknowns its templates do not cover.
   A third: [Portfolio] has no [solve_*] arm, since main.ml replaces it before
   selecting a solving arm by the stage a forked copy runs, separately for
   each SMT session check ([Config.stage_to_run]); it is offered what all
   its stages are offered.
   Keep this table and the [solve_*] arms in step: a pair accepted here
   without an arm ends in [unimplemented], and an arm missing here is
   refused before it is reached. *)
let rec supports (cfg : Config.t) (p : ProblemKind.t) =
  let open ProblemKind in
  let sat_backends = function
    | Config.Z3Sat _ | MiniSat _ | HOMCSat _ | Printer _ -> true
    | _ -> false
  in
  let pcsp_backends = function
    | Config.PCSat _ | SPACER _ | Hoice _ | MuVal _ | MuCyc _ | MuStrat _
    | Printer _ ->
        true
    | _ -> false
  in
  let muclp_backends = function
    | Config.MuVal _ | MuCyc _ | MuStrat _ | Printer _ -> true
    | _ -> false
  in
  match (cfg, p) with
  (* a portfolio takes what every one of its stages takes, so that whichever
     stage ends up answering was offered a pairing it supports *)
  | Config.Portfolio { stages }, _ ->
      (not (List.is_empty stages))
      && List.for_all stages ~f:(fun stage ->
             match stage.Config.solver with
             | Common.Util.ExtFile.Instance cfg -> supports cfg p
             | Filename _ -> false)
  | _, _ -> (
  match p with
  | PSAT -> sat_backends cfg
  | PDQSAT | PHOSAT -> (
      match cfg with Config.HOMCSat _ | Printer _ -> true | _ -> false)
  | PSMT -> (
      match cfg with
      | Config.Z3Smt _ | MuCyc _ | MuStrat _ | Printer _ -> true
      | _ -> false)
  (* TRecS and HorSat2 take only the HORS problems of [-p homc] and EffCaml
     both kinds; the command line refuses an EHMTT for TRecS or HorSat2 once
     the input is read, since the extension, which tells the two apart, is
     not known here *)
  | PHOMC -> (
      match cfg with
      | Config.TRecS _ | HorSat2 _ | EffCaml _ | Printer _ -> true
      | _ -> false)
  | PSyGuS -> pcsp_backends cfg
  | PPCSP -> (
      match cfg with Config.PolyQEntTempl _ -> true | _ -> pcsp_backends cfg)
  | PCHCMax -> ( match cfg with Config.OptPCSat _ -> true | _ -> false)
  | PMuCLP | PCLTL | PCCTL -> muclp_backends cfg
  | PMuCLPInter | PLTSTermInter _ -> (
      match cfg with Config.MuVal _ -> true | _ -> false)
  (* the printer prints the QFL problem the input reduces to, in the syntax
     of [-p qfl], solving nothing *)
  | PQFL | PPGCL | PSGCL -> (
      match cfg with Config.MuVal _ | Printer _ -> true | _ -> false)
  | PLTSSafe _ | PLTSNSafe _ | PLTSTerm _ | PLTSNTerm _ | PLTSBuchi _
  | PLTSExBuchi _ | PLTSMuCal _
  | PLTSRel _ | PPLTSTerm | PPLTSNTerm | PLLVMTerm _ ->
      muclp_backends cfg
  (* PCSat takes the safety problem only, whose predicates are all greatest
     fixpoints, and returns its solution, which the witness is built from *)
  | PLLVMSafe _ -> (
      muclp_backends cfg || match cfg with Config.PCSat _ -> true | _ -> false)
  | POCaml -> (
      match cfg with Config.RCaml _ | EffCaml _ -> true | _ -> false)
  (* MuVal reads an HES as a muCLP only at order 1 and refuses any other by
     name; the printer prints the HES in a dialect, as OCaml or as a muCLP *)
  | PHFL -> (
      match cfg with
      | Config.MuValHFL _ | MuVal _ | Printer _ -> true
      | _ -> false)
  | PQHFL -> (
      match cfg with Config.MuValQHFL _ | Printer _ -> true | _ -> false)
  (* Athena's route reads a C program its own way; the C frontend's MuVal
     configurations keep [-p cltl]/[-p cctl] *)
  | PCTerm | PCSafe | PCMemSafe | PCTermMemSafe | PCNoOverflow | PCMemCleanup
    -> (
      match cfg with Config.Athena _ -> true | _ -> false)
  | PBTOR2 -> (
      match cfg with
      | Config.PCSat _ | SPACER _ | MuCyc _ | Printer _ -> true
      | _ -> false)
  (* a type definition is translated, not solved: there is no question to
     answer, so only the printer takes it *)
  | PXMLType -> ( match cfg with Config.Printer _ -> true | _ -> false))

module type SolverType = sig
  val solve_sat : SAT.Problem.t -> unit Or_error.t
  val solve_dqsat : DQSAT.Problem.t -> unit Or_error.t
  val solve_hosat : HOSAT.Problem.t -> unit Or_error.t
  (* [threshold] is the file's [(set-info :threshold q)]; only MuCyc's
     probabilistic solvers read it, and every other backend ignores it *)
  val solve_smt : ?threshold:Q.t -> SMT.Problem.t -> unit Or_error.t
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

  val solve_muclp_lts :
    ?after_verdict:
      (Common.Verdict.t -> LLVMWitness.Certificate.t option -> unit) ->
    MuCLP.Problem.t ->
    unit Or_error.t
  (** a muCLP problem stated by a program frontend, answered in the LTS
      vocabulary ([YES]/[NO]/[MAYBE]) the competition wrappers read.
      [after_verdict] is called once the verdict line is printed, with the
      verdict and, from a backend that returns it, the evidence of the side
      that decided it, in the terms of the problem as given
      (LLVMWitness.Certificate: invariants and transitions for a YES, the
      path for a NO).  PCSat returns the invariants of a YES; MuVal, when
      its configuration asks for its certificate, the invariants and the
      checked rankings' transitions of a YES and the replayed path of a NO
      its primal (or ground decision) gave, and then writes its own
      certificate lines to standard error, not after the verdict. *)
  val solve_muclp_interactive : MuCLP.Problem.t -> unit Or_error.t
  val solve_qfl : ?header:string -> QFL.Problem.t list -> unit Or_error.t
  (** solved, or printed as [.qhes] by the printer after [header] as a
      comment *)

  val lts_division : unit -> LTS.Problem.division
  (** how the T2 reader reads [/] in a file with a [BUCHI] line, as the
      backend's configuration states it *)

  val solve_lts :
    print:(string lazy_t -> unit) -> LTS.Problem.t -> unit Or_error.t

  val solve_lts_interactive :
    print:(string lazy_t -> unit) -> LTS.Problem.lts -> unit Or_error.t

  val solve_plts :
    print:(string lazy_t -> unit) -> PLTS.Problem.t -> unit Or_error.t

  val solve_ml : string -> unit Or_error.t

  val solve_hfl : string -> unit Or_error.t
  (** an HES file or its OCaml representation, by its file name *)

  val solve_qhfl : string -> unit Or_error.t
  (** an OCaml file in an expectation mode, by its file name *)
  val solve_c :
    print:(string lazy_t -> unit) ->
    ?signed_overflow:Athena.Config.signed_overflow ->
    data_model:Athena.Pipeline.data_model ->
    property:Athena.Pipeline.property ->
    string ->
    unit Or_error.t
  (** a C program by Athena's route, answered in the LTS vocabulary
      ([YES]/[NO]/[MAYBE]) the competition wrappers read; termination of a
      memory-safe program answers [UNSAFE] for a reachable violation, which
      termCOMP scores as MAYBE but tells apart from a lack of answer.
      [signed_overflow], when given, replaces the configuration's reading of
      signed overflow (the command line's choice); a no-overflow question
      reads none, its answer being decided at the first overflow.  Notes on
      standard error, before solving: under [Arbitrary_value] that a NO or a
      violation may rest on a value chosen for an overflowing operation;
      under [Wraps] with [Mathematical] integers that they are read as
      [Wrapping]. *)
  val solve_btor2 :
    print:(string lazy_t -> unit) ->
    ?witness:BTOR2.Witness.target ->
    ?strict:bool ->
    BTOR2.Problem.ts ->
    unit Or_error.t

  val solve_xmltype : Grammar.RegTreeExpReader.defs -> unit Or_error.t
end

(* the solver configuration, under a name the functors below do not
   shadow with their parameter *)
module SolverConfig = Config

(* every [solve_*] but [solve_c], which solves with a configuration nested
   in its own and so instantiates this functor again *)
module Base (Config : Config.ConfigType) = struct
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

  let solve_smt ?threshold phi =
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
        MuCyc.solve_smt ~print_sol:true ?threshold phi >>= fun _ -> Ok ()
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
    | EffCaml cfg ->
        let module EffCaml = EffCaml.Solver.Make (struct
          let config = cfg
        end) in
        EffCaml.solve_homc ~print_sol:true homc >>= fun _ -> Ok ()
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
     kind, so every backend but PCSat refuses it. *)
  let rec solve_sygus ?(filename = None) sygus =
    try solve_sygus_aux ~filename sygus
    with PCSP.Problem.NoTemplate reason ->
      print_endline "unknown";
      prerr_endline ("unsupported input: " ^ reason);
      Ok ()

  (* One run prints one answer.  A backend called with [~print_sol:true]
     (PCSat, MuVal, MuStrat, MuCyc, PolyQEnt) prints its verdict
     itself, in its configured format -- under PCSat's SyGuS format the
     [define-fun]s alone -- so its arm prints nothing more; an arm that adds a
     line of its own calls its backend without [~print_sol].  Printing in both
     places put [sat,0] and then [sat] on stdout. *)
  and solve_sygus_aux ~filename sygus =
    let pcsp = PCSP.Problem.of_sygus sygus in
    match Config.config with
    | PCSat cfg ->
        let module PCSat = PCSat.Solver.Make (struct
          let config = cfg
        end) in
        let synth_funs, _, _ = sygus in
        PCSat.solve ~filename ~print_sol:true
          ~sygus_signature:(Map.Poly.map synth_funs ~f:fst)
          pcsp
        >>= fun _ -> Ok ()
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
        MuVal.solve_pcsp ~print_sol:true pcsp >>= fun _ -> Ok ()
    | MuStrat cfg ->
        let module MuStrat = MuStrat.Solver.Make (struct
          let config = cfg
        end) in
        MuStrat.solve_pcsp ~print_sol:true pcsp >>= fun _ -> Ok ()
    | MuCyc cfg ->
        let module MuCyc = MuCyc.Solver.Make (struct
          let config = cfg
        end) in
        (* the input's [(set-info :coar-lemma ...)] claims, which only the
           relational search reads, and only once it has proved them *)
        MuCyc.solve_pcsp ~print_sol:true
          ~lemmas:(Ast.LogicOld.get_pred_lemmas ())
          pcsp
        >>= fun _ -> Ok ()
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
      (* Definitions that no constraint reaches (directly or through another
         reached definition) are dropped, before anything below reads the
         environment, when they provably have a model in every structure
         whatever the rest denotes (constant interpretations making each of
         their equations valid): then the kept context is satisfiable exactly
         when the whole one is.  Without that proof they stay, since an unused
         definition can be inconsistent ([f x = f 0 + 1]) and make the file
         unsatisfiable.  Why: the check below cannot always find a model of an
         unused recursive definition over a global or a forall function, and
         then declined a file whose constraints never read it.  The printer
         exports the input as read, so it keeps every definition. *)
      let pcsp =
        if not require_context_model then pcsp
        else
          match Config.config with
          | Printer _ -> pcsp
          | _ ->
              let pruned = PCSP.Problem.prune_unreached_definitions pcsp in
              let kept = PCSP.Problem.fenv_of pruned in
              (* the walk follows applications only; a nullary definition
                 can also be read as a variable *)
              let read_by_constraints =
                PCSP.Problem.known_functions_read_by_constraints
                  ~applied_only:false (PCSP.Problem.fenv_of pcsp) pcsp
              in
              let read_as_variable var =
                Set.mem read_by_constraints var
                || List.exists (Map.Poly.data kept)
                     ~f:(fun (_, _, body, _, property) ->
                       Set.mem (Ast.LogicOld.Term.fvs_of body) var
                       || Set.mem (Ast.LogicOld.Formula.fvs_of property) var)
              in
              if phys_equal pruned pcsp then pcsp
              else if
                List.exists (Map.Poly.keys (PCSP.Problem.fenv_of pcsp))
                  ~f:(fun var -> (not (Map.Poly.mem kept var)) && read_as_variable var)
              then pcsp
              else if
                Z3Smt.Z3interface.omitted_definitions_have_constant_model
                  ~id:None ~kept:(PCSP.Problem.fenv_of pruned)
                  (PCSP.Problem.fenv_of pcsp)
              then (
                Common.PhaseTime.event_here "context/unreached-definitions-dropped";
                pruned)
              else pcsp
      in
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
      (* A term the theory leaves open (a division by zero, a selector on the
         wrong constructor) is a background value exactly as a global is:
         fixed in each model and different across models.  A body reading one
         can have a model in some backgrounds and none in others -- with
         [f x = ite (div 1 0 = 0) (f x + 1) 0], none where the division
         returns 0 -- and the satisfiable full-equation question below only
         says that some background admits one. *)
      let context_has_open_terms =
        List.exists (Map.Poly.data fenv) ~f:(fun (_, _, body, _, _) ->
            Ast.ClauseOld.has_theory_open_term body)
      in
      (* A defined symbol is chosen in each background together with the
         unknowns, so one background with no defining model refutes the file:
         [f x = ite (div 1 0 = 0) (f x + 1) 0] has none where [div 1 0 = 0].
         The certificate is a variable-free constraint on the open terms that
         is satisfiable by itself and unsatisfiable with the defining
         equations and the constraints; without one nothing is claimed. *)
      let open_term_refutation = lazy (
        context_has_open_terms
        && (try
              Z3Smt.Z3interface.refutes_defining_context_by_open_term_pins
                ~phis:(original_phis ()) ~id:None fenv
            with exn when not (Common.Timer.is_async exn) -> false))
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
      (* [context_admission.skip_whole_questions_when_total] (PCSat): a total
         context is left to the backend without the two admission questions
         that assert the whole problem; see the field *)
      let skip_whole_questions_when_total () =
        match Config.config with
        | PCSat c ->
            c.PCSat.Config.context_admission.skip_whole_questions_when_total
        | _ -> false
      in
      (* the configured collection rule before a new Z3 context applies to
         the admission's fresh contexts too, which are made before the
         solver that would otherwise install it *)
      (match Config.config with
      | PCSat c -> PCSat.Solver.set_z3_collector_policy c
      | _ -> ());
      (* [context_admission.full_major_every] (PCSat): see the field *)
      let admission_full_major_every =
        match Config.config with
        | PCSat c -> c.PCSat.Config.context_admission.full_major_every
        | _ -> 1
      in
      let admission =
        Common.PhaseTime.with_phase "context-admission" @@ fun () ->
        (if admission_full_major_every <= 1 then fun f -> f ()
         else
           Z3Smt.Z3interface.with_new_context_full_major_every
             admission_full_major_every)
        @@ fun () ->
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
          && (not
                (skip_whole_questions_when_total ()
                && Lazy.force total_context))
          && (try
                (* the scalar instances as before, then, where they refute
                   nothing and the context is not certified total, instances
                   over every first-order signature (datatypes, bit-vectors,
                   arrays, sequences, declared sorts), each a consequence of
                   the definitions.  A total context has a defining model in
                   every structure, so it is left to the backend, and no
                   datatype input whose only definitions are the generated
                   sizes is asked the extra question. *)
                (Z3Smt.Z3interface.supports_defining_equation_instances fenv
                 && Common.PhaseTime.with_phase "scalar-instances" (fun () ->
                        Z3Smt.Z3interface.refutes_defining_context_by_instances
                          ~phis:(original_phis ()) ~id:None fenv))
                || (not (Lazy.force total_context))
                   && Common.PhaseTime.with_phase "first-order-instances" (fun () ->
                          Z3Smt.Z3interface
                          .refutes_defining_context_by_first_order_instances
                            ~phis:(original_phis ()) ~id:None fenv)
              with exn when not (Common.Timer.is_async exn) -> false)
        then Some `Unsat
        else if
          require_context_model
          && skip_whole_questions_when_total ()
          && Lazy.force total_context
        then None
        else if require_context_model && not (Map.Poly.is_empty fenv) then
          (try
             match
               Common.PhaseTime.with_phase "projection-model" (fun () ->
                   Z3Smt.Z3interface.defining_context_projection_model
                     ~id:None fenv (original_phis ()))
             with
             | Some _ -> None
             | None when Lazy.force total_context -> None
             | None
               when Option.is_some
                      (Z3Smt.Z3interface.defining_context_projection_model_over_total
                         ~id:None fenv (original_phis ())) ->
                 (* a total sub-context (on a datatype input, at least the
                    generated sizes) kept as defined, candidates for the rest *)
                 None
             | None when Lazy.force open_term_refutation -> Some `Unsat
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
             interpretation when known bodies depend on such globals or on
             terms the theory leaves open.  A background with no defining model
             is one the problem must still be satisfied in (a defined symbol is
             chosen per background with the unknowns), so where the context
             reads open terms, a background whose pinned open-term values admit
             no defining model refutes it; otherwise the answer is declined,
             which is sound but incomplete. *)
          if require_context_model && context_has_unknowns then (
            let refuted = Lazy.force open_term_refutation in
            Common.ForkGuard.before_verdict ();
            if refuted then print_endline "unsat"
            else (
              print_endline "unknown";
              prerr_endline "known-function context needs a joint admissible predicate model");
            Ok ())
          else if require_context_model
             && (context_has_globals || context_has_open_terms)
             && not (Lazy.force total_context)
             && Option.is_none
                  (Z3Smt.Z3interface.defining_context_projection_model
                     ~id:None fenv [Ast.LogicOld.Formula.mk_true ()])
             && Option.is_none
                  (Z3Smt.Z3interface.defining_context_projection_model_over_total
                     ~id:None fenv [Ast.LogicOld.Formula.mk_true ()])
          then (
            let refuted = Lazy.force open_term_refutation in
            Common.ForkGuard.before_verdict ();
            if refuted then print_endline "unsat"
            else (
              print_endline "unknown";
              prerr_endline "known-function context needs a model for every background interpretation");
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
    | PolyQEntTempl cfg ->
        let module PolyQEntTempl = PolyQEntTempl.Solver.Make (struct
          let config = cfg
        end) in
        PolyQEntTempl.solve ~print_sol:true pcsp >>= fun _ -> Ok ()
    | MuVal cfg ->
        let module MuVal = MuVal.Solver.Make (struct
          let config = cfg
        end) in
        MuVal.solve_pcsp ~print_sol:true pcsp >>= fun _ -> Ok ()
    | MuCyc cfg ->
        let module MuCyc = MuCyc.Solver.Make (struct
          let config = cfg
        end) in
        (* the input's [(set-info :coar-lemma ...)] claims, which only the
           relational search reads, and only once it has proved them *)
        MuCyc.solve_pcsp ~print_sol:true
          ~lemmas:(Ast.LogicOld.get_pred_lemmas ())
          pcsp
        >>= fun _ -> Ok ()
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

  (* A muCLP problem whose predicates are all greatest fixpoints (or [Fix],
     read as greatest) and whose quantifiers are all universal, as a pCSP: each
     predicate is an unknown [U_<name>_] constrained by [U(x) => body], and
     the query is a goal.  A solution of the pCSP is a post-fixpoint below the
     greatest one, so it proves the query, and each unknown's solution holds of
     every state the predicate is applied to.  The problem is simplified, as
     MuVal does first (which also puts a quantifier under an implication into
     a position the reduction reads), but not optimised, so every predicate
     keeps its name and its parameters. *)
  let pcsp_of_nu_muclp (muclp : MuCLP.Problem.t) =
    let muclp = MuCLP.Problem.simplify muclp in
    if
      List.exists muclp.preds ~f:(fun p ->
          Stdlib.( = ) p.MuCLP.Pred.kind Ast.LogicOld.Predicate.Mu)
    then
      Or_error.error_string
        "PCSat answers a muCLP problem only when it has no least fixpoint"
    else if not (MuCLP.Problem.has_only_forall muclp) then
      Or_error.error_string
        "PCSat answers a muCLP problem only when it has no existential \
         quantifier"
    else
      let module Reducer = MuCLP.Reducer.Make (struct
        let config =
          MuCLP.Reducer.Config.
            {
              verbose = false;
              use_dwf = false;
              reduction =
                Wf_reduction
                  {
                    restrict_ranking_to_cycles = true;
                    record_on_head = false;
                    one_relation_per_block = false;
                  };
            }
      end) in
      let muclp' =
        MuCLP.Problem.complete_psort Map.Poly.empty
        @@ MuCLP.Problem.complete_tsort
        @@ MuCLP.Problem.aconv_tvar muclp
      in
      Ok
        (fst
           (Reducer.f ~exchange:false ~messenger:None muclp'
              (Map.Poly.empty, Map.Poly.empty)))

  (* The solution of each predicate of [muclp] in a pCSP solution of
     [pcsp_of_nu_muclp muclp], over the predicate's own parameters (the
     unknown's are renamed by position).  A predicate the solution does not
     hold, or holds at another arity, is left out. *)
  let muclp_solution_of (muclp : MuCLP.Problem.t) sub =
    Map.Poly.of_alist_exn
    @@ List.filter_map muclp.preds ~f:(fun (pred : MuCLP.Pred.t) ->
        let key = Ast.Ident.pvar_to_tvar (Ast.Ident.uninterp_pvar pred.name) in
        Option.bind (Map.Poly.find sub key) ~f:(fun data ->
            let args, term = Ast.Logic.ExtTerm.let_lam data in
            match List.zip args pred.args with
            | Unequal_lengths -> None
            | Ok pairs ->
                let phi =
                  Ast.Logic.ExtTerm.to_old_formula Map.Poly.empty
                    (Map.Poly.of_alist_exn args) term []
                in
                Some
                  ( pred.name,
                    Ast.LogicOld.Formula.rename
                      (Map.Poly.of_alist_exn
                      @@ List.map pairs ~f:(fun ((v, _), (x, _)) -> (v, x)))
                      phi )))

  (* The evidence of [Witness w], MuVal's grounds for [verdict], in the form
     a correctness or violation witness is built from.  Assumes [w] is about
     the problem MuVal received (its names and parameters), as MuVal's
     witness always is.  Guarantees:
     - for a valid verdict, [Holds] with every invariant [w] holds and, for
       each least-fixpoint predicate whose ranking's decrease Z3 checked on
       every return, that ranking's transition relation, which is over the
       parameters and their earlier-visit copies named as
       [LLVMWitness.Certificate.prev_name] names them;
     - for an invalid verdict with a replayed path, [Fails] with the path's
       steps in execution order (the refutation tree's preorder), each with
       every parameter's value and the bindings met from it to the next step
       (the query's before the first step), and with the step whose body is
       falsified at the end as [violated_in]; with a replayed lasso, [Cycles] with the
       steps before the cycle's first step as the stem and the rest as the
       cycle, the bindings as for [Fails]; with a checked recurrent set,
       [Cycles] whose stem ends at the loop head in a state of the set (that
       last step with no bindings), with the set as [recurrent]; with a
       cycle head only, [Cycles] whose stem is that loop head without values
       and whose cycle is empty;
     - [None] otherwise (an invalid verdict the dual or the ground decision
       gave without a path, an unknown, a timeout).
     Nothing is added that [w] does not hold, so a predicate left out only
     weakens the witness. *)
  let muval_witness_lines = MuVal.Witness.lines

  let certificate_of_muval_witness verdict (w : MuVal.Witness.t) =
    match (verdict : Common.Verdict.t) with
    | Valid ->
        let transitions =
          Map.Poly.of_alist_reduce ~f:(fun first _ -> first)
          @@ List.filter_map w.entries ~f:(function
            | MuVal.Witness.Ranking
                { rname; transition; rstatus = Direct_returns_checked; _ } ->
                Some (rname, transition)
            | _ -> None)
        in
        Some
          (LLVMWitness.Certificate.Holds
             { invariants = w.invariants; transitions })
    | Invalid -> (
        let pairs =
          List.map ~f:(fun (b : MuVal.Witness.binding) -> (b.var, b.value))
        in
        (* the steps of [v] with their bindings, each up to the next step *)
        let steps_of (v : MuVal.Witness.violation) =
          let binds = MuVal.Witness.binds_by_step v in
          List.map v.steps ~f:(fun (step : MuVal.Witness.step) ->
              LLVMWitness.Certificate.
                {
                  pred = step.pred;
                  args = pairs step.args;
                  binds = pairs binds.(step.index);
                  parent = step.parent;
                })
        in
        match w.violation with
        | Some ({ cycle_from = None; _ } as v) ->
            Some
              (LLVMWitness.Certificate.Fails
                 {
                   path = steps_of v;
                   violated_in =
                     Option.map (List.nth v.steps v.error.estep)
                       ~f:(fun (s : MuVal.Witness.step) -> s.pred);
                 })
        | Some ({ cycle_from = Some k; _ } as v) ->
            let stem, cycle =
              List.partition_tf (List.zip_exn v.steps (steps_of v))
                ~f:(fun ((s : MuVal.Witness.step), _) -> s.index < k)
            in
            Some
              (LLVMWitness.Certificate.Cycles
                 {
                   stem = List.map stem ~f:snd;
                   cycle = List.map cycle ~f:snd;
                   recurrent = None;
                 })
        | None ->
            List.find_map w.entries ~f:(function
              | MuVal.Witness.Recurrent { head; set; stem; entry; _ } ->
                  Some
                    (LLVMWitness.Certificate.Cycles
                       {
                         stem =
                           steps_of stem
                           @ [ { pred = head; args = pairs entry; binds = []; parent = None } ];
                         cycle = [];
                         recurrent = Some (head, set);
                       })
              | MuVal.Witness.Cycle_head { head; _ } ->
                  Some
                    (LLVMWitness.Certificate.Cycles
                       {
                         stem = [ { pred = head; args = []; binds = []; parent = None } ];
                         cycle = [];
                         recurrent = None;
                       })
              | _ -> None))
    | _ -> None

  let solve_muclp_lts ?after_verdict muclp =
    let hooked = Option.is_some after_verdict in
    let after_verdict = Option.value after_verdict ~default:(fun _ _ -> ()) in
    let answer verdict solution =
      print_endline @@ Common.Verdict.lts_str_of verdict;
      after_verdict verdict solution;
      Ok ()
    in
    match Config.config with
    | MuVal cfg ->
        let module MuVal = MuVal.Solver.Make (struct
          let config = cfg
        end) in
        (* With a caller's [after_verdict] the caller writes what follows the
           verdict, so MuVal's own lines (empty unless the configuration asks
           for its certificate) go to standard error; without one they follow
           the verdict on standard output. *)
        MuVal.solve_witnessed ~print_sol:false muclp
        >>= fun (solution, _, _, witness) ->
        let lines =
          Option.value_map witness ~default:[] ~f:muval_witness_lines
        in
        print_endline @@ Common.Verdict.lts_str_of solution;
        if hooked then (
          List.iter lines ~f:prerr_endline;
          after_verdict solution
            (Option.bind witness ~f:(certificate_of_muval_witness solution)))
        else List.iter lines ~f:print_endline;
        Ok ()
    | MuCyc cfg ->
        let module MuCyc = MuCyc.Solver.Make (struct
          let config = cfg
        end) in
        MuCyc.solve ~print_sol:false muclp >>= fun solution ->
        answer solution None
    | MuStrat cfg ->
        let module MuStrat = MuStrat.Solver.Make (struct
          let config = cfg
        end) in
        MuStrat.solve ~print_sol:false muclp >>= fun (solution, _, _) ->
        answer solution None
    | PCSat cfg -> (
        let module PCSat = PCSat.Solver.Make (struct
          let config = cfg
        end) in
        pcsp_of_nu_muclp muclp >>= fun pcsp ->
        PCSat.solve ~print_sol:false pcsp >>= fun (solution, _) ->
        match solution with
        | PCSP.Problem.Sat sub ->
            answer Common.Verdict.Valid
              (Some
                 (LLVMWitness.Certificate.of_invariants
                    (muclp_solution_of muclp sub)))
        | Unsat _ -> answer Common.Verdict.Invalid None
        | Timeout -> answer Common.Verdict.Timeout None
        | Unknown | OutSpace _ -> answer Common.Verdict.Unknown None)
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_muclp muclp;
        Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_muclp_lts"

  let solve_muclp_interactive muclp =
    match Config.config with
    | MuVal cfg ->
        let module MuVal = MuVal.Solver.Make (struct
          let config = cfg
        end) in
        MuVal.solve_interactive muclp >>= fun _ -> Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_muclp_interactive"

  let solve_qfl ?header qfl =
    match Config.config with
    | MuVal cfg ->
        let module MuVal = MuVal.Solver.Make (struct
          let config = cfg
        end) in
        MuVal.solve_qfl ~print_sol:true qfl >>= fun _ -> Ok ()
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_qfl ?header qfl
    | _ -> Or_error.unimplemented "Solver.solve_qfl"

  (* Hands the backend's options of the transition-system conversion to [LTS]
     before a conversion; MuVal's and MuStrat's configurations carry them, and
     the other backends get [LTS]'s own defaults (choices copied). *)
  let set_lts_conversion_options () =
    match Config.config with
    | MuVal cfg ->
        LTS.Problem.set_wp_share_choice cfg.wp_share_choice;
        LTS.Problem.set_wp_share_choice_min_size cfg.wp_share_choice_min_size
    | MuStrat cfg ->
        LTS.Problem.set_wp_share_choice cfg.wp_share_choice;
        LTS.Problem.set_wp_share_choice_min_size cfg.wp_share_choice_min_size
    | _ ->
        LTS.Problem.set_wp_share_choice false;
        LTS.Problem.set_wp_share_choice_min_size 256

  (* How the T2 reader reads [/] in a file with a [BUCHI] line: MuVal's and
     MuStrat's configurations carry it, and the other backends read it
     exactly, the default of both. *)
  let lts_division () =
    match Config.config with
    | MuVal cfg -> cfg.t2_division
    | MuStrat cfg -> cfg.t2_division
    | _ -> LTS.Problem.Exact

  (* Which cut set the termination encoding of a transition system uses:
     MuVal's and MuStrat's configurations carry it, and the other backends
     take the graph order, the default of both. *)
  let lts_cut_point_choice () =
    match Config.config with
    | MuVal cfg -> cfg.lts_cut_point_choice
    | MuStrat cfg -> cfg.lts_cut_point_choice
    | _ -> LTS.Problem.Graph_order

  (* [compact_after_conversion ()]: one compaction of the major heap between
     reading and converting a transition system and solving the converted
     problem.  Reading a large integer transition system and converting it
     leave a major heap far above what stays live: on a 55 MB input the heap
     was 2.2 GB and the resident size 3.0 GB at the end of the conversion,
     against about 320 MB live and a converted problem of a few MB, and the
     collector does not give that space back by itself.  The fixpoint backends
     fork copies of the process (a continued check, a raced question), and a
     copy's collector writes every page of the heap it inherits, so each
     copy came to cost the whole inflated heap again.  Compacting here
     returned the resident size to about 470 MB.  It changes no value, only
     where the live blocks sit; its cost is a pass over the live heap, once
     per run.

     It runs only when the major heap is at least
     [compact_after_conversion_min_bytes].  A [Gc.compact] costs a full major
     cycle over the program's own live data however small the input is: about
     8 ms on every small input (7-21 ms on inputs under 64 KB), a fixed share
     of a run that takes 0.2 s.  On such inputs the heap is a few tens of MB,
     so what a copy could inherit beyond its live data is bounded by the
     threshold, far below the gigabytes the compaction is there to return.
     Skipping it changes no value either.  [print] reports the heap size and
     the choice. *)
  let compact_after_conversion_min_bytes = 256 * 1024 * 1024

  let compact_after_conversion ~print () =
    let heap = Common.ForkGuard.major_heap_bytes () in
    let compact = heap >= compact_after_conversion_min_bytes in
    print
    @@ lazy
         (sprintf "major heap %d MB after the conversion: %s" (heap / 1_048_576)
            (if compact then "compacting" else "below the threshold, kept"));
    if compact then
      Common.PhaseTime.with_phase "compact-after-conversion" Gc.compact

  let solve_lts ~print (lts, mode) =
    set_lts_conversion_options ();
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
          Common.DagCensus.report "lts-to-muclp: input" lts;
          let lvs, cps, lts =
            LTS.Problem.analyze ~print
              ~cut_point_choice:(lts_cut_point_choice ()) lts
          in
          Common.DagCensus.report "lts-to-muclp: analyzed" lts;
          print @@ lazy "************* converting LTS to muCLP ***************";
          MuCLP.Util.of_lts ~print ~live_vars:(Some lvs) ~cut_points:(Some cps)
            (lts, mode)
        in
        compact_after_conversion ~print ();
        (* with COAR_SHARE_CENSUS set, the sharing of the muCLP the conversion
           made (an instrument: prints only) *)
        Common.DagCensus.report
          ~items:(List.length muclp.MuCLP.Problem.preds)
          "lts-to-muclp: output" muclp;
        match Config.config with
        | MuVal cfg ->
            let module MuVal = MuVal.Solver.Make (struct
              let config = cfg
            end) in
            MuVal.solve_certified ~print_sol:false muclp
            >>= fun (solution, _, _, cert_lines) ->
            print_endline @@ Common.Verdict.lts_str_of solution;
            (* empty unless the config asks for the certificate *)
            List.iter cert_lines ~f:print_endline;
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
    set_lts_conversion_options ();
    match Config.config with
    | MuVal cfg ->
        let muclp =
          let lvs, cps, lts =
            LTS.Problem.analyze ~print
              ~cut_point_choice:(lts_cut_point_choice ()) lts
          in
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
    set_lts_conversion_options ();
    let lts =
      Common.PhaseTime.with_phase "plts-to-lts" @@ fun () ->
      PLTS.Problem.lts_of ~print plts
    in
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
          Common.PhaseTime.with_phase "lts-to-muclp" @@ fun () ->
          Common.DagCensus.report "lts-to-muclp: input" lts;
          let lvs, cps, lts =
            LTS.Problem.analyze ~print
              ~cut_point_choice:(lts_cut_point_choice ()) lts
          in
          Common.DagCensus.report "lts-to-muclp: analyzed" lts;
          print @@ lazy "************* converting LTS to muCLP ***************";
          MuCLP.Util.of_lts ~print ~live_vars:(Some lvs) ~cut_points:(Some cps)
            (lts, mode)
        in
        compact_after_conversion ~print ();
        (* with COAR_SHARE_CENSUS set, the sharing of the muCLP the conversion
           made (an instrument: prints only) *)
        Common.DagCensus.report
          ~items:(List.length muclp.MuCLP.Problem.preds)
          "lts-to-muclp: output" muclp;
        (* with COAR_DUMP_MUCLP naming a file, the muCLP the conversion made
           is written there (and with COAR_DUMP_MUCLP_EXIT also set, the run
           stops): a check that a change to the conversion is exact *)
        (match Sys.getenv "COAR_DUMP_MUCLP" with
        | Some file ->
            Out_channel.write_all file ~data:(MuCLP.Problem.str_of muclp);
            if Option.is_some (Sys.getenv "COAR_DUMP_MUCLP_EXIT") then
              Common.ProcessExit.exit 0
        | None -> ());
        match Config.config with
        | MuVal cfg ->
            let module MuVal = MuVal.Solver.Make (struct
              let config = cfg
            end) in
            MuVal.solve_certified ~print_sol:false muclp
            >>= fun (solution, _, _, cert_lines) ->
            print_endline @@ Common.Verdict.lts_str_of solution;
            (* empty unless the config asks for the certificate *)
            List.iter cert_lines ~f:print_endline;
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

  let solve_hfl filename =
    match Config.config with
    | MuValHFL cfg ->
        let module S = MuValHFL.Solver.Make (struct
          let config = cfg
        end) in
        S.solve_from_file filename
    | MuVal cfg ->
        let module S = MuValHFL.Solver.Make (struct
          let config =
            {
              (Common.Util.config_default MuValHFL.Config.of_yojson "{}") with
              order1_backend = Some (Common.Util.ExtFile.Instance cfg);
            }
        end) in
        S.solve_order1_from_file filename
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_hfl filename
    | _ -> Or_error.unimplemented "Solver.solve_hfl"

  let solve_qhfl filename =
    match Config.config with
    | MuValQHFL cfg ->
        let module S = MuValQHFL.Solver.Make (struct
          let config = cfg
        end) in
        S.solve_from_file filename
    | Printer _ ->
        print_string (In_channel.read_all filename);
        Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_qhfl"

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
        Common.ProcessExit.exit 1
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

  let solve_xmltype defs =
    match Config.config with
    | Printer cfg ->
        let module Printer = Printer.Solver.Make (struct
          let config = cfg
        end) in
        Printer.print_xmltype defs;
        Ok ()
    | _ -> Or_error.unimplemented "Solver.solve_xmltype"
end

module Make (Config : Config.ConfigType) : SolverType = struct
  include Base (Config)
  open Or_error.Monad_infix

  (* Athena's route builds the problem to solve, and the nested MuVal
     configuration solves it exactly as [-p ltsterm]/[-p ltssafe] solve a T2
     file (the llvm2lts route) and [-p llvmterm]/[-p llvmsafe] a translation
     of LLVM IR (the direct route).  The intermediate files may be removed
     once the problem is read, so each callback reads its file and leaves the
     solving for later. *)
  let solve_c ~print ?signed_overflow ~data_model ~property filename =
    match Config.config with
    | Athena cfg ->
        let cfg =
          match (signed_overflow, property) with
          | None, _ | Some _, Athena.Pipeline.No_overflow -> cfg
          | Some so, _ -> { cfg with signed_overflow = Some so }
        in
        Athena.Config.reading cfg >>= fun (_, so) ->
        if Athena.Config.wraps_mathematical cfg then
          prerr_endline
            (if Option.is_some signed_overflow then
               "note: --c-signed-overflow wrap reads integers as Wrapping (the \
                Mathematical reading has no wrap-around)"
             else
               "note: signed_overflow Wraps reads integers as Wrapping (the \
                Mathematical reading has no wrap-around)");
        (match (so, property) with
        | ( Some Athena.Config.Arbitrary_value,
            ( Athena.Pipeline.Termination | Unreach_call | Memory_safety
            | Memory_cleanup | Termination_memory_safe ) ) ->
            (* printed before solving, so it must hold whatever the answer *)
            prerr_endline
              "note: signed overflow is read as yielding an arbitrary value of \
               its type; a NO or a violation may rest on such a value"
        | _ -> ());
        Common.Util.ExtFile.unwrap cfg.solver
        >>= fun (Athena.Config.Solver.MuVal muval) ->
        let module Nested = Base (struct
          let config = SolverConfig.MuVal muval
        end) in
        let lts ~bv_mode file =
          LTS.Parser.from_file ~bv_mode file >>| fun lts ->
          Athena.Pipeline.Problem
            (fun () ->
              Nested.solve_lts ~print
                ( lts,
                  match property with
                  | Athena.Pipeline.Termination | Termination_memory_safe ->
                      LTS.Problem.Term
                  | Unreach_call | Memory_safety | No_overflow
                  | Memory_cleanup ->
                      LTS.Problem.Safe ))
        in
        (* an input the frontend cannot read ends the run with MAYBE, as the
           competition script answers when CoAR fails on it *)
        let direct ~bv_mode ~config ~overrides file =
          match
            LlvmEntry.translate ~witness:cfg.witness ~overrides ~bv_mode
              ~property:
                (match property with
                | Athena.Pipeline.Termination | Termination_memory_safe ->
                    LlvmEntry.Termination
                | Unreach_call | Memory_safety | No_overflow | Memory_cleanup ->
                    LlvmEntry.Unreach_call)
              ~config:(Some config) file
          with
          | Ok (LlvmEntry.Problem (muclp, map)) ->
              Ok
                (Athena.Pipeline.Problem
                   (fun () ->
                     Nested.solve_muclp_lts
                       ?after_verdict:
                         (Option.map map ~f:LLVMWitness.Cinvariant.after_verdict)
                       muclp))
          | Ok (LlvmEntry.Unknown reason) -> Ok (Athena.Pipeline.Unknown reason)
          | Error err -> Ok (Athena.Pipeline.Unknown (Error.to_string_hum err))
        in
        let unknown reason =
          prerr_endline ("unknown: " ^ reason);
          print_endline "MAYBE";
          Ok ()
        in
        (match property with
        | Termination_memory_safe ->
            (* each side is a run of this executable, given the nested MuVal
               configuration as a file: the instance written out, which a
               configuration reads back as the same instance *)
            let solver_config =
              Filename_unix.temp_file "athena_muval" ".json"
            in
            Exn.protect
              ~finally:(fun () ->
                try Sys_unix.remove solver_config
                with exn when not (Common.Timer.is_async exn) -> ())
              ~f:(fun () ->
                Yojson.Safe.to_file solver_config
                  (SolverConfig.to_yojson (SolverConfig.MuVal muval));
                Athena.Pipeline.run_term_memsafe cfg ~data_model ~solver_config
                  filename)
            >>= (function
            | `Unknown reason -> unknown reason
            | `Unsafe ->
                print_endline "UNSAFE";
                Ok ()
            | `Answer answer ->
                print_endline answer;
                Ok ())
        | Termination | Unreach_call | Memory_safety | No_overflow
        | Memory_cleanup -> (
            Athena.Pipeline.run cfg ~data_model ~property
              ~direct_available:LlvmEntry.available ~direct ~lts filename
            >>= function
            | Athena.Pipeline.Problem solve -> solve ()
            | Unknown reason -> unknown reason
            | Holds ->
                (* no check of the property was placed *)
                print_endline "YES";
                Ok ()))
    | _ -> Or_error.unimplemented "Solver.solve_c"
end
