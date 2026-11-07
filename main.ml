open Core
open CoAR
open Common
open Common.Combinator

(* the problem classes, their [-p] names and the help text come from one
   table (lib/problemKind.ml); the backend compatibility check is
   [Solver.supports] (lib/solver.ml). *)
open ProblemKind

type problem = ProblemKind.t

let show_problem = ProblemKind.show

let problem =
  Command.Arg_type.create (fun problem ->
      match ProblemKind.of_string problem with
      | Some p -> Or_error.return p
      | None ->
          failwith
            (sprintf "invalid problem: %s (accepted: %s)" problem
               (String.concat ~sep:", "
                  (List.concat_map ProblemKind.table ~f:(fun (_, _, ns) -> ns)))))

(* The configuration a run without [-c] solves with depends on the problem
   class.  Contract: [default_config_file p] is [portfolio_default_config_file]
   (MuVal with the parity-progress-measure reduction for 10 s, then MuStrat for
   60 s, then MuVal with that reduction again to the end of the run) exactly
   for muCLP validity ([PMuCLP]) and integer-transition-system termination
   ([PPLTSTerm]), and [fallback_default_config_file] (MuVal) for every other
   [p], whether or not MuVal accepts it (an unaccepted pairing is refused
   afterwards, as with an explicit [-c]).  The list is explicit rather than
   "every class both stages accept" because those two are the classes the
   portfolio was measured on: on one binary at 300 s it answered 200 of 202
   muCLP inputs and 1170 of 1222 termination inputs, against 195 and 1154 for
   MuVal-with-PPM alone and 200 and 1168 for MuStrat 60 s then MuVal-with-PPM;
   the short first stage answers the inputs MuVal settles at once without
   paying MuStrat's 60 s.  Other classes both stages accept (CHC, pCSP, SyGuS,
   the LTS and LTL/CTL classes) keep MuVal until measured.  The portfolio is
   sound wherever it is offered: it prints the answer of one stage, each run
   on the original input.  Both paths are relative, so this default, like
   every configuration, assumes the repository root as the working
   directory. *)
let portfolio_default_config_file =
  "./config/solver/portfolio_muval_ppm_mustrat_muval_ppm.json"

let fallback_default_config_file = "./config/solver/muval.json"

let default_config_file = function
  | PMuCLP | PPLTSTerm -> portfolio_default_config_file
  | _ -> fallback_default_config_file

let cmd =
  Command.basic_spec ~summary:"CoAR: Collection of Automated Reasoners"
    Command.Spec.(
      empty
      +> anon ("filename" %: string)
      +> flag "--config" (optional string) ~aliases:[ "-c" ]
           ~doc:
             (sprintf
                "<config> specify solver configuration file (default: %s for \
                 muclp and pltsterm, %s otherwise)"
                portfolio_default_config_file fallback_default_config_file)
      +> flag "--problem"
           (optional_with_default (Or_error.return PMuCLP) problem)
           ~aliases:[ "-p" ]
           ~doc:
             (sprintf "choose problem %s (default: muCLP)"
                (ProblemKind.help_string ()))
      +> flag "--verbose" no_arg
           ~aliases:[ "-v" ]
           ~doc:
             "print the frontend's diagnostics while reading the input (the \
              solver's own tracing is set by verbose in the config)"
      +> flag "--c-bound-wide-nondets" no_arg
           ~doc:
             "C frontend: bound 32-/64-bit __VERIFIER_nondet_* results by \
              their width, as the LTS frontend does (default: unsigned ones \
              are only x >= 0, signed ones unbounded)"
      +> flag "--bv-default"
           (optional_with_default "32s" string)
           ~doc:
             "WIDTH[s|u] width and signedness assumed for a bit-vector whose \
              input specifies neither, e.g. a T2 file without TYPE \
              declarations in BV mode (default: 32s)"
      +> flag "--btor2-witness" (optional string)
           ~doc:
             "stdout|PATH -p btor2: on a sat answer, write a counterexample \
              in the BTOR2 witness format to standard output (in place of \
              the sat line, which is its first line) or to the file PATH \
              (default: no witness is computed)"
      +> flag "--btor2-witness-strict" no_arg
           ~doc:
             "-p btor2, with --btor2-witness: withhold a sat answer whose \
              witness cannot be built (default: answer sat without it)"
      +> flag "--llvm-config" (optional string)
           ~doc:
             "PATH -p llvm*: the LLVM frontend's JSON configuration, the \
              readings and encodings that are a choice (default: every \
              field at its default)"
      +> flag "--c-data-model"
           (optional_with_default "LP64" string)
           ~doc:
             "LP64|ILP32 -p cterm, csafe, cmemsafe, cmemcleanup, cnooverflow, \
              ctermmemsafe: the data model the C program is read and \
              compiled in, as the task states it (default: LP64)"
      +> flag "--c-signed-overflow" (optional string)
           ~doc:
             "wrap|undefined|arbitrary -p cterm, csafe, cmemsafe, \
              cmemcleanup, ctermmemsafe: what an overflowing signed operation \
              yields, as the task's compiler is not stated: its \
              two's-complement value (as with -fwrapv), undefined behaviour \
              (the execution stops, as SV-COMP reads it; also the answer for \
              a build that traps), or an arbitrary value of its type, every \
              choice covered (the direct route only); -p cnooverflow reads \
              none (default: the configuration's signed_overflow)")

(* A refusal of the command line itself -- a malformed flag, a solver and a
   problem class that do not go together, an input that does not exist -- is
   one line on standard error and status 1, never a backtrace: nothing has
   been solved, so there is no internal state worth showing, and a harness
   reads a backtrace as the tool crashing. *)
let usage_error msg =
  prerr_endline msg;
  Common.ProcessExit.exit 1

let load_solver_config prblm solver =
  (match ProblemKind.unimplemented prblm with
  | Some why ->
      usage_error
      @@ sprintf
           "the problem class %s is declared but has no implementation yet: %s"
           (ProblemKind.name_of prblm)
           why
  | None -> ());
  match Solver.Config.load_config solver with
  | Error err -> Error err
  | Ok cfg ->
      if Solver.supports cfg prblm then Or_error.return cfg
      else
        usage_error
        @@ sprintf "The specified solver does not support the problem %s"
             (ProblemKind.name_of prblm)

(* Each reader below is chosen by the file's extension; a file with another
   extension is refused by name rather than reported as an unimplemented
   function, which is what it used to say. *)
let wrong_extension ~expected filename =
  Or_error.error_string
  @@ sprintf "cannot read %s: this problem class reads files ending in %s"
       filename
       (String.concat ~sep:", " (List.map expected ~f:(fun e -> "." ^ e)))

(* [true] iff [filename] itself, or [filename] with its trailing [.gz]
   stripped, has one of [exts] as its extension. *)
let has_ext_or_gz exts filename =
  let has_ext fn =
    match snd (Filename.split_extension fn) with
    | Some ext -> List.mem exts ext ~equal:String.equal
    | None -> false
  in
  has_ext filename
  ||
  match Filename.split_extension filename with
  | fn, Some "gz" -> has_ext fn
  | _ -> false

let load_sat ~print filename =
  if has_ext_or_gz [ "dimacs"; "cnf" ] filename then
    match snd (Filename.split_extension filename) with
    | Some "gz" -> Ok (SAT.Problem.from_gzipped_dimacs_file ~print filename)
    | _ -> Ok (SAT.Problem.from_dimacs_file ~print filename)
  else wrong_extension ~expected:["cnf"; "dimacs"; "cnf.gz"; "dimacs.gz"] filename

let load_dqsat ~print filename =
  if has_ext_or_gz [ "qdimacs"; "dqdimacs" ] filename then
    match snd (Filename.split_extension filename) with
    | Some "gz" -> Ok (DQSAT.Problem.from_gzipped_dqdimacs_file ~print filename)
    | _ -> Ok (DQSAT.Problem.from_dqdimacs_file ~print filename)
  else wrong_extension ~expected:["qdimacs"; "dqdimacs"; "qdimacs.gz"; "dqdimacs.gz"] filename

let load_hosat filename =
  match snd (Filename.split_extension filename) with
  | Some "hosat" -> Ok (HOSAT.Problem.from_hosat_file filename)
  | _ -> wrong_extension ~expected:["hosat"] filename

(* [-p smt] answers every [check-sat] and [check-sat-assuming] of the session,
   in order, one answer per check in the form a single check is answered, as
   z3 and cvc5 do; each check is the problem in scope at it.

   A file with at most one check is read and solved in this process, exactly
   as before checks were counted.  With several, check [k] is read and solved
   in a forked copy of its own, made after the input is parsed and before
   anything of it is read: reading and solving set process-global state (the
   function and datatype environments, which may be set only before a solver
   domain exists, and the lemma registries), which would otherwise leak from
   one check into the next.  The copies run one at a time, so the answers come
   out in order; a copy that ends with an error has printed it, and the later
   checks are not asked, as cvc5 stops at its first error.  [report_error]
   prints a refusal or an error value and ends the process (status 1).

   [solve] receives a reader thunk so that it can choose a portfolio stage
   before reading installs process-global environments. A portfolio thus
   answers each check independently, and an undecided later check can try its
   next stage even when an earlier check was decided.

   Assumes no domain other than the main one exists yet: OCaml refuses to fork
   once one has been spawned, and nothing before a solver is built spawns
   one. *)
let solve_smt ~print ~report_error ~solve filename =
  match snd (Filename.split_extension filename) with
  | Some "smt2" -> (
      let sexps = SMT.Smtlib2.read_smt2_sexps filename in
      let threshold = SMT.Smtlib2.threshold_of_sexps sexps in
      let solve_check ?check () =
        solve ?threshold (fun () ->
            SMT.Smtlib2.of_smt2_sexps ~print ~inline:true (*ToDo*) ?check sexps)
      in
      match SMT.Smtlib2.count_checks sexps with
      | n when n <= 1 -> solve_check ()
      | n ->
          let rec from k =
            if k > n then Ok ()
            else (
              Out_channel.flush stdout;
              Out_channel.flush stderr;
              match Common.ForkGuard.fork () with
              | `In_the_child -> (
                  match solve_check ~check:k () with
                  | Ok () -> Common.ProcessExit.exit 0
                  | Error err -> report_error (Error.to_string_hum err)
                  | exception Common.Refusal.Refused msg -> report_error msg
                  | exception exn ->
                      (* the copy must never return into this loop *)
                      eprintf "Uncaught exception in check %d:\n  %s\n%s" k
                        (Exn.to_string exn)
                        (Printexc.get_backtrace ());
                      Common.ProcessExit.exit 2)
              | `In_the_parent pid -> (
                  Common.ForkGuard.register (Core.Pid.to_int pid);
                  let status = Core_unix.waitpid pid in
                  Common.ForkGuard.unregister (Core.Pid.to_int pid);
                  match status with
                  | Ok () -> from (k + 1)
                  | Error (`Exit_non_zero code) -> Common.ProcessExit.exit code
                  | Error (`Signal s) ->
                      report_error
                        (sprintf "check %d of %d ended by signal %s" k n
                           (Signal.to_string s))))
          in
          from 1)
  | _ -> wrong_extension ~expected:["smt2"] filename

(* [-] names standard input, which is read as an EHMTT: no extension is
   there to choose the dialect, and EHMTT is what the original EHMTT verifier
   read from standard input. *)
let load_homc ~print filename =
  if String.equal filename "-" then Ok (HOMC.Problem.from_ehmtt_stdin ~print ())
  else
    match snd (Filename.split_extension filename) with
    | Some ("hrs" | "hors") -> Ok (HOMC.Problem.from_hors_file ~print filename)
    | Some ("hmtt" | "ehmtt") ->
        Ok (HOMC.Problem.from_ehmtt_file ~print filename)
    | _ -> wrong_extension ~expected:["hrs"; "hors"; "hmtt"; "ehmtt"] filename

let load_pcsp ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "clp" -> Ok (PCSP.Parser.from_clp_file ~print filename)
  | _ when has_ext_or_gz [ "smt2" ] filename -> (
      match snd (Filename.split_extension filename) with
      | Some "gz" ->
          Ok
            (PCSP.Parser.from_gzipped_smt2_file ~print ~inline:true (*ToDo*)
               ~skolem_pred:true filename)
      | _ ->
          (* [COAR_READ_STAGE] set: the reader's stages, and the end of the
             reading, go to stderr with the seconds since the reading began *)
          let t0 = Common.Clock.now_s () in
          if Option.is_some (Sys.getenv "COAR_READ_STAGE") then
            PCSP.Parser.stage_trace := (fun l -> eprintf "%s\n%!" l);
          let pcsp =
            PCSP.Parser.from_smt2_file ~print ~inline:true (*ToDo*)
              ~skolem_pred:true filename
          in
          if Option.is_some (Sys.getenv "COAR_READ_STAGE") then
            eprintf "[load] returned at %.2f s\n%!" (Common.Clock.now_s () -. t0);
          Ok pcsp)
  | _ -> wrong_extension ~expected:["clp"; "smt2"; "smt2.gz"] filename

let load_sygus filename =
  match snd (Filename.split_extension filename) with
  | Some "sl" -> SyGuS.Parser.from_file filename
  | _ -> wrong_extension ~expected:["sl"] filename

let load_chcmax ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "smt2" ->
      Result.Monad_infix.(
        load_pcsp ~print filename >>= (CHCOpt.Problem.of_pcsp >> Or_error.return))
  | _ -> wrong_extension ~expected:["smt2"] filename

let load_muclp ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "hes" -> MuCLP.Util.from_file ~print filename
  | _ -> wrong_extension ~expected:["hes"] filename

(* An HFL problem is read by its solver, which tells an HES ([.in], the
   tools' extension, or [.hfl]) from its OCaml representation ([.ml]);
   [.hes] is muCLP's and is not accepted here. *)
let load_hfl filename =
  match snd (Filename.split_extension filename) with
  | Some ("in" | "hfl" | "ml") -> Ok filename
  | _ -> wrong_extension ~expected:[ "in"; "hfl"; "ml" ] filename

(* A quantitative HFL problem is an OCaml file in an expectation mode;
   [.qhfl] is reserved for a text syntax that does not exist yet. *)
let load_qhfl filename =
  match snd (Filename.split_extension filename) with
  | Some "ml" -> Ok filename
  | Some "qhfl" ->
      Or_error.error_string
        "refused: QHFL has no text syntax yet; give its OCaml representation \
         (.ml) in an expectation mode"
  | _ -> wrong_extension ~expected:[ "ml" ] filename

let load_qfl ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "qhes" -> QFL.Util.from_file ~print filename
  | _ -> wrong_extension ~expected:["qhes"] filename

let load_pgcl ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "pgcl" -> PGCL.Util.from_file ~print filename
  | _ -> wrong_extension ~expected:["pgcl"] filename

let load_sgcl ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "sgcl" -> SGCL.Util.from_file ~print filename
  | _ -> wrong_extension ~expected:["sgcl"] filename

let load_cltl ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "c" -> C.Parser.from_cltl_file ~print filename
  | _ -> wrong_extension ~expected:["c"] filename

let load_cctl ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "c" -> C.Parser.from_cctl_file ~print filename
  | _ -> wrong_extension ~expected:["c"] filename

let load_lts ?division ~bv_mode filename =
  match snd (Filename.split_extension filename) with
  | Some "t2" ->
      Result.bind (LTS.Parser.from_file ?division ~bv_mode filename)
        ~f:(fun ((start, _, _, _, trans, _) as lts) ->
          (* A file with neither a START line nor a transition (an empty
             file, or one holding only comments) has no runs, so every mode
             would answer by vacuity: terminating, never non-terminating,
             safe.  Such files are what a C-to-T2 converter leaves when it
             gives up on a program (on recursion, for instance), so the
             vacuous answer contradicts the program about as often as it
             agrees with it; the file states no question and is refused.  A
             START line with no transitions is a one-location system and is
             still answered. *)
          if Option.is_none start && List.is_empty trans then
            Or_error.error_string
              "the file has no START line and no transition, so it states no \
               transition system to ask about"
          else Ok lts)
  | _ -> wrong_extension ~expected:["t2"] filename

(* The HWMCC 2019 word-level track names 181 of its BTOR2 models [.btor], and none of them is
   in the legacy BTOR format: the extension does not tell the two apart, and only BTOR2 is
   read, so a legacy file is refused by the reader at its first line that BTOR2 lacks. *)
let load_btor2 filename =
  match snd (Filename.split_extension filename) with
  | Some ("btor2" | "btor") ->
      Or_error.map ~f:BTOR2.Problem.ts_of (BTOR2.Parser.from_file filename)
  | _ -> wrong_extension ~expected:["btor2"; "btor"] filename

let load_plts ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "smt2" -> PLTS.Parser.from_file ~print filename
  | _ -> wrong_extension ~expected:["smt2"] filename

(* The direct LLVM frontend's answer: a muCLP problem to solve, or UNKNOWN,
   which is answered MAYBE (the LTS vocabulary the competition wrappers read)
   with its reason on standard error.  With the map from the loop heads to
   the C program, a YES whose backend returns the solution is followed by one
   line per loop head: the invariant the solution gives it over C variables,
   or why there is none (LLVMWitness.Cinvariant).  A YES without a solution
   is followed by nothing, which a correctness witness reads as no
   invariant. *)
let llvm_answer ~solve_muclp = function
  | LlvmEntry.Problem (p, None) -> solve_muclp ?after_verdict:None p
  | LlvmEntry.Problem (p, Some map) ->
      solve_muclp
        ?after_verdict:(Some (LLVMWitness.Cinvariant.after_verdict map))
        p
  | LlvmEntry.Unknown reason ->
      prerr_endline ("unknown: " ^ reason);
      print_endline "MAYBE";
      Or_error.return ()

let load_llvm ~bv_mode ~property ~config filename =
  match snd (Filename.split_extension filename) with
  | Some ("ll" | "bc") ->
      LlvmEntry.translate ~bv_mode ~property ~config filename
  | _ -> wrong_extension ~expected:["ll"; "bc"] filename

(* Athena's route reads a C program, preprocessed or not *)
let check_c_input filename =
  match snd (Filename.split_extension filename) with
  | Some ("c" | "i") -> Ok ()
  | _ -> wrong_extension ~expected:[ "c"; "i" ] filename

(* the file reader owns its channel; a syntax error comes back as an error
   carrying the file, line and column *)
let load_xmltype filename =
  match snd (Filename.split_extension filename) with
  | Some "xt" -> Grammar.RegTreeExpReader.from_file filename
  | _ -> wrong_extension ~expected:[ "xt" ] filename

let main filename solver problem verbose c_bound_wide_nondets bv_default
    btor2_witness btor2_witness_strict llvm_config c_data_model
    c_signed_overflow () =
  let open Or_error.Monad_infix in
  if btor2_witness_strict && Option.is_none btor2_witness then
    usage_error "--btor2-witness-strict: requires --btor2-witness";
  (* an empty target is what a wrapper passes when its certificate argument is missing; read
     as a path, it would make every witness fail to be written, and under strict every [sat]
     be withheld *)
  if Option.exists btor2_witness ~f:String.is_empty then
    usage_error
      "--btor2-witness: expected stdout or a file path, got an empty string";
  let c_data_model =
    match c_data_model with
    | "LP64" -> Athena.Pipeline.LP64
    | "ILP32" -> Athena.Pipeline.ILP32
    | other ->
        usage_error
          (sprintf "--c-data-model: expected LP64 or ILP32, got %s" other)
  in
  let signed_overflow =
    Option.map c_signed_overflow ~f:(function
      | "wrap" -> Athena.Config.Wraps
      | "undefined" -> Athena.Config.Undefined
      | "arbitrary" -> Athena.Config.Arbitrary_value
      | other ->
          usage_error
            (sprintf
               "--c-signed-overflow: expected wrap, undefined or arbitrary, \
                got %s"
               other))
  in
  (* COAR_PHASE_TIME set: the phase-time account is on from the start of
     solving, for every backend (PCSat's own [phase_time_report] starts it only
     when a PCSat solver is built, which a fixpoint solver does after its own
     preprocessing); a diagnostic switch, the account changes no result.
     Started once the configuration is read and, for a portfolio, in each
     stage's copy, never in the process that runs the stages: the account's
     signal watcher is a thread, which a forked copy would not have, while it
     would keep the account's own SIGTERM handler, and so ignore SIGTERM. *)
  let enable_phase_time () =
    if Option.is_some (Sys.getenv "COAR_PHASE_TIME") then
      Common.PhaseTime.enable ()
  in
  C.CSyntax.bound_wide_nondets := c_bound_wide_nondets;
  (match
     Scanf.sscanf bv_default "%d%s" (fun w s ->
         match s with
         | "" | "s" -> Some (w, true)
         | "u" -> Some (w, false)
         | _ -> None)
   with
  | Some (w, signed) when w > 0 ->
      Ast.LogicOld.T_bv.default_bits := w;
      Ast.LogicOld.T_bv.default_signed := signed
  | _ | (exception _) ->
      usage_error
        (sprintf "--bv-default: expected WIDTH[s|u] (e.g. 32s, 64u), got %s"
           bv_default));
  let module Debug =
    Debug.Make ((val Debug.Config.(if verbose then enable else disable))) in
  (* What reaches the end of this function as an [Error], or as a [Refused],
     is something a reader or a solver said about itself in words: an input it
     does not handle, a pairing it declines, a failure it noticed.  It is
     printed as one line on standard error with status 1.  The previous
     [ok_exn] printed it as an OCaml backtrace whose frames named only this
     function, which added nothing to the message and made a refusal
     indistinguishable from a crash.  Every other exception still escapes
     unchanged, with its backtrace. *)
  let report_error msg =
    prerr_endline ("error: " ^ msg);
    (* a parallel backend may report its error while other domains still run *)
    Common.ProcessExit.exit 1
  in
  match
    try
      `Done
        ( problem >>= fun problem ->
          let solver =
            Option.value_or_thunk solver ~default:(fun () ->
                default_config_file problem)
          in
          load_solver_config problem solver >>= fun cfg ->
          (* a missing input is refused once, here, instead of by whichever
             reader first opens it; [-p homc] reads [-] as standard input *)
          if
            String.is_empty filename
            || (not
                  (ProblemKind.equal problem PHOMC && String.equal filename "-"))
               && not (Sys_unix.file_exists_exn ~follow_symlinks:true filename)
          then usage_error (sprintf "cannot read %s: no such file" filename);
          (* SMT sessions choose a stage separately for each check, before
             its reader installs any process-global environments. *)
          let cfg =
            if ProblemKind.equal problem PSMT then cfg
            else Solver.Config.stage_to_run ~print:Debug.print cfg
          in
          if not (ProblemKind.equal problem PSMT) then enable_phase_time ();
      let module Config = struct
        let config = cfg
      end in
      let module Solver = Solver.Make (Config) in
      (* the T2 reader's reading of [/] in LTL-VerP's dialect is the
         backend configuration's choice *)
      let load_lts =
        load_lts ~division:(Solver.lts_division ())
      in
      Debug.print
      @@ lazy
           (sprintf "*********** %s solving mode ************\n"
           @@ show_problem problem);
      match problem with
      | PSAT -> load_sat ~print:Debug.print filename >>= Solver.solve_sat
      | PDQSAT -> load_dqsat ~print:Debug.print filename >>= Solver.solve_dqsat
      | PHOSAT -> load_hosat filename >>= Solver.solve_hosat
      | PSMT ->
          solve_smt ~print:Debug.print ~report_error
            ~solve:(fun ?threshold read ->
              let cfg =
                CoAR.Solver.Config.stage_to_run ~print:Debug.print cfg
              in
              enable_phase_time ();
              let module CheckSolver = CoAR.Solver.Make (struct
                let config = cfg
              end) in
              CheckSolver.solve_smt ?threshold (read ()))
            filename
      | PHOMC -> (
          load_homc ~print:Debug.print filename >>= fun homc ->
          (* TRecS and HorSat2 decide HORS problems, each reading either
             automaton dialect; an EHMTT program is EffCaml's, which reduces
             it to HORS problems for the checker its configuration names.
             The wrappers refuse an EHMTT too, but the whole command ends in
             [ok_exn], which would turn their message into an OCaml
             backtrace; say it in one line with a non-zero status instead,
             which is what a harness can act on.  The pairing is decided
             here, once the input is read, because the extension that tells
             the two kinds apart is not known to the compatibility table. *)
          match (cfg, homc) with
          | CoAR.Solver.Config.TRecS _, HOMC.Problem.EHMTT _ ->
              usage_error
                "TRecS decides a HORS problem (.hrs, .hors); this input is an \
                 EHMTT program, which EffCaml verifies with TRecS as its \
                 checker (-c config/solver/effcaml_trecs.json)"
          | CoAR.Solver.Config.HorSat2 _, HOMC.Problem.EHMTT _ ->
              usage_error
                "HorSat2 decides a HORS problem (.hrs, .hors); this input is an \
                 EHMTT program, which EffCaml verifies with HorSat2 as its \
                 checker (-c config/solver/effcaml.json)"
          | _ -> Solver.solve_homc homc)
      | PSyGuS ->
          load_sygus filename >>= Solver.solve_sygus ~filename:(Some filename)
      | PPCSP ->
          (* PCSat reads an [.smt2] input a second time when its configuration
             asks the reader for a switch, and a third time to learn which
             unknowns every solution makes [true]; with [reader.laws.read_once] the
             switches are set before this, the first reading, PCSat keeps it,
             and the reading keeps its assertions for that question *)
          (match cfg with
          | CoAR.Solver.Config.PCSat c when c.PCSat.Config.reader.laws.read_once ->
              PCSat.Solver.set_law_reader_switches c;
              PCSP.Parser.keep_plain_assertions := true;
              (* and the least-definition probe builds its problem from the
                 assertions the problem in hand was made from, when they are
                 the ones its own reading would start from *)
              PCSP.Parser.keep_least_definition_base :=
                (match c.PCSat.Config.probes.least_definition.mode with
                | Off -> false
                | Sequential | Raced -> true)
          | _ -> ());
          (* with PCSat's [phase_time_report], the account starts here, so
             that the first reading of the input and the solving entry's
             checks before PCSat (the known-function context admission) are
             phases of the report rather than its "unaccounted" time; the
             solver's own [enable] is then a no-op *)
          (match cfg with
          | CoAR.Solver.Config.PCSat c when c.PCSat.Config.phase_time_report ->
              Common.PhaseTime.enable ()
          | _ -> ());
          Common.PhaseTime.with_phase "read-input" (fun () ->
              load_pcsp ~print:Debug.print filename)
          >>= Solver.solve_pcsp ~filename:(Some filename)
                ~require_context_model:
                  (has_ext_or_gz [ "smt2" ] filename
                  &&
                  match cfg with
                  | CoAR.Solver.Config.Printer _ -> false
                  | _ -> true)
      | PCHCMax ->
          load_chcmax ~print:Debug.print filename
          >>= Solver.solve_chcopt ~filename:(Some filename)
      | PMuCLP ->
          Common.PhaseTime.with_phase "read-input" (fun () ->
              load_muclp ~print:Debug.print filename)
          >>= Solver.solve_muclp
      | PMuCLPInter ->
          load_muclp ~print:Debug.print filename
          >>= Solver.solve_muclp_interactive
      | PQFL -> load_qfl ~print:Debug.print filename >>= Solver.solve_qfl
      | PPGCL when (match cfg with CoAR.Solver.Config.Printer _ -> true | _ -> false) ->
          (* the QFL problem the program reduces to, in the syntax of [-p qfl] *)
          load_pgcl ~print:Debug.print filename >>= fun pgcl ->
          let problem, header =
            PGCL.Util.printable_problem_of ~print:Debug.print pgcl
          in
          Solver.solve_qfl ?header [ problem ]
      | PPGCL -> (
          print_endline "Solving pGCL...";
          load_pgcl ~print:Debug.print filename >>= fun pgcl ->
          match PGCL.Util.problem_of ~print:Debug.print pgcl with
          | Some problem ->
              Debug.print
              @@ lazy
                   (sprintf "*********** QFL problem ************\n%s"
                      (QFL.Problem.str_of problem));
              Solver.solve_qfl [ problem ]
          (* Only a bound query is reduced to a solvable problem.  This used to be
             [Or_error.return ()], so the run printed "Solving pGCL..." and exited 0 with no
             answer -- indistinguishable from success, and the quietest way to be broken. *)
          | None ->
              (* Printed and exited rather than returned as an [Or_error]: the whole command
                 ends in [ok_exn], so an error value reaches the user as an OCaml backtrace,
                 which is the wrong shape for "this input asks for something the tool does not
                 reduce". One line and a non-zero status is what a harness can act on. *)
              print_endline
              @@ sprintf
                   "unsupported query: this pGCL program asks for %s, and only a bound query \
                    is reduced to a solvable problem"
                   (PGCL.PgclSyntax.Query.describe pgcl.query);
              Common.ProcessExit.exit 1)
      | PSGCL -> (
          match cfg with
          | CoAR.Solver.Config.Printer _ ->
              (* the program as the reader built it, as a comment, and the
                 QFL problem it reduces to, in the syntax of [-p qfl] *)
              load_sgcl ~print:Debug.print filename >>= fun sgcl ->
              Solver.solve_qfl
                ~header:(SGCL.SgclSyntax.Program.str_of sgcl)
                [ SGCL.Util.problem_of ~filename ~print:Debug.print sgcl ]
          | _ ->
              print_endline "Solving SGCL...";
              load_sgcl ~print:Debug.print filename >>= fun sgcl ->
              Or_error.return
                [ SGCL.Util.problem_of ~filename ~print:Debug.print sgcl ]
              >>= Solver.solve_qfl)
      | PCLTL -> load_cltl ~print:Debug.print filename >>= Solver.solve_muclp
      | PCCTL -> load_cctl ~print:Debug.print filename >>= Solver.solve_muclp
      | PLTSSafe bv_mode ->
          load_lts ~bv_mode filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.Safe)
      | PLTSNSafe bv_mode ->
          load_lts ~bv_mode filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.NonSafe)
      | PLTSTerm bv_mode ->
          load_lts ~bv_mode filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.Term)
      | PLTSNTerm bv_mode ->
          load_lts ~bv_mode filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.NonTerm)
      | PLTSBuchi bv_mode ->
          load_lts ~bv_mode filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.Buchi)
      | PLTSExBuchi bv_mode ->
          load_lts ~bv_mode filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.ExBuchi)
      | PLTSMuCal bv_mode ->
          load_lts ~bv_mode filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.MuCal)
      | PLTSRel bv_mode ->
          load_lts ~bv_mode filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.Rel)
      | PLTSTermInter bv_mode ->
          load_lts ~bv_mode filename >>= fun lts ->
          Solver.solve_lts_interactive ~print:Debug.print lts
      | PPLTSTerm ->
          Common.PhaseTime.with_phase "read-input" (fun () ->
              load_plts ~print:Debug.print filename)
          >>= fun plts ->
          Solver.solve_plts ~print:Debug.print (plts, PLTS.Problem.Term)
      | PPLTSNTerm ->
          load_plts ~print:Debug.print filename >>= fun plts ->
          Solver.solve_plts ~print:Debug.print (plts, PLTS.Problem.NonTerm)
      | POCaml -> Solver.solve_ml filename
      | PHFL -> load_hfl filename >>= Solver.solve_hfl
      | PQHFL -> load_qhfl filename >>= Solver.solve_qhfl
      | PBTOR2 ->
          load_btor2 filename
          >>= Solver.solve_btor2 ~print:Debug.print
                ?witness:(Option.map btor2_witness ~f:BTOR2.Witness.target_of_string)
                ~strict:btor2_witness_strict
      | PLLVMSafe bv_mode ->
          load_llvm ~bv_mode ~property:LlvmEntry.Unreach_call
            ~config:llvm_config filename
          >>= llvm_answer ~solve_muclp:Solver.solve_muclp_lts
      | PLLVMTerm bv_mode ->
          load_llvm ~bv_mode ~property:LlvmEntry.Termination
            ~config:llvm_config filename
          >>= llvm_answer ~solve_muclp:Solver.solve_muclp_lts
      | PCTerm ->
          check_c_input filename >>= fun () ->
          Solver.solve_c ~print:Debug.print ?signed_overflow
            ~data_model:c_data_model
            ~property:Athena.Pipeline.Termination filename
      | PCSafe ->
          check_c_input filename >>= fun () ->
          Solver.solve_c ~print:Debug.print ?signed_overflow
            ~data_model:c_data_model
            ~property:Athena.Pipeline.Unreach_call filename
      | PCMemSafe ->
          check_c_input filename >>= fun () ->
          Solver.solve_c ~print:Debug.print ?signed_overflow
            ~data_model:c_data_model
            ~property:Athena.Pipeline.Memory_safety filename
      | PCNoOverflow ->
          check_c_input filename >>= fun () ->
          Solver.solve_c ~print:Debug.print ?signed_overflow
            ~data_model:c_data_model
            ~property:Athena.Pipeline.No_overflow filename
      | PCMemCleanup ->
          check_c_input filename >>= fun () ->
          Solver.solve_c ~print:Debug.print ?signed_overflow
            ~data_model:c_data_model
            ~property:Athena.Pipeline.Memory_cleanup filename
      | PCTermMemSafe ->
          check_c_input filename >>= fun () ->
          Solver.solve_c ~print:Debug.print ?signed_overflow
            ~data_model:c_data_model
            ~property:Athena.Pipeline.Termination_memory_safe filename
      | PXMLType -> load_xmltype filename >>= Solver.solve_xmltype )
    with Common.Refusal.Refused msg -> `Refused msg
  with
  | `Done (Ok ()) -> ()
  | `Done (Error err) -> report_error (Error.to_string_hum err)
  | `Refused msg -> report_error msg

(* The process ends through [Common.ProcessExit.exit], never by falling off the
   end of the program: a parallel backend (MuVal's primal/dual modes, the only
   user of [Common.Util.Task]'s domain pool) returns its printed answer while
   domains it never joined may still be inside Z3, and the C [exit] that ends
   an OCaml program runs libz3's static destructors under them, which corrupted the heap after
   the answer and turned an answered run into a crash or a hang.
   [ProcessExit.exit] runs the OCaml [at_exit] handlers and flushes, then
   ends the process without the C library's exit handlers. *)
let () =
  (* the copy of this executable that Athena's rewriting step starts to run
     Frama-C, which reads its own command line: it never reaches CoAR's *)
  Athena.P2aEntry.run_child_if_asked ();
  Command_unix.run ~version:Version.version @@ cmd main;
  Common.ProcessExit.exit 0
