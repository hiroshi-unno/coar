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

let default_config_file = "./config/solver/muval_parallel_exc_tbq_ar.json"

let cmd =
  Command.basic_spec ~summary:"CoAR: Collection of Automated Reasoners"
    Command.Spec.(
      empty
      +> anon ("filename" %: string)
      +> flag "--config"
           (optional_with_default default_config_file string)
           ~aliases:[ "-c" ]
           ~doc:
             (sprintf "<config> specify solver configuration file (default:%s)"
                default_config_file)
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
              witness cannot be built (default: answer sat without it)")

(* A refusal of the command line itself -- a malformed flag, a solver and a
   problem class that do not go together, an input that does not exist -- is
   one line on standard error and status 1, never a backtrace: nothing has
   been solved, so there is no internal state worth showing, and a harness
   reads a backtrace as the tool crashing. *)
let usage_error msg =
  prerr_endline msg;
  exit 1

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

let load_smt ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "smt2" ->
      Ok (SMT.Smtlib2.from_smt2_file ~print ~inline:true (*ToDo*) filename)
  | _ -> wrong_extension ~expected:["smt2"] filename

let load_homc ~print filename =
  match snd (Filename.split_extension filename) with
  | Some ("hrs" | "hors") -> Ok (HOMC.Problem.from_hors_file ~print filename)
  | Some ("hmtt" | "ehmtt") -> Ok (HOMC.Problem.from_ehmtt_file ~print filename)
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
          Ok
            (PCSP.Parser.from_smt2_file ~print ~inline:true (*ToDo*)
               ~skolem_pred:true filename))
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

let load_lts ~bv_mode filename =
  match snd (Filename.split_extension filename) with
  | Some "t2" -> LTS.Parser.from_file ~bv_mode filename
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

let main filename solver problem verbose c_bound_wide_nondets bv_default
    btor2_witness btor2_witness_strict () =
  let open Or_error.Monad_infix in
  if btor2_witness_strict && Option.is_none btor2_witness then
    usage_error "--btor2-witness-strict: requires --btor2-witness";
  (* an empty target is what a wrapper passes when its certificate argument is missing; read
     as a path, it would make every witness fail to be written, and under strict every [sat]
     be withheld *)
  if Option.exists btor2_witness ~f:String.is_empty then
    usage_error
      "--btor2-witness: expected stdout or a file path, got an empty string";
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
          load_solver_config problem solver >>= fun cfg ->
          (* a missing input is refused once, here, instead of by whichever
             reader first opens it *)
          if
            String.is_empty filename
            || not (Sys_unix.file_exists_exn ~follow_symlinks:true filename)
          then usage_error (sprintf "cannot read %s: no such file" filename);
      let module Config = struct
        let config = cfg
      end in
      let module Solver = Solver.Make (Config) in
      Debug.print
      @@ lazy
           (sprintf "*********** %s solving mode ************\n"
           @@ show_problem problem);
      match problem with
      | PSAT -> load_sat ~print:Debug.print filename >>= Solver.solve_sat
      | PDQSAT -> load_dqsat ~print:Debug.print filename >>= Solver.solve_dqsat
      | PHOSAT -> load_hosat filename >>= Solver.solve_hosat
      | PSMT -> load_smt ~print:Debug.print filename >>= Solver.solve_smt
      | PHOMC -> (
          load_homc ~print:Debug.print filename >>= fun homc ->
          (* The two higher-order model checkers read different dialects of the
             same extension and each rejects the other's, so a mismatch is an
             unsupported input rather than a failed verification. The wrappers
             refuse it too, but the whole command ends in [ok_exn], which would
             turn their message into an OCaml backtrace; say it in one line with
             a non-zero status instead, which is what a harness can act on. *)
          let backend_reads_alternating =
            match cfg with
            | CoAR.Solver.Config.TRecS _ -> Some false
            | CoAR.Solver.Config.HorSat2 _ -> Some true
            | _ -> None
          in
          match backend_reads_alternating with
          | Some reads_alt
            when Stdlib.( <> ) reads_alt (HOMC.Problem.reads_alternating homc)
            ->
              print_endline
              @@ sprintf
                   "unsupported input dialect: this file specifies %s, which \
                    %s does not read"
                   (HOMC.Problem.dialect_str_of homc)
                   (if reads_alt then "HorSat2" else "TRecS");
              exit 1
          | _ -> Solver.solve_homc homc)
      | PSyGuS ->
          load_sygus filename >>= Solver.solve_sygus ~filename:(Some filename)
      | PPCSP ->
          (* PCSat reads an [.smt2] input a second time when its configuration
             asks the reader for a switch, and a third time to learn which
             unknowns every solution makes [true]; with [law_read_once] the
             switches are set before this, the first reading, PCSat keeps it,
             and the reading keeps its assertions for that question *)
          (match cfg with
          | CoAR.Solver.Config.PCSat c when c.PCSat.Config.law_read_once ->
              PCSat.Solver.set_law_reader_switches c;
              PCSP.Parser.keep_plain_assertions := true;
              (* and the least-definition probe builds its problem from the
                 assertions the problem in hand was made from, when they are
                 the ones its own reading would start from *)
              PCSP.Parser.keep_least_definition_base :=
                c.PCSat.Config.least_definition_probe
          | _ -> ());
          load_pcsp ~print:Debug.print filename
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
      | PMuCLP -> load_muclp ~print:Debug.print filename >>= Solver.solve_muclp
      | PMuCLPInter ->
          load_muclp ~print:Debug.print filename
          >>= Solver.solve_muclp_interactive
      | PQFL -> load_qfl ~print:Debug.print filename >>= Solver.solve_qfl
      | PPGCL -> (
          print_endline "Solving pGCL...";
          load_pgcl ~print:Debug.print filename >>= fun pgcl ->
          match PGCL.Util.problem_of ~print:Debug.print pgcl with
          | Some problem -> Solver.solve_qfl [ problem ]
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
              exit 1)
      | PSGCL ->
          print_endline "Solving SGCL...";
          load_sgcl ~print:Debug.print filename >>= fun sgcl ->
          Or_error.return
            [ SGCL.Util.problem_of ~filename ~print:Debug.print sgcl ]
          >>= Solver.solve_qfl
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
          load_plts ~print:Debug.print filename >>= fun plts ->
          Solver.solve_plts ~print:Debug.print (plts, PLTS.Problem.Term)
      | PPLTSNTerm ->
          load_plts ~print:Debug.print filename >>= fun plts ->
          Solver.solve_plts ~print:Debug.print (plts, PLTS.Problem.NonTerm)
      | POCaml -> Solver.solve_ml filename
      | PBTOR2 ->
          load_btor2 filename
          >>= Solver.solve_btor2 ~print:Debug.print
                ?witness:(Option.map btor2_witness ~f:BTOR2.Witness.target_of_string)
                ~strict:btor2_witness_strict )
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
  Command_unix.run ~version:Version.version @@ cmd main;
  Common.ProcessExit.exit 0
