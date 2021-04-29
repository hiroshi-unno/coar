open Core
open Async
open CoAR
open Common

(* let error_string = Deferred.Or_error.error_string *)

type problem =
  | PSAT (** SAT *)
  | PSMT (** SMT *)
  | PPCSP (** pfwCSP *)
  | PMuCLP (** muCLP *)
  | PSyGuS (** SyGyS Inv/CLIA Tracks *)
  | PCCTL (** CTL verification of C programs *)
  | PLTSTerm (** Termination verification of labeled transition systems *)
  | PLTSNTerm (** Non-termination verification of labeled transition systems *)
  | PLTSCTerm (** Interactive conditional (non-)termination analysis of labeled transition systems *)
  [@@deriving show]

type term =
  | Original
  | New

let problem = 
  Command.Arg_type.create (fun problem ->
      let open Deferred.Or_error in
      problem |> String.lowercase |> function
      | "sat"           -> return PSAT
      | "smt"           -> return PSMT
      | "chc"          -> return PPCSP
      | "pcsp"          -> return PPCSP
      | "pfwcsp"        -> return PPCSP
      | "muclp"         -> return PMuCLP
      | "sygus"         -> return PSyGuS
      | "cctl"
      | "c-ctl"         -> return PCCTL
      | "ltsterm"
      | "lts-term"      -> return PLTSTerm
      | "ltsnterm"
      | "lts-nterm"     -> return PLTSNTerm
      | "ltscterm"
      | "lts-cterm"     -> return PLTSCTerm
      | _ -> error_string (Printf.sprintf "invalid problem: %s" problem))

let term =
  Command.Arg_type.create (fun term ->
      let open Deferred.Or_error in
      term |> String.lowercase |> function
      | "original" -> return Original
      | "new"      -> return New
      | _ -> error_string (Printf.sprintf "invalid term: %s" term))

let default_config_file = "./config/solver/muval_tb_ucore_prove.json"

let cmd =
  Command.async_spec_or_error
    ~summary:("")
    Command.Spec.(
      empty
      +> anon ("filename" %: string)
      +> flag "--config" (optional_with_default default_config_file string)
        ~aliases:["-c"]
        ~doc:(Printf.sprintf
                "<config> specify solver configuration file (default:%s)"
                default_config_file)
      +> flag "--problem" (optional_with_default
                             (Deferred.Or_error.return PMuCLP) problem)
        ~aliases:["-p"]
        ~doc:"choose problem [SAT/SMT/CHC/pCSP/pfwCSP/muCLP/SyGuS/CCTL/LTSterm/LTSnterm] (default: muCLP)"
      +> flag "--verbose" no_arg (* is this option obsolete? *)
        ~aliases:["-v"] ~doc:"enable verbose mode"
      +> flag "--term" (optional_with_default
                          (Deferred.Or_error.return Original) term)
        ~aliases:["-t"]
        ~doc:(Printf.sprintf
                "<term> specify term configuration [original/new] (default:original)")
    )

let load_solver_config prblm solver =
  let open Deferred.Or_error in
  match Solver.Config.load_config solver with
  | Ok cfg ->
    begin
      match cfg with
      | Solver.Config.MuVal _ when Stdlib.(=) prblm PLTSCTerm ->
        return cfg
      | Solver.Config.MuVal _
        when Stdlib.(=) prblm PPCSP || Stdlib.(=) prblm PMuCLP ||
             Stdlib.(=) prblm PCCTL || Stdlib.(=) prblm PLTSTerm || Stdlib.(=) prblm PLTSNTerm ->
        return cfg
      | Solver.Config.PCSat _
        when Stdlib.(=) prblm PPCSP || Stdlib.(=) prblm PSyGuS ||
             Stdlib.(=) prblm PLTSTerm || Stdlib.(=) prblm PLTSNTerm ->
        return cfg
      | Solver.Config.SPACER _ | Solver.Config.Hoice _
        when Stdlib.(=) prblm PPCSP || Stdlib.(=) prblm PSyGuS ->
        return cfg
      | Solver.Config.Minisat _ | Solver.Config.Z3Sat _
        when Stdlib.(=) prblm PSAT ->
        return cfg
      | Solver.Config.Z3Smt _
        when Stdlib.(=) prblm PSMT ->
        return cfg
      | Solver.Config.Printer _
        when Stdlib.(=) prblm PPCSP || Stdlib.(=) prblm PMuCLP || Stdlib.(=) prblm PSyGuS ||
             Stdlib.(=) prblm PCCTL || Stdlib.(=) prblm PLTSTerm || Stdlib.(=) prblm PLTSNTerm ->
        return cfg
      | _ ->
        error_string 
        @@ Printf.sprintf "The specified solver does not support the problem %s"
          (show_problem prblm)
    end
  | Error err -> Deferred.return (Error err)

let load_muclp filename =
  if Stdlib.(=) (snd (Filename.split_extension filename)) (Some "hes") then
    MuCLP.Parser.from_file filename
  else Or_error.unimplemented "load_muclp"

let load_pcsp filename =
  if Stdlib.(=) (snd (Filename.split_extension filename)) (Some "smt2") then
    PCSP.Parser.from_smt2_file ~skolem_pred:true filename
  else if Stdlib.(=) (snd (Filename.split_extension filename)) (Some "clp") then
    PCSP.Parser.from_clp_file filename
  else Or_error.unimplemented "load_pcsp"

let load_sygus term filename =
  if Stdlib.(=) (snd (Filename.split_extension filename)) (Some "sl") then
    match term with
    (*    | Original ->
          SyGuS.SyGuSInvParser.from_file filename >>= fun (_logic_type, phis) ->
          Ok (PCSP.Problem.of_formulas phis)*)
    | Original
    | New -> SyGuS.Parser.from_file filename
  else Or_error.unimplemented "load_sygus"

let load_cctl term filename =
  if Stdlib.(=) (snd (Filename.split_extension filename)) (Some "c") then
    CCtl.C.from_file filename
  else Or_error.unimplemented "load_cctl"

let load_lts term filename =
  if Stdlib.(=) (snd (Filename.split_extension filename)) (Some "t2") then
    LTS.Parser.from_file filename
  else Or_error.unimplemented "load_t2"

let load_sat filename =
  if Stdlib.(=) (snd (Filename.split_extension filename)) (Some "dimacs") || Stdlib.(=) (snd (Filename.split_extension filename)) (Some "cnf") then
    Result.return @@ SAT.Parser.from_dimacs_file filename
  else Or_error.unimplemented "load_sat"

let load_smt filename =
  if Stdlib.(=) (snd (Filename.split_extension filename)) (Some "smt2") then
    SMT.Smtlib2.from_smt2_file filename
  else Or_error.unimplemented "load_smt"

let main filename solver problem verbose term () : unit Deferred.Or_error.t =
  let module Debug =
    Debug.Make (val (Debug.Config.(if verbose then enable else disable))) in
  problem >>=? fun problem ->
  term >>=? fun term ->
  load_solver_config problem solver >>=? fun cfg ->
  let module Config = struct let config = cfg end in
  let module Solver = Solver.Make (Config) in
  Debug.print @@ lazy (sprintf "*********** %s solving mode ************\n" @@ show_problem problem);
  match problem with
  | PSAT -> Deferred.return (load_sat filename) >>=? Solver.solve_sat
  | PSMT -> Deferred.return (load_smt filename) >>=? Solver.solve_smt
  | PPCSP -> Deferred.return (load_pcsp filename) >>=? Solver.solve_pcsp
  | PMuCLP -> Deferred.return (load_muclp filename) >>=? Solver.solve_muclp
  | PSyGuS -> Deferred.return (load_sygus term filename) >>=? Solver.solve_sygus
  | PCCTL -> Deferred.return (load_cctl term filename) >>=? Solver.solve_muclp
  | PLTSTerm -> Deferred.return (load_lts term filename) >>=? fun lts -> Solver.solve_lts (lts, LTS.Problem.Term)
  | PLTSNTerm -> Deferred.return (load_lts term filename) >>=? fun lts -> Solver.solve_lts (lts, LTS.Problem.NonTerm)
  | PLTSCTerm -> Deferred.return (load_lts term filename) >>=? fun lts -> Solver.solve_lts (lts, LTS.Problem.CondTerm)

let () = cmd main |> Command.run
