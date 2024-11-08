open Core
open CoAR
open Common
open Common.Combinator

type problem =
  | PSAT  (** SAT Solving *)
  | PSMT  (** SMT Solving *)
  | PHOMC  (** Higher-Order Model Checking *)
  | PSyGuS  (** SyGyS Inv/CLIA *)
  | PPCSP  (** pfwnCSP Satifiability Checking *)
  | PCHCMax  (** CHC Maximization *)
  | PMuCLP  (** muCLP Validity Checking *)
  | PMuCLPInter  (** Interactive Conditional muCLP Validity Checking *)
  | PCLTL  (** LTL Verification of C Programs *)
  | PCCTL  (** CTL Verification of C Programs *)
  | PLTSSafe  (** Safety Verification of Labeled Transition Systems *)
  | PLTSNSafe  (** Non-Safety Verification of Labeled Transition Systems *)
  | PLTSTerm  (** Termination Verification of Labeled Transition Systems *)
  | PLTSNTerm  (** Non-Termination Verification of Labeled Transition Systems *)
  | PLTSMuCal
      (** Modal mu-Calculus Model Checking of Labeled Transition Systems *)
  | PLTSRel  (** Relational Verification of Labeled Transition Systems *)
  | PLTSTermInter
      (** Interactive Conditional (Non-)Termination Analysis of Labeled Transition Systems *)
  | PPLTSTerm
      (** Termination Verification of Pushdown Labeled Transition Systems *)
  | PPLTSNTerm
      (** Non-Termination Verification of Pushdown Labeled Transition Systems *)
  | POCaml  (** Refinement Type Inference of OCaml Programs *)
[@@deriving show]

let problem =
  Command.Arg_type.create (fun problem ->
      let open Or_error in
      problem |> String.lowercase |> function
      | "sat" -> return PSAT
      | "smt" -> return PSMT
      | "homc" -> return PHOMC
      | "sygus" -> return PSyGuS
      | "chc" | "pcsp" | "pfwcsp" | "pfwncsp" -> return PPCSP
      | "chcmax" -> return PCHCMax
      | "muclp" -> return PMuCLP
      | "muclpinter" | "muclp-inter" -> return PMuCLPInter
      | "cltl" | "c-ltl" -> return PCLTL
      | "cctl" | "c-ctl" -> return PCCTL
      | "ltssafe" | "lts-safe" -> return PLTSSafe
      | "ltsnsafe" | "lts-nsafe" -> return PLTSNSafe
      | "ltsterm" | "lts-term" -> return PLTSTerm
      | "ltsnterm" | "lts-nterm" -> return PLTSNTerm
      | "ltsmucal" | "lts-mucal" -> return PLTSMuCal
      | "ltsrel" | "lts-rel" -> return PLTSRel
      | "ltsterminter" | "lts-term-inter" -> return PLTSTermInter
      | "pltsterm" | "plts-term" -> return PPLTSTerm
      | "pltsnterm" | "plts-nterm" -> return PPLTSNTerm
      | "ml" -> return POCaml
      | _ -> failwith (sprintf "invalid problem: %s" problem))

let default_config_file = "./config/solver/muval_parallel_exc_tbq_ar.json"

let cmd =
  Command.basic_spec ~summary:""
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
             "choose problem \
              [SAT/SMT/HOMC/SyGuS/CHC/pCSP/pfwCSP/pfwnCSP/CHCMax/muCLP/muCLPInter/CLTL/CCTL/LTSsafe/LTSnsafe/LTSterm/LTSnterm/LTSmucal/LTSrel/LTStermInter/PLTSterm/PLTSnterm/ML] \
              (default: muCLP)"
      +> flag "--verbose" no_arg (* this option is obsolete *)
           ~aliases:[ "-v" ] ~doc:"enable verbose mode")

let load_solver_config prblm solver =
  let open Solver.Config in
  match load_config solver with
  | Error err -> Error err
  | Ok cfg -> (
      Or_error.return
      @@
      match cfg with
      | MuVal _ when Stdlib.(prblm = PMuCLPInter || prblm = PLTSTermInter) ->
          cfg
      | (MuVal _ | MuCyc _ | Printer _)
        when Stdlib.(
               prblm = PSyGuS || prblm = PPCSP || prblm = PMuCLP
               || prblm = PCLTL || prblm = PCCTL || prblm = PLTSSafe
               || prblm = PLTSNSafe || prblm = PLTSTerm || prblm = PLTSNTerm
               || prblm = PLTSMuCal || prblm = PLTSRel || prblm = PPLTSTerm
               || prblm = PPLTSNTerm) ->
          cfg
      | (PCSat _ | SPACER _ | Hoice _)
        when Stdlib.(prblm = PPCSP || prblm = PSyGuS) ->
          cfg
      | OptPCSat _ when Stdlib.(prblm = PCHCMax) -> cfg
      | (RCaml _ | EffCaml _) when Stdlib.(prblm = POCaml) -> cfg
      | (MiniSat _ | Z3Sat _) when Stdlib.(prblm = PSAT) -> cfg
      | Z3Smt _ when Stdlib.(prblm = PSMT) -> cfg
      | (TRecS _ | HorSat2 _) when Stdlib.(prblm = PHOMC) -> cfg
      | _ ->
          failwith
          @@ sprintf "The specified solver does not support the problem %s"
               (show_problem prblm))

let load_sat filename =
  match snd (Filename.split_extension filename) with
  | Some ("dimacs" | "cnf") -> Ok (SAT.Problem.from_dimacs_file filename)
  | Some "gz" (*ToDo*) -> Ok (SAT.Problem.from_gzipped_dimacs_file filename)
  | _ -> Or_error.unimplemented "load_sat"

let load_smt ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "smt2" ->
      Ok (SMT.Smtlib2.from_smt2_file ~print ~inline:true (*ToDo*) filename)
  | _ -> Or_error.unimplemented "load_smt"

let load_homc ~print filename =
  match snd (Filename.split_extension filename) with
  | Some ("hrs" | "hors") -> Ok (HOMC.Problem.from_hors_file ~print filename)
  | Some ("hmtt" | "ehmtt") -> Ok (HOMC.Problem.from_ehmtt_file ~print filename)
  | _ -> Or_error.unimplemented "load_homc"

let load_pcsp ~print filename =
  match Filename.split_extension filename with
  | _, Some "smt2" ->
      Ok
        (PCSP.Parser.from_smt2_file ~print ~inline:true (*ToDo*)
           ~skolem_pred:true filename)
  | fn, Some "gz"
    when match Filename.split_extension fn with
         | _, Some "smt2" -> true
         | _ -> false ->
      Ok
        (PCSP.Parser.from_gzipped_smt2_file ~print ~inline:true (*ToDo*)
           ~skolem_pred:true filename)
  | _, Some "clp" -> Ok (PCSP.Parser.from_clp_file filename)
  | _ -> Or_error.unimplemented "load_pcsp"

let load_sygus filename =
  match snd (Filename.split_extension filename) with
  | Some "sl" -> SyGuS.Parser.from_file filename
  | _ -> Or_error.unimplemented "load_sygus"

let load_chcmax ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "smt2" ->
      Result.Monad_infix.(
        load_pcsp ~print filename >>= (CHCOpt.Problem.of_pcsp >> Or_error.return))
  | _ -> Or_error.unimplemented "load_chcmax"

let load_muclp ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "hes" -> MuCLP.Parser.muclp_from_file ~print filename
  | _ -> Or_error.unimplemented "load_muclp"

let load_cltl ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "c" -> C.Parser.from_cltl_file ~print filename
  | _ -> Or_error.unimplemented "load_cltl"

let load_cctl ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "c" -> C.Parser.from_cctl_file ~print filename
  | _ -> Or_error.unimplemented "load_cctl"

let load_lts filename =
  match snd (Filename.split_extension filename) with
  | Some "t2" -> LTS.Parser.from_file filename
  | _ -> Or_error.unimplemented "load_lts"

let load_plts ~print filename =
  match snd (Filename.split_extension filename) with
  | Some "smt2" -> PLTS.Parser.from_file ~print filename
  | _ -> Or_error.unimplemented "load_plts"

let main filename solver problem verbose () =
  let open Or_error.Monad_infix in
  let module Debug =
    Debug.Make ((val Debug.Config.(if verbose then enable else disable))) in
  ok_exn
    ( problem >>= fun problem ->
      load_solver_config problem solver >>= fun cfg ->
      let module Config = struct
        let config = cfg
      end in
      let module Solver = Solver.Make (Config) in
      Debug.print
      @@ lazy
           (sprintf "*********** %s solving mode ************\n"
           @@ show_problem problem);
      match problem with
      | PSAT -> load_sat filename >>= Solver.solve_sat
      | PSMT -> load_smt ~print:Debug.print filename >>= Solver.solve_smt
      | PHOMC -> load_homc ~print:Debug.print filename >>= Solver.solve_homc
      | PSyGuS ->
          load_sygus filename >>= Solver.solve_sygus ~filename:(Some filename)
      | PPCSP ->
          load_pcsp ~print:Debug.print filename
          >>= Solver.solve_pcsp ~filename:(Some filename)
      | PCHCMax ->
          load_chcmax ~print:Debug.print filename
          >>= Solver.solve_chcopt ~filename:(Some filename)
      | PMuCLP -> load_muclp ~print:Debug.print filename >>= Solver.solve_muclp
      | PMuCLPInter ->
          load_muclp ~print:Debug.print filename
          >>= Solver.solve_muclp_interactive
      | PCLTL -> load_cltl ~print:Debug.print filename >>= Solver.solve_muclp
      | PCCTL -> load_cctl ~print:Debug.print filename >>= Solver.solve_muclp
      | PLTSSafe ->
          load_lts filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.Safe)
      | PLTSNSafe ->
          load_lts filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.NonSafe)
      | PLTSTerm ->
          load_lts filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.Term)
      | PLTSNTerm ->
          load_lts filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.NonTerm)
      | PLTSMuCal ->
          load_lts filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.MuCal)
      | PLTSRel ->
          load_lts filename >>= fun lts ->
          Solver.solve_lts ~print:Debug.print (lts, LTS.Problem.Rel)
      | PLTSTermInter ->
          load_lts filename >>= fun lts ->
          Solver.solve_lts_interactive ~print:Debug.print lts
      | PPLTSTerm ->
          load_plts ~print:Debug.print filename >>= fun plts ->
          Solver.solve_plts ~print:Debug.print (plts, PLTS.Problem.Term)
      | PPLTSNTerm ->
          load_plts ~print:Debug.print filename >>= fun plts ->
          Solver.solve_plts ~print:Debug.print (plts, PLTS.Problem.NonTerm)
      | POCaml -> Solver.solve_ml filename )

let () = Command_unix.run @@ cmd main
