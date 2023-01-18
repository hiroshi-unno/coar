open Core
open CoAR
open Common

type problem =
  | PSAT (** SAT Solving *)
  | PSMT (** SMT Solving *)
  | PPCSP (** pfwnCSP Satifiability Checking *)
  | PSyGuS (** SyGyS Inv/CLIA *)
  | PCHCMax (** CHC Maximization *)
  | PMuCLP (** muCLP Validity Checking *)
  | PCLTL (** LTL Verification of C Programs *)
  | PCCTL (** CTL Verification of C Programs *)
  | PLTSSafe (** Safety Verification of Labeled Transition Systems *)
  | PLTSNSafe (** Non-Safety Verification of Labeled Transition Systems *)
  | PLTSTerm (** Termination Verification of Labeled Transition Systems *)
  | PLTSNTerm (** Non-Termination Verification of Labeled Transition Systems *)
  | PLTSCTerm (** Interactive Conditional (Non-)Termination Analysis of Labeled Transition Systems *)
  | PLTSMuCal (** Modal mu-Calculus Model Checking of Labeled Transition Systems *)
  | PLTSRel (** Relational Verification of Labeled Transition Systems *)
  | POCaml (** Refinement Type Inference of OCaml Programs *)
[@@deriving show]

let problem =
  Command.Arg_type.create (fun problem ->
      let open Or_error in
      problem |> String.lowercase |> function
      | "sat"           -> return PSAT
      | "smt"           -> return PSMT
      | "chc"
      | "pcsp"
      | "pfwcsp"        -> return PPCSP
      | "sygus"         -> return PSyGuS
      | "chcmax"        -> return PCHCMax
      | "muclp"         -> return PMuCLP
      | "cltl"
      | "c-ltl"         -> return PCLTL
      | "cctl"
      | "c-ctl"         -> return PCCTL
      | "ltssafe"
      | "lts-safe"      -> return PLTSSafe
      | "ltsnsafe"
      | "lts-nsafe"     -> return PLTSNSafe
      | "ltsterm"
      | "lts-term"      -> return PLTSTerm
      | "ltsnterm"
      | "lts-nterm"     -> return PLTSNTerm
      | "ltscterm"
      | "lts-cterm"     -> return PLTSCTerm
      | "ltsmucal"
      | "lts-mucal"     -> return PLTSMuCal
      | "ltsrel"
      | "lts-rel"       -> return PLTSRel
      | "ml"            -> return POCaml
      | _ -> failwith (Printf.sprintf "invalid problem: %s" problem))

let default_config_file = "./config/solver/muval_prove_tb.json"

let cmd =
  Command.basic_spec
    ~summary:""
    Command.Spec.(
      empty
      +> anon ("filename" %: string)
      +> flag "--config" (optional_with_default default_config_file string)
        ~aliases:["-c"]
        ~doc:(Printf.sprintf
                "<config> specify solver configuration file (default:%s)"
                default_config_file)
      +> flag "--problem" (optional_with_default (Or_error.return PMuCLP) problem)
        ~aliases:["-p"]
        ~doc:"choose problem [SAT/SMT/CHC/pCSP/pfwCSP/CHCMax/muCLP/SyGuS/CLTL/CCTL/LTSsafe/LTSnsafe/LTSterm/LTSnterm/LTScterm/LTSmucal/LTSrel/TypeInf/TypeOpt] (default: muCLP)"
      +> flag "--verbose" no_arg (* is this option obsolete? *)
        ~aliases:["-v"] ~doc:"enable verbose mode")

let load_solver_config prblm solver =
  let open Or_error in
  match Solver.Config.load_config solver with
  | Ok cfg ->
    begin
      match cfg with
      | Solver.Config.MuVal _ when Stdlib.(=) prblm PLTSCTerm ->
        Ok cfg
      | Solver.Config.MuVal _
        when Stdlib.(=) prblm PPCSP || Stdlib.(=) prblm PSyGuS || Stdlib.(=) prblm PMuCLP ||
             Stdlib.(=) prblm PLTSSafe || Stdlib.(=) prblm PLTSNSafe ||
             Stdlib.(=) prblm PLTSTerm || Stdlib.(=) prblm PLTSNTerm || Stdlib.(=) prblm PLTSMuCal ||
             Stdlib.(=) prblm PCLTL || Stdlib.(=) prblm PCCTL ->
        Ok cfg
      | Solver.Config.PCSat _ | Solver.Config.SPACER _ | Solver.Config.Hoice _
        when Stdlib.(=) prblm PPCSP || Stdlib.(=) prblm PSyGuS ->
        Ok cfg
      | Solver.Config.RCaml _
        when Stdlib.(=) prblm POCaml ->
        Ok cfg
      | Solver.Config.Minisat _ | Solver.Config.Z3Sat _
        when Stdlib.(=) prblm PSAT ->
        Ok cfg
      | Solver.Config.Z3Smt _
        when Stdlib.(=) prblm PSMT ->
        Ok cfg
      | Solver.Config.Printer _
        when Stdlib.(=) prblm PPCSP || Stdlib.(=) prblm PSyGuS || Stdlib.(=) prblm PMuCLP ||
             Stdlib.(=) prblm PLTSSafe || Stdlib.(=) prblm PLTSNSafe ||
             Stdlib.(=) prblm PLTSTerm || Stdlib.(=) prblm PLTSNTerm || Stdlib.(=) prblm PLTSMuCal ||
             Stdlib.(=) prblm PCLTL || Stdlib.(=) prblm PCCTL ->
        Ok cfg
      | Solver.Config.OptPCSat _
        when Stdlib.(=) prblm PCHCMax  ->
        Ok cfg
      | _ ->
        failwith
        @@ Printf.sprintf "The specified solver does not support the problem %s"
          (show_problem prblm)
    end
  | Error err -> Error err

let load_muclp filename =
  match snd (Filename.split_extension filename) with
  | Some "hes" -> MuCLP.Parser.from_file filename
  | _ -> Or_error.unimplemented "load_muclp"

let load_pcsp filename =
  match snd (Filename.split_extension filename) with
  | Some "smt2" -> PCSP.Parser.from_smt2_file ~skolem_pred:true filename
  | Some "clp" -> PCSP.Parser.from_clp_file filename
  | _ -> Or_error.unimplemented "load_pcsp"

let load_chcmax filename = let open Result.Monad_infix in
  match snd (Filename.split_extension filename) with
  | Some "smt2" -> load_pcsp filename >>= (fun pcsp -> Ok (CHCOpt.Problem.of_pcsp pcsp))
  | _ -> Or_error.unimplemented "load_chcmax"

let load_sygus filename =
  match snd (Filename.split_extension filename) with
  | Some "sl" -> SyGuS.Parser.from_file filename
  | _ -> Or_error.unimplemented "load_sygus"

let load_cltl filename =
  match snd (Filename.split_extension filename) with
  | Some "c" -> C.Parser.from_cltl_file filename
  | _ -> Or_error.unimplemented "load_cltl"

let load_cctl filename =
  match snd (Filename.split_extension filename) with
  | Some "c" -> C.Parser.from_cctl_file filename
  | _ -> Or_error.unimplemented "load_cctl"

let load_lts filename =
  match snd (Filename.split_extension filename) with
  | Some "t2" -> LTS.Parser.from_file filename
  | _ -> Or_error.unimplemented "load_lts"

let load_sat filename =
  match snd (Filename.split_extension filename) with
  | Some ("dimacs" | "cnf") -> Ok (SAT.Parser.from_dimacs_file filename)
  | _ -> Or_error.unimplemented "load_sat"

let load_smt filename =
  match snd (Filename.split_extension filename) with
  | Some "smt2" -> SMT.Smtlib2.from_smt2_file filename
  | _ -> Or_error.unimplemented "load_smt"

let main filename solver problem verbose () =
  let open Or_error.Monad_infix in
  let module Debug =
    Debug.Make (val (Debug.Config.(if verbose then enable else disable))) in
  ok_exn
    (problem >>= fun problem ->
     load_solver_config problem solver >>= fun cfg ->
     let module Config = struct let config = cfg end in
     let module Solver = Solver.Make (Config) in
     Debug.print @@ lazy (sprintf "*********** %s solving mode ************\n" @@ show_problem problem);
     match problem with
     | PSAT -> load_sat filename >>= Solver.solve_sat
     | PSMT -> load_smt filename >>= Solver.solve_smt
     | PPCSP -> load_pcsp filename >>= Solver.solve_pcsp ~filename:(Some filename)
     | PSyGuS -> load_sygus filename >>= Solver.solve_sygus ~filename:(Some filename)
     | PCHCMax -> load_chcmax filename >>= Solver.solve_chcopt ~filename:(Some filename)
     | PMuCLP -> load_muclp filename >>= Solver.solve_muclp
     | PCLTL -> load_cltl filename >>= Solver.solve_muclp
     | PCCTL -> load_cctl filename >>= Solver.solve_muclp
     | PLTSSafe -> load_lts filename >>= fun lts -> Solver.solve_lts (lts, LTS.Problem.Safe)
     | PLTSNSafe -> load_lts filename >>= fun lts -> Solver.solve_lts (lts, LTS.Problem.NonSafe)
     | PLTSTerm -> load_lts filename >>= fun lts -> Solver.solve_lts (lts, LTS.Problem.Term)
     | PLTSNTerm -> load_lts filename >>= fun lts -> Solver.solve_lts (lts, LTS.Problem.NonTerm)
     | PLTSCTerm -> load_lts filename >>= fun lts -> Solver.solve_lts (lts, LTS.Problem.CondTerm)
     | PLTSMuCal -> load_lts filename >>= fun lts -> Solver.solve_lts (lts, LTS.Problem.MuCal)
     | PLTSRel -> load_lts filename >>= fun lts -> Solver.solve_lts (lts, LTS.Problem.Rel)
     | POCaml -> Solver.solve_ml filename)

let () = Command_unix.run @@ cmd main
