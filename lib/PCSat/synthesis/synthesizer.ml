open Core
open Common.Util
open PCSatCommon

module Config = struct
  type t =
    | Template of TBSynthesizer.Config.t (** configuration for TBSynthesizer *)
    | Classification of CBSynthesizer.Config.t (** configuration for CBSynthesizers [DT/GSC/SCQM/LTB] *)
    | PredicateAbstraction of PASynthesizer.Config.t (** configuration for PASynthesizers [PASAT/PASID] *) [@@ deriving yojson]

  let rec instantiate_ext_files = function
    | Template cfg ->
      let open Or_error in
      TBSynthesizer.Config.instantiate_ext_files cfg >>= fun cfg ->
      Ok (Template cfg)
    | Classification cfg ->
      let open Or_error in
      CBSynthesizer.Config.instantiate_ext_files cfg >>= fun cfg ->
      Ok (Classification cfg)
    | PredicateAbstraction cfg ->
      let open Or_error in
      PASynthesizer.Config.instantiate_ext_files cfg >>= fun cfg ->
      Ok (PredicateAbstraction cfg)
  and load_ext_file = function
    | ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename)
        >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x ->
          instantiate_ext_files x >>= fun x ->
          Ok (ExtFile.Instance x)
        | Error msg ->
          error_string
          @@ Printf.sprintf
            "Invalid Synthesizer Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (ExtFile.Instance x)

  module type ConfigType = sig val config : t end
end

module type SynthesizerType = sig
  val run_phase : State.u -> State.s Or_error.t
end

module Make (Cfg: Config.ConfigType) (Problem: PCSP.Problem.ProblemType): SynthesizerType = struct
  let config = Cfg.config

  module Synthesizer =
    (val (match config with
         | Config.Template cfg ->
           (module TBSynthesizer.Make (struct let config = cfg end) (Problem)
              : SynthesizerType)
         | Classification cfg ->
           (module CBSynthesizer.Make (struct let config = cfg end) (Problem)
              : SynthesizerType)
         | PredicateAbstraction cfg -> 
           (module PASynthesizer.Make (struct let config = cfg end) (Problem)
              : SynthesizerType)
       ))

  let run_phase = Synthesizer.run_phase
end

let make config problem =
  (module Make(struct let config = config end) (struct let problem = problem end) : SynthesizerType)
