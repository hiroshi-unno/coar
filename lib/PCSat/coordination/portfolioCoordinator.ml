open Core
open Async
open Common.Util
open Validation
open Resolution
open Synthesis

module Config = struct
  type phase = V of Validator.Config.t ext_file
             | R of Resolver.Config.t ext_file
             | S of Synthesizer.Config.t ext_file
             | P of phase * phase [@@deriving yojson]
  type t = { phase_list : phase list } [@@deriving yojson]

  let instantiate_ext_files _cfg =
    Or_error.unimplemented "PortfolioCoordinator.instantiate_ext_files"

  let load_ext_file = function
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
            "Invalid PortfolioCoordinator Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)

  module type ConfigType = sig val config : t end
end

module Make(Cfg: Config.ConfigType) = struct
  let solve _pcsp = Or_error.unimplemented "PortfolioCoordinator.solve"
end