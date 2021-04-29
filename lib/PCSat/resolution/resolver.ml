(** Resolver *)

open Core
open Common.Util
open PCSatCommon

(** Configuration of Resolver *)
module Config = struct
  type t = Disable
         | Old of OldResolver.Config.t
         | SMT of SMTResolver.Config.t [@@ deriving yojson]

  let instantiate_ext_files = function
    | Disable -> Ok Disable
    | Old cfg ->
      let open Or_error in
      OldResolver.Config.instantiate_ext_files cfg >>= fun cfg ->
      Ok (Old cfg)
    | SMT cfg ->
      let open Or_error in
      SMTResolver.Config.instantiate_ext_files cfg >>= fun cfg ->
      Ok (SMT cfg)

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
            "Invalid Resolver Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)

  module type ConfigType = sig val config: t end
end

module type ResolverType = sig
  val run_phase : State.u -> State.u Or_error.t
end

module Make (Config: Config.ConfigType) (Problem: PCSP.Problem.ProblemType)
  : ResolverType = struct
  let config = Config.config

  module Resolver =
    (val (match config with
         | Disable -> (module struct let run_phase e = Ok e end  : ResolverType)
         | Old cfg -> (module OldResolver.Make (struct let config = cfg end) (Problem))
         | SMT cfg -> (module SMTResolver.Make (struct let config = cfg end) (Problem)))
       : ResolverType)

  let run_phase = Resolver.run_phase
end

let make config problem
  = (module Make(struct let config = config end)
        (struct let problem = problem end) : ResolverType)
