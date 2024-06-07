(** Resolver *)

open Core
open Common
open Common.Util
open PCSatCommon

(** Configuration of Resolver *)
module Config = struct
  type t = Disable | Old of OldResolver.Config.t | SMT of SMTResolver.Config.t
  [@@deriving yojson]

  let instantiate_ext_files = function
    | Disable -> Ok Disable
    | Old cfg ->
        let open Or_error in
        OldResolver.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Old cfg)
    | SMT cfg ->
        let open Or_error in
        SMTResolver.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (SMT cfg)

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid Resolver Configuration (%s): %s" filename msg)

  module type ConfigType = sig
    val config : t
  end
end

module type ResolverType = sig
  val run_phase : int -> State.u -> State.u Or_error.t
end

module Make
    (RLCfg : RLConfig.ConfigType)
    (Config : Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) : ResolverType = struct
  let config = Config.config
  let id = PCSP.Problem.id_of APCSP.problem
  let _messenger = PCSP.Problem.messenger_of APCSP.problem

  let verbose =
    match config with
    | Old cfg -> cfg.verbose
    | SMT cfg -> cfg.verbose
    | Disable -> false

  module Debug =
    Debug.Make ((val Debug.Config.(if verbose then enable else disable)))

  let _ = Debug.set_id id

  module Resolver =
    (val match config with
         | Disable ->
             (module struct
               let run_phase _iters e = Ok e
             end : ResolverType)
         | Old cfg ->
             (module OldResolver.Make
                       (struct
                         let config = cfg
                       end)
                       (APCSP))
         | SMT cfg ->
             (module GraphResolver.Make
                       (struct
                         let config = cfg
                       end)
                       (APCSP))
        : ResolverType)

  let run_phase = Resolver.run_phase

  let run_phase iters e =
    if RLCfg.config.enable then (
      if RLCfg.config.show_elapsed_time then (
        RLConfig.lock ();
        Debug.print_stdout @@ lazy "begin resolver";
        RLConfig.unlock ());
      let tm = Timer.make () in
      let res = run_phase iters e in
      if RLCfg.config.show_elapsed_time then (
        RLConfig.lock ();
        Debug.print_stdout @@ lazy (sprintf "end resolver: %f" (tm ()));
        RLConfig.unlock ());
      res)
    else run_phase iters e
end

let make rl_config config problem =
  (module Make
            (struct
              let config = rl_config
            end)
            (struct
              let config = config
            end)
            (struct
              let problem = problem
            end) : ResolverType)
