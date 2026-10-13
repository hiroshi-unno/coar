(** Resolver *)

open Core
open Common
open Common.Util
open PCSatCommon

(** Configuration of Resolver *)
module Config = struct
  (* [Graph] is named after the module it builds: it instantiates
     [GraphResolver], while the record it carries is [SMTResolver.Config.t] --
     [GraphResolver.Make] takes that module's [ConfigType], having none of its
     own.  [SMTResolver.ml] itself is instantiated by no configuration, so a
     probe placed there prints nothing, which does not mean that this phase
     does not run.  [SMTResolver] is kept deliberately: an SMT-based resolver may be written again, and its
     [Config] is live in the meantime. *)
  type t =
    | Disable
    | Old of OldResolver.Config.t
    | Graph of SMTResolver.Config.t
  [@@deriving yojson]

  let instantiate_ext_files = function
    | Disable -> Ok Disable
    | Old cfg ->
        let open Or_error in
        OldResolver.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Old cfg)
    | Graph cfg ->
        let open Or_error in
        SMTResolver.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (Graph cfg)

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "Resolver"
    let instantiate = instantiate_ext_files
  end)

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
    | Graph cfg -> cfg.verbose
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
         | Graph cfg ->
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
