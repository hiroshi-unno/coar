open Core
open Common.Util

module Config = struct

  type t = Sequential of SequentialCoordinator.Config.t
         | Portfolio of PortfolioCoordinator.Config.t
         | PseudoParallel of PseudoParallelCoordinator.Config.t
         | Parallel of ParallelCoordinator.Config.t [@@deriving yojson]

  module type ConfigType = sig val config: t end

  let instantiate_ext_files cfg =
    let open Or_error in
    match cfg with
    | Sequential cfg ->
      SequentialCoordinator.Config.instantiate_ext_files cfg >>= fun cfg ->
      Ok (Sequential cfg)
    | Portfolio cfg ->
      PortfolioCoordinator.Config.instantiate_ext_files cfg >>= fun cfg ->
      Ok (Portfolio cfg)
    | PseudoParallel cfg ->
      PseudoParallelCoordinator.Config.instantiate_ext_files cfg >>= fun cfg ->
      Ok (PseudoParallel cfg)
    | Parallel cfg ->
      ParallelCoordinator.Config.instantiate_ext_files cfg >>= fun cfg ->
      Ok (Parallel cfg)

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
            "Invalid Coordinator Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)
end

module type CoordinatorType = sig
  val solve: PCSP.Problem.t -> (PCSP.Problem.solution * int) Core.Or_error.t
end

module Make(Config: Config.ConfigType): CoordinatorType = struct
  let config = Config.config

  module Coordinator =
    (val (match config with
         | Sequential cfg ->
           (module SequentialCoordinator.Make (struct let config = cfg end)
              : CoordinatorType)
         | Portfolio cfg ->
           (module PortfolioCoordinator.Make (struct let config = cfg end)
              : CoordinatorType)
         | PseudoParallel cfg ->
           (module PseudoParallelCoordinator.Make (struct let config = cfg end)
              : CoordinatorType)
         | Parallel cfg ->
           (module ParallelCoordinator.Make (struct let config = cfg end)
              : CoordinatorType)
       ))
  let solve = Coordinator.solve
end

let make (config : Config.t) = (module Make(struct let config = config end) : CoordinatorType)
