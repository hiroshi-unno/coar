open Core
open Common.Util
open PCSatCommon

module Config = struct
  type t = { output_iteration : bool; sygus_comp : bool } [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid SolPrinter Configuration (%s): %s" filename msg)
end

module type SolPrinterType = sig
  val print : State.output -> unit
end

module Make (Config : Config.ConfigType) = struct
  let config = Config.config

  let print (solution, info) =
    Out_channel.print_endline
    @@
    if config.sygus_comp then PCSP.Problem.str_of_sygus_solution solution
    else if config.output_iteration then
      sprintf "%s,%d"
        (PCSP.Problem.str_of_solution solution)
        info.State.num_cegis_iters
    else PCSP.Problem.str_of_solution solution;
    Out_channel.flush stdout
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolPrinterType)
