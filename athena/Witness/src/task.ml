(* An SV-COMP task definition (the .yml beside a benchmark, format 2.0 of
   https://gitlab.com/sosy-lab/benchmarking/task-definition-format): only
   options.data_model is read. *)

(* The data model the task states: [Ok None] when it states none. *)
let data_model_of_yaml (v : Yaml.value) =
  let member k = function `O fields -> List.assoc_opt k fields | _ -> None in
  match Option.bind (member "options" v) (member "data_model") with
  | None -> Ok None
  | Some (`String "ILP32") -> Ok (Some Witness.ILP32)
  | Some (`String "LP64") -> Ok (Some Witness.LP64)
  | Some _ -> Error "options.data_model is neither ILP32 nor LP64"

let read_data_model path =
  match In_channel.with_open_bin path In_channel.input_all with
  | exception Sys_error e -> Error e
  | text -> (
      match Yaml.of_string text with
      | Error (`Msg m) -> Error (path ^ ": " ^ m)
      | Ok v -> Result.map_error (fun m -> path ^ ": " ^ m) (data_model_of_yaml v))
