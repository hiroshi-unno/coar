type property = Unreach_call | Termination
type answer = Problem of MuCLP.Problem.t * LLVMWitness.Cmap.t option | Unknown of string

let available = true

let translate ?(witness = false) ?(overrides = []) ~bv_mode ~property ~config path =
  let open Core in
  let open Or_error.Monad_infix in
  (match config with
  | None -> Result.map_error ~f:Error.of_string (LLVMFront.Config.of_members overrides)
  | Some file -> Result.map_error ~f:Error.of_string (LLVMFront.Config.load ~overrides file))
  >>| (fun (config : LLVMFront.Config.t) -> if witness then { config with witness = true } else config)
  >>= fun config ->
  let property : LLVMFront.Frontend.property =
    match property with
    | Unreach_call -> Unreach_call
    | Termination -> Termination
  in
  match LLVMFront.Frontend.run ~bv_mode ~property ~config path with
  | Ok (Problem (p, map)) -> Ok (Problem (p, map))
  | Ok (Unknown reason) -> Ok (Unknown reason)
  | Error message -> Or_error.error_string message
