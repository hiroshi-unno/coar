open Core
open Common.Util
open PCSatCommon
open Coordination
open Preprocessing

module type SolverType = sig
  val solve :
    ?bpvs:Ast.Ident.tvar Set.Poly.t ->
    ?filename:string option ->
    ?print_sol:bool ->
    PCSP.Problem.t ->
    State.output Or_error.t

  val preprocess :
    ?bpvs:Ast.Ident.tvar Set.Poly.t ->
    PCSP.Problem.t ->
    PCSP.Problem.t Or_error.t

  val reset : unit -> unit
  val push : unit -> unit
  val pop : unit -> unit
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config
  let context = Context.create ()

  let preprocessor =
    let open Or_error in
    ExtFile.unwrap config.preprocessor >>= fun cfg -> Ok (Preprocessor.make cfg)

  let coordinator =
    let open Or_error in
    ExtFile.unwrap config.coordinator >>= fun cfg ->
    Ok (Coordinator.make cfg context)

  let sol_printer =
    let open Or_error in
    ExtFile.unwrap config.sol_printer >>= fun cfg -> Ok (SolPrinter.make cfg)

  let solve ?(bpvs = Set.Poly.empty) ?(filename = None) ?(print_sol = false)
      pcsp =
    let open Or_error in
    sol_printer >>= fun (module SolPrinter : SolPrinter.SolPrinterType) ->
    preprocessor
    >>= fun (module Preprocessor : Preprocessor.PreprocessorType) ->
    coordinator >>= fun (module Coordinator : Coordinator.CoordinatorType) ->
    let pcsps =
      if config.solve_each_query then PCSP.Problem.divide pcsp else [ pcsp ]
    in
    let oracle =
      if config.load_oracle_sol then
        Option.(
          filename >>= fun filename ->
          let basename =
            fst @@ Filename.split_extension @@ snd @@ Filename.split filename
          in
          let filename = "./" ^ basename ^ ".sol" in
          match SyGuS.Parser.solution_from_file filename with
          | Ok defs ->
              Some
                ( Map.Poly.empty,
                  Set.Poly.of_list @@ List.map defs ~f:Ast.CandSolOld.of_fundef
                )
          | Error _ -> failwith @@ sprintf "failed to load %s" filename)
      else None
    in
    List.map pcsps ~f:(Preprocessor.solve ~bpvs ~oracle Coordinator.solve)
    |> Or_error.combine_errors
    >>= fun res ->
    let sols, infos = List.unzip res in
    let solution = PCSP.Problem.merge_sols pcsp sols in
    let info = State.merge_infos infos in
    if print_sol then SolPrinter.print (solution, info);
    Or_error.return (solution, info)

  let preprocess ?(bpvs = Set.Poly.empty) pcsp =
    let open Or_error in
    preprocessor
    >>= fun (module Preprocessor : Preprocessor.PreprocessorType) ->
    Or_error.return (snd @@ Preprocessor.preprocess ~bpvs pcsp)

  let reset () = Context.reset context
  let push () = Context.push context
  let pop () = ignore @@ Context.pop context
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
