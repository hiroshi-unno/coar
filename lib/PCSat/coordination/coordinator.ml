open Core
open Common
open Common.Ext
open Common.Util
open PCSatCommon
open Validation
open Resolution
open Synthesis
open Labeling

module Config = struct
  (** resolution and validation must be followed by Labeler *)
  type phase =
    | V of Validator.Config.t ext_file
    | R of Resolver.Config.t ext_file
    | S of Synthesizer.Config.t ext_file
    | L of Labeler.Config.t ext_file
    | P of phase * phase
  [@@deriving yojson]

  type t = {
    phase_list : phase list;
    rl_config : RLConfig.t ext_file;
    verbose : bool;
  }
  [@@deriving yojson]

  let rec load_ext_phase =
    let open Or_error in
    function
    | V cfg -> Validator.Config.load_ext_file cfg >>= fun cfg -> Ok (V cfg)
    | S cfg -> Synthesizer.Config.load_ext_file cfg >>= fun cfg -> Ok (S cfg)
    | R cfg -> Resolver.Config.load_ext_file cfg >>= fun cfg -> Ok (R cfg)
    | L cfg -> Labeler.Config.load_ext_file cfg >>= fun cfg -> Ok (L cfg)
    | P (phase1, phase2) ->
        load_ext_phase phase1 >>= fun phase1 ->
        load_ext_phase phase2 >>= fun phase2 -> Ok (P (phase1, phase2))

  let instantiate_ext_files cfg =
    let open Or_error in
    List.map ~f:load_ext_phase cfg.phase_list |> Result.all
    >>= fun phase_list ->
    RLConfig.load_ext_file cfg.rl_config >>= fun rl_config ->
    Ok { cfg with phase_list; rl_config }

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid Coordinator Configuration (%s): %s" filename msg
        )

  let str_of_phase = function
    | V _ -> "Validation"
    | S _ -> "Synthesis"
    | R _ -> "Resolution"
    | L _ -> "Labeling"
    | P _ -> "Parallel"

  module type ConfigType = sig
    val config : t
  end
end

module type CoordinatorType = sig
  val solve :
    ?oracle:PCSP.Problem.oracle -> PCSP.Problem.t -> State.output Or_error.t
end

module Make (Cfg : Config.ConfigType) (MContext : Context.ContextType) :
  CoordinatorType = struct
  module type MUS = sig
    val run_phase : int -> State.u -> State.s Or_error.t
  end

  module type MUU = sig
    val run_phase : int -> State.u -> State.u Or_error.t
  end

  module type MSU = sig
    val run_phase : int -> State.s -> State.u Or_error.t
  end

  type phase_type =
    | US of (module MUS)
    | UU of (module MUU)
    | SU of (module MSU)

  type state_type = S of State.s | U of State.u

  let str_of_phase_type = function US _ -> "US" | UU _ -> "UU" | SU _ -> "SU"
  let str_of_state_type = function S _ -> "S" | U _ -> "U"
  let id = ref None
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let build_phase pcsp rl_config phase =
    let open Config in
    let open Or_error in
    match phase with
    | V cfg ->
        ExtFile.unwrap cfg >>= fun cfg ->
        Ok (SU (Validator.make rl_config cfg pcsp))
    | R cfg ->
        ExtFile.unwrap cfg >>= fun cfg ->
        Ok (UU (Resolver.make rl_config cfg pcsp))
    | S cfg ->
        ExtFile.unwrap cfg >>= fun cfg ->
        Ok (US (Synthesizer.make rl_config cfg pcsp))
    | L cfg ->
        ExtFile.unwrap cfg >>= fun cfg ->
        Ok (UU (Labeler.make rl_config cfg pcsp))
    | P (_phase1, _phase2) -> Or_error.unimplemented "build_phase"

  let last_version_space = ref None

  let str_of_phase_list n =
    config.phase_list
    |> String.concat_mapi_list ~sep:" >> " ~f:(fun i phase ->
           Config.str_of_phase phase |> if i = n then String.bracket else Fn.id)

  let print_status iter n =
    let header =
      "************** current phase of "
      ^ Ordinal.string_of (Ordinal.make iter)
      ^ " iteration **************"
    in
    Debug.print @@ lazy (header ^ "\n");
    Debug.print @@ lazy (str_of_phase_list n ^ "\n");
    Debug.print @@ lazy (String.init (String.length header) ~f:(fun _ -> '*'))

  let app_phase messenger iters i e phase =
    let open Or_error in
    e >>= fun e ->
    Common.Messenger.receive_request messenger !id;
    match (e, phase) with
    | U e, US (module Phase : MUS) ->
        if Fn.non State.is_end e then print_status iters i;
        Phase.run_phase iters e >>= fun e -> Ok (S e)
    | U e, UU (module Phase : MUU) ->
        if Fn.non State.is_end e then print_status iters i;
        Phase.run_phase iters e >>= fun e -> Ok (U e)
    | S e, SU (module Phase : MSU) ->
        if Fn.non State.is_end e then print_status iters i;
        Phase.run_phase iters e >>= fun e -> Ok (U e)
    | _ ->
        Error
          (Error.of_thunk (fun () ->
               sprintf
                 ("phase type error: apply %s phase to %s state.\n"
                ^^ "coordinator configuration may be broken\n"
                ^^ "Hint:\n e.g., any validator follows only synthesizer")
                 (str_of_phase_type phase) (str_of_state_type e)))

  let update_context_version () =
    match !last_version_space with
    | None -> ()
    | Some vs -> (
        match MContext.context.version with
        | None -> assert false
        | Some version ->
            Context.set_version MContext.context
            @@ Context.version_of version vs)

  let rec main_loop messenger (f : int -> State.u -> state_type Or_error.t)
      num_iters e =
    let open Or_error in
    update_context_version ();
    if config.verbose then Context.show_graph ~id:!id MContext.context.version;
    Common.Messenger.receive_request messenger !id;
    e >>= fun e ->
    f num_iters e >>= function
    | U (State.Sat cand) ->
        Ok
          ( PCSP.Problem.Sat (Ast.CandSol.to_subst cand),
            { State.num_cegis_iters = num_iters } )
    | U State.Unsat ->
        Ok (PCSP.Problem.Unsat, { State.num_cegis_iters = num_iters })
    | U (State.Continue _ as e') ->
        let vs = State.version_space_of e' in
        last_version_space := Some vs;
        main_loop messenger f (num_iters + 1) (Ok e')
    | U State.Timeout ->
        Ok (PCSP.Problem.Unknown, { State.num_cegis_iters = num_iters })
    | U (State.OutSpace ps) ->
        Ok (PCSP.Problem.OutSpace ps, { State.num_cegis_iters = num_iters })
    | S _ -> Error (Error.of_thunk (fun () -> ""))

  let solve ?(oracle = None) pcsp =
    if Map.Poly.is_empty @@ PCSP.Problem.senv_of pcsp then
      let phi =
        Ast.ClauseSetOld.to_formula
        @@ Ast.ClauseSet.to_old_clause_set Map.Poly.empty
        @@ PCSP.Problem.clauses_of pcsp
      in
      if Z3Smt.Z3interface.is_valid ~id:None (Ast.LogicOld.get_fenv ()) phi then
        Ok (PCSP.Problem.Sat Map.Poly.empty, { State.num_cegis_iters = 0 })
      else Ok (PCSP.Problem.Unsat, { State.num_cegis_iters = 0 })
    else
      let open Or_error in
      last_version_space := None;
      let version =
        match MContext.context.version with
        | None -> Context.create_version pcsp
        | Some _ -> Context.significant_version_of MContext.context pcsp
      in
      Context.set_version MContext.context version;
      let new_state =
        VersionSpace.init oracle
        |> VersionSpace.set_fenv (PCSP.Problem.fenv_of pcsp)
        |> VersionSpace.set_examples version.graph
        |> VersionSpace.set_truth_table version.truth_table
        |> State.of_version_space
      in
      let messenger = PCSP.Problem.messenger_of pcsp in
      id := PCSP.Problem.id_of pcsp;
      if config.verbose then
        Context.show_graph ~pre:"init_" ~id:!id MContext.context.version;
      Debug.set_id !id;
      ExtFile.unwrap Cfg.config.rl_config >>= fun rl_config ->
      config.phase_list
      |> List.map ~f:(build_phase pcsp rl_config)
      |> Result.all
      >>= fun phase_list ->
      if rl_config.enable then (
        RLConfig.lock ();
        if rl_config.show_constraints then
          Debug.print_stdout
          @@ lazy
               (sprintf "constraints: %s" @@ Yojson.Safe.to_string
               @@ PCSP.Problem.to_yojson pcsp);
        if rl_config.show_num_constrs then
          Debug.print_stdout
          @@ lazy (sprintf "#constrs: %d" @@ PCSP.Problem.num_constrs pcsp);
        if rl_config.show_num_pvars then
          Debug.print_stdout
          @@ lazy (sprintf "#pvars: %d" @@ PCSP.Problem.num_pvars pcsp);
        if rl_config.show_dep_graph then
          Debug.print_stdout
          @@ lazy
               (sprintf "dependency graph:\n%s\n"
               @@ PCSP.Problem.str_of_graph
               @@ PCSP.Problem.dep_graph_of_chc pcsp);
        RLConfig.unlock ());
      main_loop messenger
        (fun iter e ->
          List.foldi phase_list ~init:(Ok (U e)) ~f:(app_phase messenger iter))
        0 (Ok new_state)
end

let make (config : Config.t) (context : Context.t) =
  (module Make
            (struct
              let config = config
            end)
            (struct
              let context = context
            end) : CoordinatorType)
