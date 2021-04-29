open Core
open Common
open Common.Util
open PCSatCommon
open Validation
open Resolution
open Synthesis
open SatChecking

module Config = struct
  type phase =
    | V of Validator.Config.t ext_file
    | R of Resolver.Config.t ext_file
    | S of Synthesizer.Config.t ext_file
    | C of SatChecker.Config.t ext_file [@@deriving yojson]
  (** resolution and validation must be followed by SatChecker *)

  type t = {
    phase_list : phase list;
    validate_each_candidate: bool; (** check whether each candidate satisfies example instances *)
    verbose: bool
  } [@@deriving yojson]

  let load_ext_phase =
    let open Or_error in
    function
    | V cfg -> Validator.Config.load_ext_file cfg
      >>= fun cfg -> Ok (V cfg)
    | S cfg -> Synthesizer.Config.load_ext_file cfg
      >>= fun cfg -> Ok (S cfg)
    | R cfg -> Resolver.Config.load_ext_file cfg
      >>= fun cfg -> Ok (R cfg)
    | C cfg -> SatChecker.Config.load_ext_file cfg
      >>= fun cfg -> Ok (C cfg)

  let instantiate_ext_files cfg =
    let open Or_error in
    List.map ~f:load_ext_phase cfg.phase_list
    |> Result.all
    >>= fun phase_list -> Ok { cfg with phase_list = phase_list }

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
            "Invalid DefaultCoordinator Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)

  let str_of_phase = function
    | V _ -> "Validation" | S _ -> "Synthesis" | R _ -> "Resolution" | C _ -> "Sat Checking"

  module type ConfigType = sig val config : t end
end

open Config

module Make(Cfg: Config.ConfigType) = struct
  module type MUS = sig
    val run_phase : State.u -> State.s Or_error.t
  end
  module type MUU = sig
    val run_phase : State.u -> State.u Or_error.t
  end
  module type MSU = sig
    val run_phase : State.s -> State.u Or_error.t
  end
  type phase_type =
    | US of (module MUS) | UU of (module MUU) | SU of (module MSU)

  type state_type =
    | S of State.s | U of State.u

  let str_of_phase_type = function US _ -> "US" | UU _ -> "UU" | SU _ -> "SU"
  let str_of_state_type = function S _ -> "S" | U _ -> "U"

  let build_phase pcsp =
    let open Or_error in
    function
    | V cfg ->
      ExtFile.unwrap cfg >>= fun cfg -> Ok (SU (Validator.make cfg pcsp))
    | R cfg ->
      ExtFile.unwrap cfg >>= fun cfg -> Ok (UU (Resolver.make cfg pcsp))
    | S cfg ->
      ExtFile.unwrap cfg >>= fun cfg -> Ok (US (Synthesizer.make cfg pcsp))
    | C cfg ->
      ExtFile.unwrap cfg >>= fun cfg -> Ok (UU (SatChecker.make cfg pcsp))

  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let str_of_phase_list n =
    config.phase_list
    |> List.mapi ~f:(fun i phase ->
        Config.str_of_phase phase
        |> if i = n then (fun s -> "[" ^ s ^ "]") else ident)
    |> String.concat ~sep:" >> "

  let print_status iter n =
    let header = "************** current phase of " ^ Ordinal.string_of iter ^ " iteration **************" in
    Debug.print @@ lazy (header ^ "\n");
    Debug.print @@ lazy ((str_of_phase_list n) ^ "\n");
    Debug.print @@ lazy (String.init (String.length header) ~f:(fun _ -> '*'))

  let check_candidates exi_senv e =
    if config.validate_each_candidate then
      let open State.Monad_infix in
      Debug.print @@ lazy "** checking whether the candidates satisfy the example instances";
      Ok e >>=? fun vs cands ->
      let (pos, neg, und) = VersionSpace.examples_of vs in
      match ExClauseSet.check_candidates ~inst:true exi_senv (Set.Poly.union_list [pos; neg; und]) cands with
      | None -> Ok e
      | Some (cand, clause) ->
        Debug.print @@ lazy "The following candidate\n";
        Debug.print @@ lazy (Ast.CandSol.str_of cand);
        Debug.print @@ lazy "\nviolates the following example instance\n";
        Debug.print @@ lazy (ExClause.str_of clause);
        Debug.print @@ lazy "\nThis may be a bug of the synthesizer.";
        Or_error.error_string "Error in SequentialCoordinator.check_candidates"
    else Ok e

  let app_phase exi_senv iters i e phase =
    let open Or_error in
    e >>= fun e ->
    match e, phase with
    | U e, US (module Phase : MUS) ->
      if not (State.is_end e) then print_status iters i;
      (Phase.run_phase e >>= fun e -> Ok (S e))
    | U e, UU (module Phase : MUU) ->
      if not (State.is_end e) then print_status iters i;
      (Phase.run_phase e >>= fun e -> Ok (U e))
    | S e, SU (module Phase : MSU) ->
      if not (State.is_end e) then print_status iters i;
      check_candidates exi_senv e >>= fun e ->
      (Phase.run_phase e >>= fun e -> Ok (U e))
    | _ -> Error (Error.of_thunk (fun () ->
        Printf.sprintf
          ("phase type error: apply %s phase to %s state.\n"
           ^^ "coordinator configuration may be broken\n"
           ^^ "Hint:\n e.g., any validator follows only synthesizer")
          (str_of_phase_type phase) (str_of_state_type e)))

  let rec main_loop (f: int -> State.u -> state_type Or_error.t) iteration e =
    let open Or_error in
    e >>= fun e -> f iteration e >>= function
    | U (State.Sat cand) -> Ok (PCSP.Problem.Sat (Ast.CandSol.to_subst cand), iteration)
    | U Unsat -> Ok (PCSP.Problem.Unsat, iteration)
    | U ((State.Continue _) as e') -> main_loop f (iteration + 1) (Ok e')
    | S _ -> Error (Error.of_thunk (fun () -> ""))

  let solve pcsp =
    let open Or_error in
    let new_state = VersionSpace.init () |> VersionSpace.set_fenv (PCSP.Problem.fenv_of pcsp) |> State.of_version_space in
    config.phase_list
    |> List.map ~f:(build_phase pcsp)
    |> Result.all >>= fun phase_list ->
    main_loop
      (fun iter e -> List.foldi phase_list ~init:(Ok (U e)) ~f:(app_phase (PCSP.Problem.senv_of pcsp) iter))
      0 (Ok (new_state))
end