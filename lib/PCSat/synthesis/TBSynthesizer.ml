open Core
open Common
open Common.Util
open PCSatCommon

module Config = struct
  type t = {
    verbose: bool;
    generalize: bool;
    solution_template: SolutionTemplate.Config.t;
  } [@@ deriving yojson]

  let instantiate_ext_files cfg =
    let open Or_error in
    SolutionTemplate.Config.instantiate_ext_files cfg.solution_template >>= fun solution_template ->
    Ok { cfg with solution_template = solution_template }

  module type ConfigType = sig val config: t end
end

module Make (Cfg : Config.ConfigType) (PCSP: PCSP.Problem.ProblemType) = struct
  let config = Cfg.config

  module Debug = Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  module SolutionTemplate = SolutionTemplate.Make (struct let config = config.solution_template end) (PCSP)

  let mk_candidate examples =
    let candidate =
      SolutionTemplate.instantiate examples
      |> Map.Poly.to_alist
      |> List.map ~f:(fun (tvar, (sort, phi)) -> (tvar, sort), phi)
      |> Set.Poly.of_list
    in
    Ok candidate

  let run_phase example =
    let open State.Monad_infix in
    Ok (State.lift example) >>=? fun vs _ ->
    Debug.print @@ lazy "**************************************";
    Debug.print @@ lazy "***** Template Based Synthesizer *****";
    Debug.print @@ lazy "**************************************";
    let open Or_error in
    mk_candidate example >>= fun cand ->
    let cand = Ast.Logic.SortMap.empty, cand in
    let cands = [cand] @ if config.generalize then [Ast.CandSol.generalize cand] else [] in
    Ok (State.Continue (vs, cands))
end
