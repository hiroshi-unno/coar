open Core
open Common
open Ast
open PCSatCommon

module Config = struct
  type t = {
    verbose : bool;
    generalize : bool;
    solution_template : SolutionTemplate.Config.t;
  }
  [@@deriving yojson]

  let instantiate_ext_files cfg =
    let open Or_error in
    SolutionTemplate.Config.instantiate_ext_files cfg.solution_template
    >>= fun solution_template -> Ok { cfg with solution_template }

  module type ConfigType = sig
    val config : t
  end
end

module Make
    (RLCfg : RLConfig.ConfigType)
    (Cfg : Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) =
struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  module MSolutionTemplate =
    SolutionTemplate.Make
      (RLCfg)
      (struct
        let config = config.solution_template
      end)
      (APCSP)

  let init () = MSolutionTemplate.init_incr ()

  let run_phase num_iters examples =
    let open State.Monad_infix in
    Ok (State.lift examples) >>=? fun vs _ ->
    Debug.print @@ lazy "**************************************";
    Debug.print @@ lazy "***** Template Based Synthesizer *****";
    Debug.print @@ lazy "**************************************";
    match MSolutionTemplate.synthesize num_iters examples with
    | SolutionTemplate.Cands (cand, part_cands) ->
        let cand = CandSol.make cand in
        let cands =
          (cand, CandSol.Total true)
          ::
          (if config.generalize then
             [ (CandSol.generalize cand, CandSol.Total true) ]
           else [])
          @ List.map part_cands ~f:(fun (cand, key) ->
                (CandSol.make cand, CandSol.Partial key))
        in
        Ok (State.Continue (vs, cands))
    | SolutionTemplate.OutSpace ps -> Ok (State.OutSpace ps)
end
