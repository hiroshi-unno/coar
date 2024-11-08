open Core
open Ast
open PCSatCommon

module Make
    (Cfg : CBSynthesizer.Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) =
struct
  module CBSynthesizer =
    CBSynthesizer.Make
      (struct
        let config = Cfg.config
      end)
      (APCSP)

  let update template_modules _num_iters example _ =
    match CBSynthesizer.run_phase 0 (*dummy*) example with
    | Ok (State.Continue (_, candidates)) ->
        let (_params, candidate), _ = List.hd_exn candidates in
        Set.iter candidate ~f:(fun ((f, _), term) ->
            let (module FT : Template.Function.Type) =
              Map.Poly.find_exn template_modules f
            in
            Logic.ExtTerm.to_old_fml
              (PCSP.Problem.senv_of APCSP.problem)
              (Map.Poly.empty, term)
            |> FT.update_with_solution)
    | _ -> assert false
end
