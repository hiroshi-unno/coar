open Core
open Common.Util
open Ast
open PCSatCommon

module Make (Cfg : CBSynthesizer.Config.ConfigType) (PCSP: PCSP.Problem.ProblemType) = struct
  module CBSynthesizer = CBSynthesizer.Make (struct let config = Cfg.config end) (PCSP)

  let update template_modules example _ =
    match CBSynthesizer.run_phase example with
    | Ok (State.Continue (_, candidates)) ->
      let _params, candidate = List.hd_exn candidates in
      Set.Poly.iter candidate ~f:(fun ((f, _), term) ->
          let (module FunTemplate : Template.Function.Type) = Map.Poly.find_exn template_modules f in
          let senv = assert false in
          Logic.ExtTerm.to_old_formula senv term []
          |> FunTemplate.update_with_solution
        )
    | _ -> assert false
end