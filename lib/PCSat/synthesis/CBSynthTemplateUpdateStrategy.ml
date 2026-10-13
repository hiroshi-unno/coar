open Core
open Ast
open PCSatCommon

(* Unreachable as shipped: no config selects [Config.CBSynth], the only
   constructor that builds this strategy ([TemplateUpdateStrategy]).  That
   matters because the body below calls [FT.update_with_solution], and *every*
   one of the fifteen template modules defines it as [failwith "not
   implemented"] or [assert false] -- so this path aborts for any template it
   could be given.  Kept, because the repository keeps unexercised paths on
   purpose, but do not read it as working code: making it run means
   implementing [update_with_solution] somewhere first. *)

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
              Map.Poly.empty term
            |> FT.update_with_solution)
    | _ -> assert false
end
