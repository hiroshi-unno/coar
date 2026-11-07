(* The framework's entry point for a frontend: an OCaml file to the
   model-checking problems of its [check_toplevel] attributes, through
   elaboration ([CpsElab]), a scheme and the HORS back end ([CpsHors]).

   [Selective_atp] names the selective transformation of Sekiyama, Dal Lago
   and Unno (OOPSLA 2025), which is not built yet: asking for it is an
   [Error], never a silent fallback to another scheme.  [O24] is the
   scheme of Sekiyama and Unno (OOPSLA 2024) as today's generator applies it.

   Contract: [Ok problems] lists one [HOMC.Problem.RSFD] per [check_toplevel]
   attribute, in source order, each over the items before its attribute; an
   input the framework does not translate is an [Error] naming why. *)

open Core

type scheme = O24 | Selective_atp

let from_ml_file ~verbose ~mbcsol ?(options = CpsHors.legacy_options) scheme
    filename =
  match scheme with
  | Selective_atp ->
      Or_error.error_string
        "[cps] the selective ATP scheme (OOPSLA 2025) is not built yet"
  | O24 -> (
      let module E = CpsElab.Make (struct
        let config = CpsElab.Config.{ verbose; mbcsol }
      end) in
      match E.elaborate_file filename with
      | Error msg -> Or_error.error_string msg
      | Ok { program; checks } ->
          List.map checks ~f:(fun (ta, n) ->
              match CpsHors.of_program ~options program n with
              | Ok rules ->
                  Ok
                    ( Format.asprintf "type_of(_) <: %s"
                        (Automata.TreeAutomaton.init_state_of ta),
                      HOMC.Problem.RSFD ([], rules, ta) )
              | Error msg -> Or_error.error_string msg)
          |> Or_error.combine_errors)
