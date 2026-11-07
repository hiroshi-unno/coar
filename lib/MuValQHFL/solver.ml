(* MuValQHFL: bounds of quantitative lambda-HFL terms.

   A problem is an OCaml file in one of RCaml's expectation modes
   ([[@@@mode "hfl_prop_as_expectation"]] or
   ["hfl_prop_as_conditional_expectation"]): a lambda-HFL term over the
   non-negative reals (pairs of them) with least fixed points, or one in a
   probability mode, a sub-probability term over [0, 1] that RCaml checks
   before typing it: ["hfl_prop_as_probability"] (least fixed points, upper
   bounds) or ["hfl_prop_as_liberal_probability"] ([0, 1] in the opposite
   order: greatest fixed points in the usual order, lower bounds), and
   [[@@@assert]]s bounding its top-level names.  There is no text syntax of
   its own.  A file without one of these modes is refused, since RCaml's
   ordinary reading is not about expectations.

   Each assertion is answered [valid] when RCaml's typing proves it (the
   refinement of a recursive result is admissible, so a typing is a proof of
   the bound) and [unknown] otherwise: an untypable bound is not refuted (the
   type system is incomplete, lower bounds of a least fixed point are out of
   its reach, and RCaml's [unsat] of an expectation problem is not a
   counterexample).  One line per assertion, in RCaml's format with this
   vocabulary: [valid,<iterations>   @assert <assertion> [#i]]. *)

open Core
open Common

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module RCamlSolver = RCaml.Solver.Make (struct
    let config = config.rcaml
  end)

  let expectation_modes =
    [
      "hfl_prop_as_expectation";
      "hfl_prop_as_conditional_expectation";
      "hfl_prop_as_probability";
      "hfl_prop_as_liberal_probability";
    ]

  let has_expectation_mode text =
    List.exists expectation_modes ~f:(fun m ->
        String.is_substring text ~substring:(sprintf "[@@@mode \"%s\"]" m))

  let solve_from_file filename =
    let open Or_error.Monad_infix in
    let text = In_channel.read_all filename in
    if not (has_expectation_mode text) then
      Or_error.error_string
        "refused: not a quantitative HFL program (no [@@@mode \
         \"hfl_prop_as_expectation\"], \
         \"hfl_prop_as_conditional_expectation\", \
         \"hfl_prop_as_probability\" or \
         \"hfl_prop_as_liberal_probability\")"
    else
      RCamlSolver.solutions_of_ml_string ~filename text >>| fun sols ->
      List.iteri sols ~f:(fun i -> function
        | RCaml.Problem.AssertSol (str, sol, iter) ->
            let verdict =
              match sol with
              | PCSP.Problem.Sat _ -> Verdict.Valid
              | _ -> Verdict.Unknown
            in
            print_endline
              (sprintf "%s,%d   \t@assert %s [#%d] " (Verdict.str_of verdict)
                 iter str (i + 1))
        | RCaml.Problem.OptimizeSol _ ->
            print_endline (sprintf "unknown,0   \t@optimize [#%d] " (i + 1)))
end
