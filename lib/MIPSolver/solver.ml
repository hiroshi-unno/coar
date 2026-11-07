open Core
open Common
open Common.Ext
open MIP.Problem
open Ast
open Ast.LogicOld

module type SolverType = sig
  type result = Sat of model | Unsat | Unknown of string

  val check_sat : Atom.t list -> sort_env_set -> result
end

module Make (Cfg : Config.ConfigType) : SolverType = struct
  let config = Cfg.config

  type result = Sat of model | Unsat | Unknown of string

  (* Gurobi is commercial: [GurobiEngine] is the real engine only in a build
     with the `lp-gurobi` package, and otherwise answers with an error. *)
  let solve =
    match config.engine with
    | Config.Glpk -> Lp_glpk.solve ~term_output:config.verbose
    | Config.Gurobi -> GurobiEngine.solve ~term_output:config.verbose
    | Config.Best_available ->
        if GurobiEngine.available then
          GurobiEngine.solve ~term_output:config.verbose
        else Lp_glpk.solve ~term_output:config.verbose

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  (* The value an engine reported for a column, as a term of [sort], or
     [None] when there is none to give.  An integer column's value is within
     the engine's integrality tolerance of an integer on either side
     (2.9999999997 for 3), so it is rounded to the nearest integer: truncation
     toward zero turned such a value into the wrong integer, which the exact
     check then rejected, losing a model the engine had found.  A real
     column's float is taken exactly.  Either is only a candidate, re-checked
     against the atoms by the caller. *)
  let value_of_column sort sol =
    if not (Float.is_finite sol) then None
    else
      match sort with
      | T_int.SInt ->
          Some
            (Term.of_value (get_dtenv ())
            @@ Value.Int (Z.of_float (Float.round_nearest sol)))
      | T_real.SReal ->
          Some (Term.of_value (get_dtenv ()) @@ Value.Real (Q.of_float sol))
      | _ -> None

  (* [Sat model] only when [model] satisfies every atom exactly, [Unsat] only
     when an atom is literally false, and [Unknown] for everything else --
     including an atom the MIP translation cannot express (a disequality, a
     nonlinear or non-arithmetic symbol), which is a refusal and not an
     error, and an infeasible MIP, which is a statement about a floating-point
     image of the atoms only. *)
  let check_sat atoms env =
    if List.exists atoms ~f:Atom.is_false then Unsat
    else if List.for_all atoms ~f:Atom.is_true then
      Sat (List.map (Set.to_list env) ~f:(fun bound -> (bound, None)))
    else
      match MIP.Problem.of_atoms atoms with
      | exception exn when not (Timer.is_async exn) ->
          Unknown ("MIPSolver: no MIP translation: " ^ Exn.to_string exn)
      | problem ->
      (* GLPK rejects zero columns by aborting before its OCaml error handler.
         Inspect the translated problem: cancellation can remove source vars. *)
      if List.is_empty (Lp.Problem.uniq_vars problem) then
        Unknown "MIPSolver: backend problem has no columns"
      else
        solve problem |> function
        | Ok (_, pmap) ->
            let model =
              List.map (Set.to_list env) ~f:(fun (tvar, sort) ->
                  let value =
                    match sort with
                    | T_int.SInt | T_real.SReal ->
                        Option.bind
                          (Lp.PMap.find_opt (lp_var_of_tvar tvar sort) pmap)
                          ~f:(value_of_column sort)
                    | _ -> None
                  in
                  ((tvar, sort), value))
            in
            let substitution =
              Map.Poly.of_alist_exn
                (List.filter_map model ~f:(fun ((v, _), value) ->
                     Option.map value ~f:(fun term -> (v, term))))
            in
            if
              List.for_all atoms ~f:(fun atom ->
                  let atom = Atom.subst substitution atom in
                  Set.is_empty (Atom.tvs_of atom)
                  && Formula.is_true (Evaluator.simplify (Formula.mk_atom atom)))
            then Sat model
            else
              Unknown
                "MIPSolver: candidate does not exactly satisfy original atoms"
        (* The adapter exposes all unsuccessful outcomes as an unstructured
       string: infeasibility, unavailable engines and backend failures are
       indistinguishable here. None is an unsatisfiability certificate. *)
        | Error message -> Unknown message
end
