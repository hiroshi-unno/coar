(* The Z3 backend for plain SMT problems ([-p smt]).

   The formula is type-inferred (an unresolved numeric sort defaults to
   [Int]), its lets eliminated and simplified, and asked of Z3 together with
   the process-global function environment the reader filled.  Satisfiability
   here is SMT-LIB's: some model of the theory, with every defined function's
   defining equation holding.  For the definition families the Z3 boundary
   can state as ordinary declarations plus equations, all equations are
   asserted in a fresh context, since a native recursive definition is unfolded
   only where a query applies it. Unsupported positive known-function contexts
   without a verified model certificate return the Unknown verdict; other
   native [timeout] and [unknown] answers remain errors. *)
open Core
open Common
open Ast
open Ast.LogicOld

module type SolverType = sig
  val solve :
    ?print_sol:bool -> SMT.Problem.t -> SMT.Problem.solution Or_error.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let solve ?(print_sol = false) phi =
    Debug.print @@ lazy ("input: " ^ Ast.LogicOld.Formula.str_of phi);
    let phi =
      Evaluator.simplify @@ Formula.elim_let (*_equi false*)
      (*ToDo*) @@ Normalizer.normalize_let ~rename:true
      @@ Typeinf.typeinf_formula
           ~print:(*Debug.print*) (fun _ -> ())
           ~default:(Some LogicOld.T_int.SInt (*ToDo*)) phi
    in
    Debug.print @@ lazy ("simplified: " ^ Ast.LogicOld.Formula.str_of phi);
    let fenv =
      (* The reader keeps a recursive definition out of the formula on purpose --
         it cannot be inlined -- and hands it over here instead, where the Z3
         boundary declares the function and attaches its defining equation.
         Passing an empty environment dropped every such definition, so a
         function defined by [define-fun-rec] reached the solver uninterpreted
         and a query its definition refutes came back satisfiable, with the
         function shown as a don't-care in the model.  The same file written
         with [define-fun] answered correctly, because that body is inlined and
         never needs this. *)
      LogicOld.get_fenv ()
    in
    (* Defining equations must hold even when no assertion calls the
       function. Native recursive registration alone does not ensure this:
       Z3 unfolds a recursive definition only where a query applies it, so an
       uncalled definition with no model was answered sat. Ordinary declarations plus all equations are used in a fresh
       query context for this supported family only. *)
    let result =
      if Z3interface.supports_defining_equations fenv then
        Z3interface.check_sat_base ~fresh_solver:true ~defining_equations:true
          ~id:None fenv [ phi ]
      else if
        Z3interface.refutes_defining_context_by_instances ~phis:[ phi ] ~id:None fenv
      then `Unsat
      else if Map.Poly.is_empty fenv then Z3interface.check_sat ~id:None fenv [ phi ]
      else
        match Z3interface.defining_context_projection_model ~id:None fenv [phi] with
        | Some model -> `Sat model
        | None ->
            (match Z3interface.check_sat ~id:None fenv [phi] with
             | `Unsat -> `Unsat
             | _ -> `Unknown "known-function context has no verified model certificate")
    in
    match result with
    | `Sat model ->
        let solution = SMT.Problem.Sat model in
        if print_sol then print_endline (SMT.Problem.str_of_solution solution);
        Ok solution
    | `Unsat ->
        let solution = SMT.Problem.Unsat in
        if print_sol then print_endline (SMT.Problem.str_of_solution solution);
        Ok solution
    | `Unknown "known-function context has no verified model certificate" ->
        let solution = SMT.Problem.Unknown in
        if print_sol then (
          print_endline (SMT.Problem.str_of_solution solution);
          prerr_endline "known-function context check: no verified model certificate");
        Ok solution
    | `Timeout -> Or_error.error_string "timeout"
    | `Unknown reason -> Or_error.error_string reason
end
