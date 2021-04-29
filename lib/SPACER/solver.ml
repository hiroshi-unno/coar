open Core
open Common
open Z3
open Ast
open Ast.LogicOld

module Make (Cfg: Config.ConfigType) = struct
  let config = Cfg.config

  module Debug = Debug.Make (val (Debug.Config.(if config.verbose then enable else disable)))

  let ctx =
    let options =
      match config.timeout with
      | None -> []
      | Some timeout -> ["timeout", string_of_int @@ timeout * 1000]
    in
    mk_context options
  let solver = Fixedpoint.mk_fixedpoint ctx

  let solve ?(print_sol=false) pcsp =
    assert (Core.Set.Poly.is_empty @@ PCSP.Problem.wfpvs_of pcsp &&
            Core.Set.Poly.is_empty @@ PCSP.Problem.fnpvs_of pcsp
            (* ToDo: check if pcsp is of CHC *));
    let pcsp = pcsp |> PCSP.Problem.to_nnf |> PCSP.Problem.to_cnf in
    let cls = pcsp |> PCSP.Problem.clauses_of in
    let dtenv = Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx @@ PCSP.Problem.dtenv_of pcsp in
    let query_name = "__query__" in
    let exi_senv = Logic.SortMap.add_exn (PCSP.Problem.senv_of pcsp) ~key:(Ident.Tvar query_name) ~data:Logic.BoolTerm.SBool in
    let fenv = PCSP.Problem.fenv_of pcsp in
    let penv =
      List.map (Logic.SortMap.to_alist @@ exi_senv) ~f:(fun (Ident.Tvar name, sort) ->
          let arg_sorts =
            Logic.Sort.args_of sort
            |> List.map ~f:(fun s -> Z3Smt.Z3interface.of_sort ctx dtenv @@ Logic.ExtTerm.to_old_sort s) in
          let symbol = Symbol.mk_string ctx name in
          let func_decl = FuncDecl.mk_func_decl ctx symbol arg_sorts (Boolean.mk_sort ctx) in
          (Ident.Pvar name, func_decl))
    in
    List.iter ~f:(fun (_, funcdecl) -> Fixedpoint.register_relation solver funcdecl) penv;
    Core.Set.Poly.iter cls ~f:(fun (uni_senv, ps, ns, phi) ->
        let senv = (Logic.SortMap.merge exi_senv uni_senv) in
        let ps =
          match Core.Set.Poly.length ps with
          | 0 -> Core.Set.Poly.singleton (Atom.mk_app (Predicate.mk_var (Ident.Pvar query_name) []) [])
          | 1 -> Core.Set.Poly.map ps ~f:(fun t -> Logic.ExtTerm.to_old_atom senv t [])
          | _ -> assert false
        in
        let ns = Core.Set.Poly.map ns ~f:(fun t -> Logic.ExtTerm.to_old_atom senv t []) in
        let body =
          Formula.mk_neg (Logic.ExtTerm.to_old_formula senv phi []) ::
          (ns |> Core.Set.Poly.map ~f:Formula.mk_atom |> Core.Set.Poly.to_list)
          |> Formula.and_of
        in
        let head = 
          ps |> Core.Set.Poly.map ~f:(fun a -> Formula.mk_atom a) |> Core.Set.Poly.to_list |> Formula.and_of
        in
        let phi' = Formula.mk_imply body head in
        Debug.print @@ lazy (Formula.str_of phi');
        let tenv = Logic.SortMap.to_alist uni_senv |> List.map ~f:(fun (x, s) -> x, Logic.ExtTerm.to_old_sort s) in
        let c = Z3Smt.Z3interface.of_formula ctx tenv penv fenv dtenv phi' in
        Fixedpoint.add_rule solver c None);
    try
      let solution =
        match Fixedpoint.query_r solver [List.Assoc.find_exn penv ~equal:Stdlib.(=) (Ident.Pvar query_name)] with
        | Solver.UNSATISFIABLE -> PCSP.Problem.Sat Map.Poly.empty(** ToDo: return a solution *)
        | Solver.SATISFIABLE -> PCSP.Problem.Unsat
        | Solver.UNKNOWN -> PCSP.Problem.Unknown
      in
      if print_sol then print_endline (PCSP.Problem.str_of_solution solution);
      Or_error.return solution
    with
    | Error reason ->
      if String.(reason = "spacer canceled" || reason = "canceled") then
        raise PCSP.Problem.Timeout(*ToDo*)
      else begin
        Debug.print @@ lazy (Printf.sprintf "Z3 Error: %s" reason);
        Or_error.return (PCSP.Problem.Unknown)
        (* Deferred.Or_error.error_string reason*)
      end
end