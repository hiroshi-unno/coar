open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld

module Make (Cfg: Config.ConfigType) = struct
  let config = Cfg.config

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))

  let ctx =
    let options =
      match config.timeout with
      | None -> []
      | Some timeout -> ["timeout", string_of_int @@ timeout * 1000]
    in
    Z3.mk_context options
  let solver = Z3.Fixedpoint.mk_fixedpoint ctx

  let solve ?(print_sol=false) pcsp =
    assert (Set.Poly.is_empty @@ PCSP.Problem.wfpvs_of pcsp &&
            Set.Poly.is_empty @@ PCSP.Problem.fnpvs_of pcsp
            (* ToDo: check if pcsp is of CHC *));
    let pcsp = pcsp |> PCSP.Problem.to_nnf |> PCSP.Problem.to_cnf in
    let cls = pcsp |> PCSP.Problem.clauses_of in
    let dtenv = Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx @@ PCSP.Problem.dtenv_of pcsp in
    let query_name = "__query__" in
    let exi_senv = Map.Poly.add_exn (PCSP.Problem.senv_of pcsp) ~key:(Ident.Tvar query_name) ~data:Logic.BoolTerm.SBool in
    let fenv = PCSP.Problem.fenv_of pcsp in
    let penv =
      List.map (Map.Poly.to_alist @@ exi_senv) ~f:(fun (Ident.Tvar name, sort) ->
          let arg_sorts =
            Logic.Sort.args_of sort
            |> List.map ~f:(fun s -> Z3Smt.Z3interface.of_sort ctx dtenv @@ Logic.ExtTerm.to_old_sort s) in
          let symbol = Z3.Symbol.mk_string ctx name in
          let func_decl = Z3.FuncDecl.mk_func_decl ctx symbol arg_sorts (Z3.Boolean.mk_sort ctx) in
          (Ident.Pvar name, func_decl))
    in
    List.iter ~f:(fun (_, funcdecl) -> Z3.Fixedpoint.register_relation solver funcdecl) penv;
    Set.Poly.iter cls ~f:(fun (uni_senv, ps, ns, phi) ->
        (** assume that [phi] is alpha-renamed *)
        let lenv = Logic.Term.let_sort_env_of phi in
        let uni_senv' = Map.force_merge uni_senv lenv in
        let ps =
          match Set.Poly.length ps with
          | 0 -> Set.Poly.singleton (Atom.mk_app (Predicate.mk_var (Ident.Pvar query_name) []) [])
          | 1 -> Set.Poly.map ps ~f:(fun t -> Logic.ExtTerm.to_old_atom exi_senv uni_senv t [])
          | _ -> assert false
        in
        let ns = Set.Poly.map ns ~f:(fun t -> Logic.ExtTerm.to_old_atom exi_senv uni_senv t []) in
        let body =
          Formula.mk_neg
            (Logic.ExtTerm.to_old_formula exi_senv uni_senv phi []
             |> Normalizer.normalize_let |> Formula.equivalent_valid) ::
          (ns |> Set.Poly.map ~f:Formula.mk_atom |> Set.Poly.to_list)
          |> Formula.and_of
        in
        let head =
          ps |> Set.Poly.map ~f:Formula.mk_atom |> Set.Poly.to_list |> Formula.and_of
        in
        let phi' = Formula.mk_imply body head in
        Debug.print @@ lazy (Formula.str_of phi');
        let tenv = Map.Poly.to_alist uni_senv' |> List.map ~f:(fun (x, s) -> x, Logic.ExtTerm.to_old_sort s) in
        let c = Z3Smt.Z3interface.of_formula ctx tenv penv fenv dtenv phi' in
        Z3.Fixedpoint.add_rule solver c None);
    try
      let solution =
        match Z3.Fixedpoint.query_r solver
                [List.Assoc.find_exn penv ~equal:Stdlib.(=) (Ident.Pvar query_name)] with
        | Z3.Solver.UNSATISFIABLE -> PCSP.Problem.Sat Map.Poly.empty(** ToDo: return a solution *)
        | Z3.Solver.SATISFIABLE -> PCSP.Problem.Unsat
        | Z3.Solver.UNKNOWN -> PCSP.Problem.Unknown
      in
      if print_sol then print_endline (PCSP.Problem.str_of_solution solution);
      Or_error.return solution
    with
    | Z3.Error reason ->
      if String.(reason = "spacer canceled" || reason = "canceled") then
        raise PCSP.Problem.Timeout(*ToDo*)
      else begin
        Debug.print @@ lazy (Printf.sprintf "Z3 Error: %s" reason);
        Or_error.return (PCSP.Problem.Unknown)
        (* Or_error.error_string reason*)
      end
end