open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld

let verbose = false
module Debug = Debug.Make (val Debug.Config.(if verbose then enable else disable))
let ctx = Z3.mk_context []
let solver = Z3.Fixedpoint.mk_fixedpoint ctx

let of_pcsp pcsp =
  (* Debug.print @@ lazy (sprintf "===================== pcsp ====================: \n%s" (PCSP.Problem.str_of pcsp)); *)
  let pcsp = PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf pcsp in
  let dtenv = Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx @@ PCSP.Problem.dtenv_of pcsp in
  let fenv = PCSP.Problem.fenv_of pcsp in
  let exi_senv = PCSP.Problem.senv_of pcsp in
  let query_name, exi_senv =
    try
      let query_name = "__query__" in
      query_name, Map.Poly.add_exn exi_senv ~key:(Ident.Tvar query_name) ~data:Logic.BoolTerm.SBool
    with _ ->
    try
      let query_name = "__query__hmm__" in
      query_name, Map.Poly.add_exn exi_senv ~key:(Ident.Tvar query_name) ~data:Logic.BoolTerm.SBool
    with _ -> assert false(*ToDo*)
  in
  let penv =
    List.map (Map.Poly.to_alist exi_senv) ~f:(fun (Ident.Tvar name, sort) ->
        let arg_sorts, ret_sort = Logic.Sort.args_ret_of sort in
        assert (Logic.ExtTerm.is_bool_sort ret_sort);
        let arg_sorts = List.map arg_sorts ~f:(fun s -> Z3Smt.Z3interface.of_sort ctx dtenv @@ Logic.ExtTerm.to_old_sort s) in
        let symbol = Z3.Symbol.mk_string ctx name in
        let func_decl = Z3.FuncDecl.mk_func_decl ctx symbol arg_sorts (Z3.Boolean.mk_sort ctx) in
        (Ident.Pvar name, func_decl))
  in
  List.iter ~f:(fun (_, funcdecl) -> Z3.Fixedpoint.register_relation solver funcdecl) penv;
  let exists_query = ref false in
  Set.Poly.iter (PCSP.Problem.clauses_of pcsp) ~f:(fun (uni_senv, ps, ns, phi) ->
      let ps =
        match Set.Poly.length ps with
        | 0 ->
          exists_query := true;
          Set.Poly.singleton (Atom.mk_app (Predicate.mk_var (Ident.Pvar query_name) []) [])
        | 1 -> Set.Poly.map ps ~f:(fun t -> Logic.ExtTerm.to_old_atom exi_senv uni_senv t [])
        | _ -> (* z3 does not support head disjunction *)assert false
      in
      let ns = Set.Poly.map ns ~f:(fun t -> Logic.ExtTerm.to_old_atom exi_senv uni_senv t []) in
      let body =
        Formula.mk_neg
          (Logic.ExtTerm.to_old_formula exi_senv uni_senv phi []
           |> Normalizer.normalize_let |> Formula.equivalent_valid) ::
        (ns |> Set.Poly.map ~f:Formula.mk_atom |> Set.Poly.to_list)
        |> Formula.and_of |> Evaluator.simplify
      in
      let head =
        ps |> Set.Poly.map ~f:Formula.mk_atom |> Set.Poly.to_list |> Formula.or_of
      in
      let phi' =  Formula.mk_imply body head in
      let tenv =
        (** assume that [phi] is alpha-renamed *)
        let lenv = Logic.Term.let_sort_env_of phi in
        let uni_senv = Map.force_merge uni_senv lenv in
        Map.Poly.to_alist uni_senv |> List.map ~f:(fun (x, s) -> x, Logic.ExtTerm.to_old_sort s)
      in
      let c = Z3Smt.Z3interface.of_formula ctx tenv penv fenv dtenv phi' in
      Z3.Fixedpoint.add_rule solver c None);
  (* set params *)
  let params = Z3.Params.mk_params ctx in
  Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "print_fixedpoint_extensions") false;
  Z3.Fixedpoint.set_parameters solver params;
  (* make smt string *)
  let prefix = ref "" in
  let inputs =
    let reg_assert = Str.regexp "^(assert \\(.*\\)$" in
    let reg_forall = Str.regexp "^(forall " in
    Z3.Fixedpoint.to_string solver
    |> String.split_on_chars ~on:['\n']
    |> List.map ~f:(fun line ->
        if Str.string_match reg_assert line 0 then
          let matched_str = Str.matched_group 1 line in
          let line' = !prefix in
          line'
          ^
          if not @@ Str.string_match reg_forall matched_str 0 then begin
            prefix := ")\n";
            "(assert (forall () " ^ matched_str
          end else begin
            prefix := "";
            line
          end else line) in
  let reg_anno = Str.regexp "(! \\| :weight.*[0-9])" in
  let reg_decl_query_name = Str.regexp @@ sprintf ".*declare-fun.*%s.*" query_name in
  let inputs = List.map inputs ~f:(fun s -> Str.global_replace reg_anno "" s) in
  let inputs = List.map inputs ~f:(fun s -> Str.global_replace reg_decl_query_name "" s) in
  let inputs = List.map inputs ~f:(fun s -> String.substr_replace_all s ~pattern:query_name ~with_:"false") in
  let inputs = inputs @ [ !prefix ] in
  (* let inputs = inputs @ if !exists_query then [ Printf.sprintf "(assert (forall ((M Bool)) (not (%s))))" query_name ] else [] in *)
  let inputs = inputs @ [ "(check-sat)" ] in
  (* let inputs = if config.produce_proofs then
      "(set-option :produce-proofs true)" :: inputs @ ["(get-proof)"]
     else inputs in *)
  let inputs = inputs @ ["(exit)"] in
  String.concat ~sep:"\n" inputs
