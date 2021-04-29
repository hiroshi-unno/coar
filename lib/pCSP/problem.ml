open Core
open Common.Util
open Ast
open Ast.Logic

(** unknown parameters to be synthesized *)
type t = Raw of (SortMap.t * term) Set.Poly.t * Params.t
       | Cnf of ClauseSet.t * Params.t

type solution = Sat of (Ident.tvar, term) Map.Poly.t | Unsat | Unknown

exception Timeout

module type ProblemType = sig val problem : t end

let of_formulas ?(params=Params.empty) phis = Raw (phis, params)
let of_clauses ?(params=Params.empty) cs = Cnf (cs, params)

let to_nnf = function
  | Raw (phis, params) -> Raw(Set.Poly.map phis ~f:(fun (senv, phi) -> senv, BoolTerm.nnf_of phi), params)
  | cnf -> cnf
let to_cnf = function
  | Raw (phis, params) -> Cnf (ClauseSet.of_formulas (params.senv) phis, params)
  | cnf -> cnf

let clauses_of = function
  | Raw _ -> failwith "The pfwCSP is not of CNF"
  | Cnf (cnf, _) -> cnf
let formulas_of = function
  | Raw (phis, _) -> phis
  | Cnf (cnf, _) -> cnf |> Set.Poly.map ~f:(fun c -> Clause.sort_env_of c, Clause.to_formula c)
let formula_of = function
  | Raw (phis, _) -> BoolTerm.and_of (Set.Poly.map ~f:snd phis |> Set.Poly.to_list)
  | Cnf (cnf, _) -> ClauseSet.to_formula cnf
let params_of = function
  | Raw (_, params) | Cnf (_, params) -> params
let senv_of pcsp = (params_of pcsp).Params.senv
let wfpvs_of pcsp = (params_of pcsp).Params.wfpvs
let fnpvs_of pcsp = (params_of pcsp).Params.fnpvs
let dtenv_of pcsp = (params_of pcsp).Params.dtenv
let fenv_of pcsp = (params_of pcsp).Params.fenv
let wfpvs_senv_of pcsp =
  let wfpvs = wfpvs_of pcsp in
  Logic.SortMap.filter_keys (senv_of pcsp) ~f:(Set.Poly.mem wfpvs)
let fnpvs_senv_of pcsp =
  let fnpvs = fnpvs_of pcsp in
  Logic.SortMap.filter_keys (senv_of pcsp) ~f:(Set.Poly.mem fnpvs)
let npfvs_of pcsp =
  Set.Poly.filter_map (Logic.SortMap.to_set @@ senv_of pcsp) ~f:(fun (x, s) -> if Stdlib.(<>) (Sort.ret_of s) BoolTerm.SBool then Some x else None)
let pvs_of pcsp =
  Set.Poly.filter_map (Logic.SortMap.to_set @@ senv_of pcsp) ~f:(fun (x, s) -> if Stdlib.(=) (Sort.ret_of s) BoolTerm.SBool then Some x else None)

let is_wf_pred pcsp = Set.Poly.mem (wfpvs_of pcsp)
let is_fn_pred pcsp = Set.Poly.mem (fnpvs_of pcsp)
let is_ord_pred pcsp x =
  match Logic.SortMap.find (senv_of pcsp) x with
  | None -> false
  | Some s -> Stdlib.(=) (Sort.ret_of s) ExtTerm.SBool && not @@ is_wf_pred pcsp x && not @@ is_fn_pred pcsp x
let is_int_fun pcsp x =
  match Logic.SortMap.find (senv_of pcsp) x with
  | None -> false
  | Some s -> Stdlib.(=) (Sort.ret_of s) ExtTerm.SInt

let map_if_raw_old ~f = function
  | Raw (phis, params) ->
    let exi_senv = params.senv in
    phis
    |> Set.Poly.map ~f:(fun (uni_senv, phi) ->
        Map.of_set @@ Logic.SortMap.to_set @@ Logic.SortMap.map ~f:ExtTerm.to_old_sort uni_senv,
        ExtTerm.to_old_formula (SortMap.merge exi_senv uni_senv) phi [])
    |> f
    |> Set.Poly.map ~f:(fun (uni_senv, phi) ->
        Logic.SortMap.of_old_sort_map ExtTerm.of_old_sort uni_senv,
        ExtTerm.of_old_formula phi)
    |> fun phis -> Raw (phis, params)
  | cnf -> cnf
let map_if_raw ~f:f = function
  | Raw (phis, params) -> Raw (f phis, params)
  | cnf -> cnf

let str_of pcsp =
  let exi_senv = (params_of pcsp).senv in
  let s1 =
    pcsp
    |> formulas_of
    |> Set.Poly.map ~f:(fun (uni_senv, phi) ->
        string_of_int (Logic.SortMap.length uni_senv) ^ ": " ^
        LogicOld.Formula.str_of @@ ExtTerm.to_old_formula (SortMap.merge exi_senv uni_senv) phi []
        (*ExtTerm.str_of phi*))
    |> Set.Poly.to_list
    |> String.concat ~sep:";\n"
  in
  let s2 = "sort env: " ^ (SortEnv.str_of ExtTerm.str_of_sort (Map.Poly.to_alist @@ senv_of pcsp)) in
  let s3 = "wfpvs: " ^ (wfpvs_of pcsp |> Set.Poly.to_list |> List.map ~f:(fun (Ident.Tvar n) -> n) |> String.concat ~sep:",") in
  let s4 = "fnpvs: " ^ (fnpvs_of pcsp |> Set.Poly.to_list |> List.map ~f:(fun (Ident.Tvar n) -> n) |> String.concat ~sep:",") in
  s1 ^ "\n" ^ s2 ^ "\n" ^ s3 ^ "\n" ^ s4

let str_of_info pcsp =
  let phis = formulas_of pcsp in
  let num_of_constraints = Set.Poly.length phis in
  let num_of_pvars = pvs_of pcsp |> Set.Poly.length in
  Printf.sprintf 
    "number of predicate variables: %d, number of constraints: %d" num_of_pvars num_of_constraints
let str_of_solution = function
  | Sat _subst -> "sat"
  | Unsat -> "unsat"
  | Unknown -> "unknown"

let str_of_sygus_solution = function
  | Sat sol -> SyGuS.InvPrinter.str_of_solution @@ CandSolOld.of_subst sol
  | Unsat -> "infeasible"
  | Unknown -> "fail"

let add_non_emptiness (pvar, sorts) = let open LogicOld in function
    | Raw (phis, p_params) ->
      let params = SortEnv.of_sorts sorts in
      let bool_params, arith_params =
        SortEnv.partition_tf params ~f:(function (_, T_bool.SBool) -> true | _ -> false)
      in
      let pvs = List.map (SortEnv.list_of arith_params) ~f:(fun (Ident.Tvar x, _) -> Ident.Pvar ("FN_" ^ x)) in
      let body = Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts (Term.of_sort_env params) in
      let body =
        (* expand existential quantification over boolean variables *)
        let rec aux body = function
          | [] -> body
          | (x, sort) :: xs ->
            assert (Stdlib.(=) sort T_bool.SBool);
            let body = aux body xs in
            Formula.or_of [Formula.subst (Map.Poly.singleton x (T_bool.of_atom (Atom.mk_true ()))) body;
                           Formula.subst (Map.Poly.singleton x (T_bool.of_atom (Atom.mk_false ()))) body]
        in
        aux body (SortEnv.list_of bool_params)
      in
      let senv = Map.Poly.of_alist_exn @@ SortEnv.map ~f:Logic.ExtTerm.of_old_sort_bind params in
      let phi =
        Logic.ExtTerm.of_old_formula @@
        Evaluator.simplify @@
        Formula.mk_imply
          (Formula.and_of @@
           List.map2_exn pvs (SortEnv.list_of arith_params) ~f:(fun pvar (tvar, sort) ->
               Formula.mk_atom @@ Atom.mk_pvar_app pvar [sort] [Term.mk_var tvar sort]))
          body
      in
      let fnpv_senv = Map.Poly.of_alist_exn @@ List.map pvs ~f:(fun (Ident.Pvar x) -> Ident.Tvar x, Logic.Sort.mk_arrow Logic.IntTerm.SInt(*ToDo*) Logic.BoolTerm.SBool) in
      let p_params = { p_params with senv = SortMap.merge p_params.senv fnpv_senv; fnpvs = Set.Poly.union p_params.fnpvs (Map.key_set fnpv_senv) } in
      Raw (Set.Poly.add phis (senv, BoolTerm.elim_imp phi), p_params)
    | Cnf (_, _) -> failwith "add_non_emptiness"
let add_formula (senv, phi) = function
  | Raw (phis, params) ->
    Raw (Set.Poly.add phis (senv, BoolTerm.elim_imp phi), params)
  | Cnf (_, _) -> failwith "add_formula"
let add_clause clause = function
  | Raw (_, _) -> failwith "The pfwCSP is not of CNF"
  | Cnf (cnf, params) -> Cnf (Set.Poly.add cnf clause, params)

let divide pcsp =
  pcsp |> to_nnf |> to_cnf |> function
  | Raw (_, _) -> failwith "The pfwCSP is not of CNF"
  | Cnf (cnf, params) ->
    let cnf1, cnf2 = Set.Poly.partition_tf cnf ~f:(Clause.is_query params.wfpvs params.fnpvs) in
    Set.Poly.map cnf1 ~f:(fun c -> Cnf (Set.Poly.add cnf2 c, params))
    |> Set.Poly.to_list
let merge_sol _pcsp sols =
  let iters = List.fold ~init:0 ~f:(+) (List.map ~f:snd sols) in
  let merge _s s' = s' (* ToDo *) in
  let rec inner sol = function
    | [] -> Sat sol, iters
    | Sat sol' :: sols -> inner (merge sol sol') sols
    | Unsat :: _sols -> Unsat, iters
    | Unknown :: _sols -> Unknown, iters
  in
  inner Map.Poly.empty (List.map ~f:fst sols)
let extend_sol sol sol' =
  match sol with
  | Sat sol -> Sat (Map.force_merge sol sol')
  | Unsat | Unknown -> sol

let of_sygus (synth_funs, declared_vars, terms) =
  let exi_senv = Logic.SortMap.map synth_funs ~f:fst in
  List.map terms ~f:(fun t -> declared_vars, t)
  |> Set.Poly.of_list
  |> of_formulas ~params:(Params.make exi_senv)

let of_lts _lts = assert false

let remove_unused_params pcsp =
  match pcsp with
  | Raw (phis, params) ->
    let vs = Set.Poly.map phis ~f:(fun (_, phi) -> Term.fvs_of phi) |> Set.concat in
    Raw (phis, { params with senv = Logic.SortMap.filter_keys ~f:(Set.Poly.mem vs) params.senv } )
  | Cnf (cnf, params) ->
    let pvs = ClauseSet.pvs_of cnf in
    Cnf (cnf, { params with senv = Logic.SortMap.filter_keys ~f:(Set.Poly.mem pvs) params.senv })

let mk_dtenv pcsp =
  let exi_senv = (params_of pcsp).senv in
  let dtenv = Set.Poly.fold (formulas_of pcsp) ~init:(Map.Poly.empty) ~f:(
      fun ret (uni_senv, phi) -> 
        LogicOld.DTEnv.merge ret 
          (LogicOld.DTEnv.of_formula @@ 
           Logic.ExtTerm.to_old_formula (SortMap.merge exi_senv uni_senv) phi [])
    ) in
  dtenv

let update_params_dtenv pcsp =
  match pcsp with
  | Raw (phis, params) -> Raw(phis, {params with dtenv = mk_dtenv pcsp}) 
  | Cnf (cls, params) -> Cnf (cls, {params with dtenv = mk_dtenv pcsp})
