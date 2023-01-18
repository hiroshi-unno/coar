open Core
open Common.Ext
open Ast
open Ast.Logic
open Common.Messenger

type t =
  | Raw of (sort_env_map * term) Set.Poly.t * Params.t
  | Cnf of ClauseSet.t * Params.t

type solution = Sat of term_subst_map | Unsat | Unknown | OutSpace of Ident.tvar list
type oracle = CandSolOld.t option

type bounds = (Ident.tvar, int * (sort_env_map * term)) Map.Poly.t
type info +=
  | CandidateSolution of
      (term_subst_map * term_subst_map * ClauseSet.t * ClauseSet.t *
       (sort_env_map * Ast.LogicOld.FunEnv.t * (Ident.tvar, Logic.term) Hashtbl.Poly.t) option)
  | LowerBounds of bounds
  | UpperBounds of bounds

exception Timeout

module type ProblemType = sig val problem : t end

let of_formulas ?(params=Params.empty) phis = Raw (phis, params)
let of_clauses ?(params=Params.empty) cs = Cnf (cs, params)

let params_of = function Raw (_, params) | Cnf (_, params) -> params
let senv_of pcsp = (params_of pcsp).Params.senv
let kind_map_of pcsp = (params_of pcsp).Params.kind_map
let kindpvs_of_aux pcsp is_kind =
  (params_of pcsp).Params.kind_map
  |> Map.Poly.filter ~f:is_kind
  |> Map.Poly.filter_keys ~f:(Map.Poly.mem (senv_of pcsp))
  |> Map.key_set
let wfpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_wf
let fnpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_fn
let nwfpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_nwf
let nepvs_of pcsp = kindpvs_of_aux pcsp Kind.is_ne
let wfpvs_senv_of pcsp =
  let wfpvs = wfpvs_of pcsp in
  Map.Poly.filter_keys (senv_of pcsp) ~f:(Set.Poly.mem wfpvs)
let fnpvs_senv_of pcsp =
  let fnpvs = fnpvs_of pcsp in
  Map.Poly.filter_keys (senv_of pcsp) ~f:(Set.Poly.mem fnpvs)
let nepvs_senv_of pcsp =
  let nepvs = nepvs_of pcsp in
  Map.Poly.filter_keys (senv_of pcsp) ~f:(Set.Poly.mem nepvs)
let nwfpvs_senv_of pcsp =
  Map.Poly.filter_mapi (senv_of pcsp) ~f:(fun ~key ~data:_ ->
      match Map.Poly.find (kind_map_of pcsp) key with
      | Some (Kind.NWF (nwf, (idl, idr))) ->
        Some (nwf.name, nwf.param_sorts,
              idl, Kind.sorts_of_tag nwf idl,
              idr, Kind.sorts_of_tag nwf idr)
      | _ -> None)
let npfvs_of pcsp =
  Set.Poly.filter_map (Map.to_set @@ senv_of pcsp)
    ~f:(fun (x, s) -> if Fn.non BoolTerm.is_bool_sort @@ Sort.ret_of s then Some x else None)
let pvs_of pcsp =
  Set.Poly.filter_map (Map.to_set @@ senv_of pcsp)
    ~f:(fun (x, s) -> if BoolTerm.is_bool_sort @@ Sort.ret_of s then Some x else None)
let dtenv_of pcsp = (params_of pcsp).Params.dtenv
let fenv_of pcsp = (params_of pcsp).Params.fenv
let sol_space_of pcsp = (params_of pcsp).Params.sol_space
let messenger_of pcsp = (params_of pcsp).Params.messenger
let sol_for_eliminated_of pcsp = (params_of pcsp).Params.sol_for_eliminated
let args_record_of pcsp = (params_of pcsp).Params.args_record
let unpreprocessable_clauses_of pcsp = (params_of pcsp).Params.unpreprocessable_clauses
let partial_sol_targets_of pcsp = (params_of pcsp).Params.partial_sol_targets
let dep_graph_of pcsp = (params_of pcsp).Params.dep_graph
let id_of pcsp = (params_of pcsp).id

let is_wf_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_wf
let is_fn_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_fn
let is_ord_pred pcsp x =
  match Map.Poly.find (senv_of pcsp) x with
  | None -> false
  | Some s -> BoolTerm.is_bool_sort @@ Sort.ret_of s &&
              Params.is_kind (params_of pcsp) Kind.is_ord x
let is_int_fun pcsp x =
  match Map.Poly.find (senv_of pcsp) x with
  | None -> false
  | Some s -> Stdlib.(Sort.ret_of s = ExtTerm.SInt)
let is_nwf_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_nwf
let is_ne_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_ne

let clauses_of ?(full_clauses=true) = function
  | Raw _ -> failwith "The pfwCSP is not of CNF"
  | Cnf (cnf, _) as pcsp ->
    if full_clauses then Set.Poly.union cnf (unpreprocessable_clauses_of pcsp) else cnf
let clauses_to_formulas = Set.Poly.map ~f:(fun c -> Clause.sort_env_of c, Clause.to_formula c)
let formulas_of ?(full_clauses=true) = function
  | Raw (phis, _) -> phis
  | Cnf (cnf, _) as pcsp ->
    if full_clauses then
      Set.Poly.union (clauses_to_formulas @@ unpreprocessable_clauses_of pcsp) @@
      clauses_to_formulas cnf
    else clauses_to_formulas cnf
let formula_of ?(full_clauses=true) = function
  | Raw (phis, _) -> BoolTerm.and_of @@ Set.Poly.to_list @@ Set.Poly.map ~f:snd phis
  | Cnf (cnf, _) as pcsp ->
    BoolTerm.and_of
      [ClauseSet.to_formula @@
       if full_clauses then unpreprocessable_clauses_of pcsp else Set.Poly.empty;
       ClauseSet.to_formula cnf]

let num_constrs pcsp = Set.Poly.length @@ formulas_of pcsp
let num_pvars pcsp = Set.Poly.length @@ pvs_of pcsp


let dtenv_of_def pcsp =
  let exi_senv = (params_of pcsp).senv in
  Set.Poly.fold ~init:Map.Poly.empty (formulas_of pcsp) ~f:(fun ret (uni_senv, phi) ->
      LogicOld.DTEnv.force_merge ret @@
      LogicOld.DTEnv.of_formula @@ Logic.ExtTerm.to_old_formula exi_senv uni_senv phi [])

let map_params ~f = function
  | Raw (phis, params) -> Raw (phis, f params)
  | Cnf (cls, params) -> Cnf (cls, f params)
let update_params pcsp params =
  match pcsp with
  | Raw (phis, _) -> Raw (phis, params)
  | Cnf (cls, _) -> Cnf (cls, params)
let update_params_dtenv = function
  | Raw (phis, params) as pcsp ->
    Raw (phis, { params with dtenv = Map.force_merge (dtenv_of pcsp) @@ dtenv_of_def pcsp })
  | Cnf (cls, params) as pcsp ->
    Cnf (cls, { params with dtenv = Map.force_merge (dtenv_of pcsp) @@ dtenv_of_def pcsp })
let update_params_sol_space pcsp sol_space =
  update_params pcsp { (params_of pcsp) with sol_space = sol_space }

let map_if_raw_old ~f = function
  | Raw (phis, params) ->
    let exi_senv = params.senv in
    phis
    |> Set.Poly.map ~f:(fun (uni_senv, phi) ->
        Map.of_set_exn @@ Map.to_set @@ Map.Poly.map ~f:ExtTerm.to_old_sort uni_senv,
        ExtTerm.to_old_formula exi_senv uni_senv phi [])
    |> f
    |> Set.Poly.map ~f:(fun (uni_senv, phi) ->
        Logic.of_old_sort_env_map ExtTerm.of_old_sort uni_senv,
        ExtTerm.of_old_formula phi)
    |> fun phis -> Raw (phis, params)
  | cnf -> cnf
let map_if_raw ~f:f = function Raw (phis, params) -> Raw (f phis, params) | cnf -> cnf

type pcsp = { clauses: string list; unknowns: (string * string) list } [@@ deriving to_yojson]
let to_yojson pcsp =
  let exi_senv = (params_of pcsp).senv in
  {
    clauses =
      pcsp
      |> formulas_of
      |> Set.Poly.map ~f:(fun (uni_senv, phi) -> ExtTerm.str_of_formula exi_senv uni_senv phi)
      |> Set.Poly.to_list;
    unknowns =
      senv_of pcsp
      |> Map.Poly.to_alist
      |> List.map ~f:(fun (tvar, sort) -> Ident.name_of_tvar tvar, ExtTerm.str_of_sort sort)
  }
  |> pcsp_to_yojson

let str_of pcsp =
  let str_of_set s =
    String.concat_map_list ~sep:"," ~f:Ident.name_of_tvar @@ Set.Poly.to_list s
  in
  sprintf "%s\n\nsort env: %s\nwfpvs: %s\nnwfpvs: %s\nfnpvs: %s\nnepvs: %s\nsol_space: %s"
    (String.concat_map_set ~sep:"\n" (formulas_of pcsp) ~f:(fun (uni_senv, phi) ->
         "[" ^ string_of_int (Map.Poly.length uni_senv) ^ "] " ^
         ExtTerm.str_of_formula (params_of pcsp).senv uni_senv phi))
    (str_of_sort_env_list ExtTerm.str_of_sort @@ Map.Poly.to_alist @@ senv_of pcsp)
    (str_of_set @@ wfpvs_of pcsp) (str_of_set @@ nwfpvs_of pcsp)
    (str_of_set @@ fnpvs_of pcsp) (str_of_set @@ nepvs_of pcsp)
    (SolSpace.str_of @@ sol_space_of pcsp)
(*let str_of_senv pcsp = "sort env: " ^ str_of_sort_env_map ExtTerm.str_of_sort @@ senv_of pcsp*)

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
  | OutSpace pvs ->
    sprintf "out_space: %s" @@ String.concat_map_list ~sep:"," pvs ~f:Ident.name_of_tvar
let str_of_sygus_solution = function
  | Sat sol -> SyGuS.InvPrinter.str_of_solution @@ CandSolOld.of_subst sol
  | Unsat -> SyGuS.InvPrinter.str_of_unsat ()
  | Unknown -> SyGuS.InvPrinter.str_of_unknown ()
  | OutSpace pvs ->
    sprintf "out_space: %s" @@ String.concat_map_list ~sep:"," pvs ~f:Ident.name_of_tvar

let add_non_emptiness (pvar, sorts) = let open LogicOld in
  function
  | Raw (phis, p_params) ->
    let params = sort_env_list_of_sorts sorts in
    let bool_params, arith_params =
      List.partition_tf params ~f:(function (_, T_bool.SBool) -> true | _ -> false)
    in
    let pvs =
      List.map arith_params ~f:(fun (Ident.Tvar x, _) ->
          Ident.Pvar ("FN" ^ Ident.divide_flag ^ x))
    in
    let body = Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts (Term.of_sort_env params) in
    let body =
      (* expand existential quantification over boolean variables *)
      let rec aux body = function
        | [] -> body
        | (x, sort) :: xs ->
          assert (Term.is_bool_sort sort);
          let body = aux body xs in
          Formula.or_of
            [Formula.subst (Map.Poly.singleton x (T_bool.of_atom (Atom.mk_true ()))) body;
             Formula.subst (Map.Poly.singleton x (T_bool.of_atom (Atom.mk_false ()))) body]
      in
      aux body bool_params
    in
    let senv = Map.Poly.of_alist_exn @@ List.map ~f:Logic.ExtTerm.of_old_sort_bind params in
    let phi =
      Logic.ExtTerm.of_old_formula @@ Evaluator.simplify @@
      Formula.mk_imply
        (Formula.and_of @@
         List.map2_exn pvs arith_params ~f:(fun pvar (tvar, sort) ->
             Formula.mk_atom @@ Atom.mk_pvar_app pvar [sort] [Term.mk_var tvar sort]))
        body
    in
    let fnpv_senv =
      Map.Poly.of_alist_exn @@
      List.map pvs ~f:(fun (Ident.Pvar x) ->
          Ident.Tvar x, Logic.Sort.mk_arrow Logic.IntTerm.SInt(*ToDo*) Logic.BoolTerm.SBool)
    in
    let p_params =
      { p_params with
        senv = Map.force_merge p_params.senv fnpv_senv;
        kind_map =  Kind.add_kinds (Map.key_set fnpv_senv) Kind.FN p_params.kind_map }
    in
    Raw (Set.Poly.add phis (senv, BoolTerm.elim_imp phi), p_params)
  | Cnf (_, _) -> failwith "add_non_emptiness"
let add_formula (senv, phi) = function
  | Raw (phis, params) ->
    Raw (Set.Poly.add phis (senv, BoolTerm.elim_imp phi), params)
  | Cnf (_, _) -> failwith "add_formula"
let add_clause clause = function
  | Raw (_, _) -> failwith "The pfwCSP is not of CNF"
  | Cnf (cnf, params) -> Cnf (Set.Poly.add cnf clause, params)

let to_nnf = function
  | Raw (phis, params) ->
    Raw (Set.Poly.map phis ~f:(fun (senv, phi) -> senv, BoolTerm.nnf_of phi), params)
  | cnf -> cnf
let to_cnf = function
  | Raw (phis, params) -> Cnf (ClauseSet.of_formulas params.senv phis, params)
  | cnf -> cnf
let divide pcsp =
  pcsp |> to_nnf |> to_cnf |> function
  | Raw (_, _) -> failwith "The pfwCSP is not of CNF"
  | Cnf (cnf, params) ->
    let cnf1, cnf2 =
      Set.Poly.partition_tf cnf ~f:(Clause.is_query (wfpvs_of pcsp) (fnpvs_of pcsp))
    in
    Set.Poly.to_list @@ Set.Poly.map cnf1 ~f:(fun c -> Cnf (Set.Poly.add cnf2 c, params))

let merge_sols _pcsp sols =
  let merge _s s' = s' (* ToDo *) in
  let rec inner sol = function
    | [] -> Sat sol
    | Sat sol' :: sols -> inner (merge sol sol') sols
    | Unsat :: _sols -> Unsat
    | Unknown :: _sols -> Unknown
    | OutSpace pvs :: _sols -> OutSpace pvs
  in
  inner Map.Poly.empty sols
let extend_sol sol sol' =
  match sol with
  | Sat sol -> Sat (Map.force_merge sol sol')
  | Unsat | Unknown | OutSpace _ -> sol
(*let nest_subst subst =
  let keys = Map.key_set subst in
  let rec inner subst =
    let subst = Map.Poly.map subst ~f:(Logic.ExtTerm.subst subst) in
    if Map.Poly.exists subst ~f:(fun term ->
        Set.Poly.exists (ExtTerm.fvs_of term) ~f:(Set.Poly.mem keys)) then inner subst
    else subst
  in
  inner subst*)

let svs_of = function
  | Raw (phis, _params) ->
    Set.concat_map phis ~f:(fun (_, phi) ->
        Term.svs_of ExtTerm.svs_of_sym ExtTerm.svs_of_sort phi)
  | Cnf (cnf, _params) -> ClauseSet.svs_of cnf
let instantiate_svars_to_int pcsp =
  let sub = Map.of_set_exn @@ Set.Poly.map (svs_of pcsp) ~f:(fun svar -> svar, LogicOld.T_int.SInt) in
  map_if_raw_old pcsp ~f:(Set.Poly.map ~f:(fun (uni_senv, phi) ->
      (uni_senv, LogicOld.Formula.subst_sorts sub phi)))

let normalize pcsp =
  let unknowns = Map.key_set @@ senv_of pcsp in
  map_if_raw_old pcsp ~f:(Set.Poly.map ~f:(fun (uni_senv, phi) ->
      let phi' =
        phi
        (*|> LogicOld.Formula.elim_pvars unknowns*)
        |> Normalizer.normalize_let ~rename:true
        (* |> LogicOld.Formula.equivalent_valid *)
        |> LogicOld.Formula.elim_let_with_unknowns unknowns
        (* |> LogicOld.Formula.elim_let *)
        |> Normalizer.normalize
        |> Evaluator.simplify
      in
      (* print_endline @@ sprintf "[normalize] \n  before:%s\n  after :%s\n" (str_of phi) (str_of phi'); *)
      (uni_senv, phi')))

let of_sygus (synth_funs, declared_vars, terms) =
  let exi_senv = Map.Poly.map synth_funs ~f:fst in
  List.map terms ~f:(fun t -> declared_vars, t)
  |> Set.Poly.of_list
  |> of_formulas ~params:(Params.make exi_senv)
  |> normalize

let of_lts _lts = assert false

let remove_unused_params pcsp =
  let pcsp' =
    let unpreprocessable_pvs = ClauseSet.pvs_of @@ unpreprocessable_clauses_of pcsp in
    match pcsp with
    | Raw (phis, params) ->
      let vs =
        Set.Poly.union unpreprocessable_pvs @@
        Set.concat_map phis ~f:(fun (_, phi) -> Term.fvs_of phi)
      in
      Raw (phis, { params with senv = Map.Poly.filter_keys ~f:(Set.Poly.mem vs) params.senv } )
    | Cnf (cnf, params) ->
      let pvs = Set.Poly.union unpreprocessable_pvs @@ ClauseSet.pvs_of cnf in
      Cnf (cnf, { params with senv = Map.Poly.filter_keys ~f:(Set.Poly.mem pvs) params.senv })
  in
  let pvs = pvs_of pcsp' in
  let partial_sol_targets' =
    partial_sol_targets_of pcsp'
    |> Map.Poly.filteri ~f:(fun ~key ~data:_ ->
        Set.Poly.exists pvs ~f:(fun pv -> is_ord_pred pcsp pv && Ident.is_related_tvar pv key))
  in
  update_params pcsp' { (params_of pcsp') with partial_sol_targets = partial_sol_targets' }

let normalize_uni_senv = function
  | Raw (phis, params) ->
    let phis =
      Set.Poly.map phis ~f:(fun (senv, phi) ->
          let vars = List.sort ~compare:Ident.tvar_compare @@ Map.Poly.keys senv in
          let sub =
            Map.Poly.of_alist_exn @@
            List.mapi vars ~f:(fun i tvar -> tvar, Ident.Tvar (sprintf "x%d" i))
          in
          Map.rename_keys_and_drop_unused senv ~f:(Map.Poly.find sub),
          Logic.ExtTerm.rename sub phi)
    in
    let params =
      { params with unpreprocessable_clauses =
                      Set.Poly.map ~f:Clause.normalize_uni_senv @@
                      params.Params.unpreprocessable_clauses }
    in
    Raw (phis, params)
  | Cnf (cls, params) ->
    let cls = Set.Poly.map cls ~f:Clause.normalize_uni_senv in
    let params =
      { params with unpreprocessable_clauses =
                      Set.Poly.map ~f:Clause.normalize_uni_senv @@
                      params.Params.unpreprocessable_clauses }
    in
    Cnf (cls, params)
let ast_size_of pcsp =
  let unpreprocessable_ast =
    Set.Poly.fold ~init:0 ~f:(fun acc cl -> 1 + acc + Clause.ast_size_of cl) @@
    unpreprocessable_clauses_of pcsp
  in
  unpreprocessable_ast +
  match pcsp with
  | Raw (phis, _) -> Set.Poly.fold phis ~init:0 ~f:(fun acc (_, t) -> 1 + acc + ExtTerm.ast_size t)
  | Cnf (cls, _) -> Set.Poly.fold cls ~init:0 ~f:(fun acc cl -> 1 + acc + Clause.ast_size_of cl)
let tag_of pcsp tvar =
  if not @@ is_nwf_pred pcsp tvar then None
  else
    match Map.Poly.find (kind_map_of pcsp) tvar with
    | Some (Kind.NWF (_, tag)) -> Some tag
    | _ -> None
let recover_elimed_params_of_sol elimed_params_logs sol =
  Map.Poly.mapi sol ~f:(fun ~key:(Ident.Tvar v) ~data:term ->
      let pvar = Ident.Pvar v in
      if not @@ Map.Poly.mem elimed_params_logs pvar then term
      else
        let arr, args = Map.Poly.find_exn elimed_params_logs pvar in
        let senv, term = Logic.Term.let_lam term in
        let senv = ref senv in
        let senv' =
          List.mapi args ~f:(fun i arg ->
              if Array.get arr i then begin
                match !senv with
                | hd :: tl -> senv := tl; hd
                | [] -> assert false
              end
              else (Ident.mk_fresh_tvar (), arg))
        in
        Logic.Term.mk_lambda senv' term)

let sol_of_candidate pcsp (cand: CandSol.t) =
  Map.force_merge (sol_for_eliminated_of pcsp) (CandSol.to_subst cand)
  |> recover_elimed_params_of_sol (args_record_of pcsp)

let elim_dup_nwf_predicate pcsp =
  let id_log = Hashtbl.Poly.create () in
  let visited = Hash_set.Poly.create () in
  let kind_map = kind_map_of pcsp in
  let pcsp' = to_cnf @@ to_nnf pcsp in
  Set.Poly.iter (clauses_of pcsp') ~f:(fun (_, ps, ns, _) ->
      Set.Poly.iter (Set.Poly.union ps ns) ~f:(fun atm ->
          match Map.Poly.find kind_map @@ fst @@ ExtTerm.let_var_app atm with
          | Some (Kind.NWF (nwf, (idl, idr)))
            when not @@ Hash_set.Poly.mem visited (nwf.name, idl, idr) ->
            Hash_set.Poly.add visited (nwf.name, idl, idr);
            Hashtbl.Poly.update id_log (nwf.name, idl) ~f:(function None -> 1 | Some i -> i + 1);
            Hashtbl.Poly.update id_log (nwf.name, idr) ~f:(function None -> 1 | Some i -> i + 1);
          | _ -> ()));
  let clauses' =
    Set.Poly.filter_map (clauses_of pcsp') ~f:(fun (uni_senv, ps, ns, phi) ->
        let aux atm =
          match Map.Poly.find kind_map @@ fst @@ ExtTerm.let_var_app atm with
          | Some (Kind.NWF (nwf, (idl, idr))) ->
            Hashtbl.Poly.find_exn id_log (nwf.name, idl) > 1 &&
            Hashtbl.Poly.find_exn id_log (nwf.name, idr) > 1
          | _ -> true
        in
        if Set.Poly.exists ps ~f:(Fn.non aux) then None
        else Some (uni_senv, ps, Set.Poly.filter ns ~f:aux, phi))
  in
  match pcsp with 
  | Raw (_, params) -> 
    let phis' = Set.Poly.map clauses' ~f:(fun (uni_senv, ps, ns, phi) -> uni_senv, Clause.to_formula @@ (uni_senv, ps, ns, phi)) in
    Raw (phis', params)
  | Cnf (_, params) -> Cnf (clauses', params)

(** assume pcsp is cnf *)
let merge_clauses pcsp =
  let mk_flag atms =
    Set.Poly.to_list atms
    |> List.map ~f:(fun t -> fst @@ ExtTerm.let_var_app t)
    |> List.sort ~compare:Stdlib.compare
  in
  let sorted_atms atms =
    Set.Poly.to_list atms
    |> List.sort ~compare:(fun atm1 atm2 -> 
        let p1 = fst @@ ExtTerm.let_var_app atm1 in 
        let p2 = fst @@ ExtTerm.let_var_app atm2 in 
        Stdlib.compare p1 p2)
  in
  let unify_atm atm1 atm2 =
    let p1, args1 = ExtTerm.let_var_app atm1 in
    let p2, args2 = ExtTerm.let_var_app atm2 in
    if Stdlib.(p1 = p2) then
      let tvars1, tvars2 = 
        List.map args1 ~f:(fun t -> fst @@ ExtTerm.let_var t), 
        List.map args2 ~f:(fun t -> fst @@ ExtTerm.let_var t)
      in
      List.zip_exn tvars1 tvars2 |> Map.Poly.of_alist_exn
    else Map.Poly.empty
  in
  let clauses = clauses_of pcsp in
  let senv = senv_of pcsp in
  let params = params_of pcsp in
  let clauses =
    Set.Poly.map ~f:(fun c -> Clause.refresh_tvar c |> Clause.refresh_pvar_args senv) clauses
    |> Set.Poly.to_list
    |> List.map ~f:(fun (uni_senv, ps, ns, phi) ->
        let flag_head = mk_flag ps in 
        let flag_body = mk_flag ns in
        (flag_head, flag_body), (uni_senv, sorted_atms ps, sorted_atms ns, phi))
    |> List.classify (fun (flag1, _) (flag2, _) -> Stdlib.(flag1 = flag2))
    |> List.concat_map ~f:(fun cls ->
        let (flag_head, flag_body) = fst @@ List.hd_exn cls in
        let cls = List.map ~f:snd cls in
        if List.length cls <= 1 || 
           List.length flag_head <> Set.Poly.length (Set.Poly.of_list flag_head) ||
           List.length flag_body <> Set.Poly.length (Set.Poly.of_list flag_body) 
        then cls
        else
          let uni_senvs, ps, ns, phiss =
            List.fold cls ~init:([], [], [], [])
              ~f:(fun (uni_senvs, ps, ns, phis) (uni_senv0, ps0, ns0, phi0) ->
                  if List.is_empty uni_senvs then [uni_senv0], ps0, ns0, [phi0]
                  else
                    let subst =
                      List.fold2_exn ps0 ps ~init:Map.Poly.empty ~f:(fun acc atm atm0 ->
                          Map.force_merge acc (unify_atm atm atm0))
                    in
                    let subst =
                      List.fold2_exn ns0 ns ~init:subst ~f:(fun acc atm atm0 ->
                          Map.force_merge acc (unify_atm atm atm0))
                    in
                    (uni_senv0::uni_senvs, ps, ns, ExtTerm.rename subst phi0 :: phis))
          in
          [Map.force_merge_list uni_senvs, ps, ns, ExtTerm.and_of phiss])
    |> List.map ~f:(fun (uni_senv, ps, ns, phi) ->
        uni_senv, Set.Poly.of_list ps, Set.Poly.of_list ns, phi)
    |> Set.Poly.of_list
  in
  of_clauses ~params clauses

let is_qualified_partial_solution pvars_the_target_pvar_depends_on target_pvars violated_non_query_clauses =
  not @@ Set.Poly.exists violated_non_query_clauses
    ~f:(Clause.is_clause_must_satisfy target_pvars pvars_the_target_pvar_depends_on)

let make ?(skolem_pred=false) = fun (phis, _, pvs, fnp_env, wfp_env, fenv, dtenv) ->
  let fenv =
    let size_fenv =
      Map.Poly.to_alist dtenv
      |> List.filter ~f:(fun (_, dt) ->
          Fn.non LogicOld.Datatype.is_poly dt
          (*ToDo: generate size functions for polymorphic datatypes*))
      |> List.map ~f:(fun (_, dt) -> LogicOld.Datatype.size_fun_of dt)
      |> Map.Poly.of_alist_exn
    in
    Map.force_merge size_fenv @@
    Map.Poly.filter fenv ~f:(fun (_, _, _, is_rec, _) -> is_rec)
  in
  LogicOld.update_ref_fenv fenv;
  let dummy_sus_senv =
    Map.Poly.fold dtenv ~init:[] ~f:(fun ~key ~data senv ->
        if LogicOld.Datatype.is_undef data then
          (Ident.Tvar ("dummy_" ^ key),
           LogicOld.T_dt.SUS (key, LogicOld.Datatype.args_of data)) ::
          senv
        else senv)
  in
  Atomic.set LogicOld.dummy_term_senv dummy_sus_senv;
  let exi_senv =
    let senv_set =
      Set.Poly.union_list [pvs; fnp_env; wfp_env]
      |> Set.Poly.map ~f:(fun (Ident.Pvar x, sorts) ->
          let sort = Sort.mk_fun (List.map sorts ~f:ExtTerm.of_old_sort @ [ExtTerm.SBool]) in
          (Ident.Tvar x, sort))
    in
    try Map.of_set_exn senv_set with _ ->
      failwith @@
      String.concat_map_set ~sep:"\n" senv_set ~f:(fun (Ident.Tvar x, sort) ->
          sprintf "%s: %s" x (ExtTerm.str_of_sort sort))
  in
  (if skolem_pred then
     List.rev_map phis ~f:(fun phi ->
         let senv, fsenv, phi =
           LogicOld.Formula.skolemize_pred @@ LogicOld.Formula.nnf_of phi
         in
         let new_fnp_env =
           Set.Poly.of_list @@
           List.map fsenv ~f:(fun (Ident.Pvar x, sort) ->
               Ident.Tvar x, Logic.ExtTerm.of_old_sort sort)
         in
         Map.of_set_exn @@ new_fnp_env,
         Set.Poly.map ~f:fst new_fnp_env,
         (Logic.of_old_sort_env_map ExtTerm.of_old_sort senv, ExtTerm.of_old_formula phi))
   else
     List.rev_map phis ~f:(fun phi ->
         let senv, fsenv, phi = LogicOld.Formula.skolemize_fun @@ LogicOld.Formula.nnf_of phi in
         (*print_endline ("phi: " ^ LogicOld.Formula.str_of phi);*)
         Map.of_list_exn @@ List.map fsenv ~f:(fun (x, sort) -> x, Logic.ExtTerm.of_old_sort sort),
         Set.Poly.empty,
         (Logic.of_old_sort_env_map ExtTerm.of_old_sort senv, ExtTerm.of_old_formula phi)))
  |> List.unzip3
  |> (fun (fsenv_list, fnpvs_list, phis) ->
      let senv = Map.force_merge_list (exi_senv :: fsenv_list) in
      (*List.iter phis ~f:(fun (usenv, phi) ->
         print_endline ("phi: " ^ LExtTerm.ExTerm.str_of_formula senv usenv phi));*)
      let fnpvs =
        Set.Poly.union_list @@
        Set.Poly.map fnp_env ~f:(fun (Ident.Pvar x, _) -> Ident.Tvar x) :: fnpvs_list
      in
      let wfpvs = Set.Poly.map wfp_env ~f:(fun (Ident.Pvar x, _) -> Ident.Tvar x) in
      Set.Poly.of_list phis
      |> of_formulas ~params:(Params.make ~fnpvs ~wfpvs ~fenv ~dtenv senv)
      |> update_params_dtenv)
(*|> normalize*)
