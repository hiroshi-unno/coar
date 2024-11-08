open Core
open Graph
open Common.Ext
open Common.Combinator
open Ast
open Ast.Logic

type t =
  | Raw of (sort_env_map * term) Set.Poly.t * Params.t
  | Cnf of ClauseSet.t * Params.t

type solution =
  | Sat of term_subst_map
  | Unsat of LogicOld.Formula.t option
  | Unknown
  | OutSpace of Ident.tvar list
  | Timeout

type oracle = CandSolOld.t option

let lts_str_of_solution = function
  | Sat _ -> "YES"
  | Unsat _ -> "NO"
  | Unknown | OutSpace _ | Timeout -> "MAYBE"

type bounds = (Ident.tvar, int * (sort_env_map * term)) Map.Poly.t

type Common.Messenger.info +=
  | CandidateSolution of
      (term_subst_map
      * term_subst_map
      * ClauseSet.t
      * ClauseSet.t
      * (sort_env_map * LogicOld.FunEnv.t * (Ident.tvar, term) Hashtbl.Poly.t)
        option)
  | LowerBounds of bounds
  | UpperBounds of bounds

module type ProblemType = sig
  val problem : t
end

let of_formulas ?(params = Params.empty) phis = Raw (phis, params)

let of_old_formulas ?(params = Params.empty) =
  Set.Poly.map ~f:ExtTerm.of_old >> of_formulas ~params

let of_clauses ?(params = Params.empty) cs = Cnf (cs, params)
let params_of = function Raw (_, params) | Cnf (_, params) -> params
let senv_of pcsp = (params_of pcsp).Params.senv
let kind_map_of pcsp = (params_of pcsp).Params.kind_map
let kind_of pcsp = Map.Poly.find_exn (kind_map_of pcsp)

let kindpvs_of_aux pcsp is_kind =
  (params_of pcsp).Params.kind_map |> Map.Poly.filter ~f:is_kind
  |> Map.Poly.filter_keys ~f:(Map.Poly.mem (senv_of pcsp))
  |> Map.key_set

let fnpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_fn
let nepvs_of pcsp = kindpvs_of_aux pcsp Kind.is_ne
let wfpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_wf
let dwfpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_dwf
let nwfpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_nwf
let admpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_adm
let integpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_integ

let fnpvs_senv_of pcsp =
  let fnpvs = fnpvs_of pcsp in
  Map.Poly.filter_keys (senv_of pcsp) ~f:(Set.mem fnpvs)

let nepvs_senv_of pcsp =
  let nepvs = nepvs_of pcsp in
  Map.Poly.filter_keys (senv_of pcsp) ~f:(Set.mem nepvs)

let wfpvs_senv_of pcsp =
  let wfpvs = wfpvs_of pcsp in
  Map.Poly.filter_keys (senv_of pcsp) ~f:(Set.mem wfpvs)

let dwfpvs_senv_of pcsp =
  let dwfpvs = dwfpvs_of pcsp in
  Map.Poly.filter_keys (senv_of pcsp) ~f:(Set.mem dwfpvs)

let nwfpvs_senv_of pcsp =
  Map.Poly.filter_mapi (senv_of pcsp) ~f:(fun ~key ~data:_ ->
      match Map.Poly.find (kind_map_of pcsp) key with
      | Some (Kind.NWF (nwf, (idl, idr))) ->
          Some
            ( nwf.name,
              nwf.param_sorts,
              idl,
              Kind.sorts_of_tag nwf idl,
              idr,
              Kind.sorts_of_tag nwf idr )
      | _ -> None)

let npfvs_of pcsp =
  Set.Poly.filter_map
    (Map.to_set @@ senv_of pcsp)
    ~f:(fun (x, s) ->
      if Fn.non BoolTerm.is_bool_sort @@ Sort.ret_of s then Some x else None)

let pvs_of pcsp =
  Set.Poly.filter_map
    (Map.to_set @@ senv_of pcsp)
    ~f:(fun (x, s) ->
      if BoolTerm.is_bool_sort @@ Sort.ret_of s then Some x else None)

let dtenv_of pcsp = (params_of pcsp).Params.dtenv
let fenv_of pcsp = (params_of pcsp).Params.fenv
let sol_space_of pcsp = (params_of pcsp).Params.sol_space
let messenger_of pcsp = (params_of pcsp).Params.messenger
let sol_for_eliminated_of pcsp = (params_of pcsp).Params.sol_for_eliminated
let args_record_of pcsp = (params_of pcsp).Params.args_record
let stable_clauses_of pcsp = (params_of pcsp).Params.stable_clauses
let partial_sol_targets_of pcsp = (params_of pcsp).Params.partial_sol_targets
let dep_graph_of pcsp = (params_of pcsp).Params.dep_graph
let id_of pcsp = (params_of pcsp).id

let is_ord_pred pcsp x =
  Params.is_kind (params_of pcsp) Kind.is_ord x
  &&
  (*ToDo*)
  match Map.Poly.find (senv_of pcsp) x with
  | None -> false
  | Some s -> BoolTerm.is_bool_sort @@ Sort.ret_of s

let is_fn_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_fn
let is_ne_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_ne
let is_wf_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_wf
let is_dwf_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_dwf
let is_nwf_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_nwf
let is_adm_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_adm

let is_adm_pred_with_cond pcsp =
  Params.is_kind (params_of pcsp) Kind.is_adm_with_cond

let is_integ_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_integ

let is_int_fun pcsp x =
  Params.is_kind (params_of pcsp) Kind.is_int_fun x
  &&
  (*ToDo*)
  match Map.Poly.find (senv_of pcsp) x with
  | None -> false
  | Some s -> IntTerm.is_int_sort @@ Sort.ret_of s

let is_regex pcsp x =
  Params.is_kind (params_of pcsp) Kind.is_regex x
  &&
  (*ToDo*)
  match Map.Poly.find (senv_of pcsp) x with
  | None -> false
  | Some s -> Stdlib.(s = ExtTerm.SRegEx)

let clauses_of ?(full_clauses = true) = function
  | Raw _ -> failwith "The pfwCSP is not of CNF @ clauses_of"
  | Cnf (cnf, params) ->
      if full_clauses then Set.union cnf params.Params.stable_clauses else cnf

let formulas_of ?(full_clauses = true) = function
  | Raw (phis, params) ->
      Set.union phis @@ ClauseSet.to_formulas
      @@ if full_clauses then params.Params.stable_clauses else Set.Poly.empty
  | Cnf (cnf, params) ->
      Set.union (ClauseSet.to_formulas cnf)
      @@ ClauseSet.to_formulas
      @@ if full_clauses then params.Params.stable_clauses else Set.Poly.empty

let formula_of ?(full_clauses = true) pcsp =
  let senvs, ts = Set.unzip @@ formulas_of ~full_clauses pcsp in
  ( Map.force_merge_list @@ Set.to_list @@ senvs,
    BoolTerm.and_of @@ Set.to_list ts )

let old_formulas_of ?(full_clauses = true) = function
  | Raw (phis, params) ->
      Set.union (Set.Poly.map ~f:(ExtTerm.to_old_fml params.senv) phis)
      @@ Set.Poly.map ~f:(Clause.to_old_formula params.senv)
      @@ if full_clauses then params.Params.stable_clauses else Set.Poly.empty
  | Cnf (cnf, params) ->
      ClauseSetOld.to_formulas
      @@ ClauseSet.to_old_clause_set params.senv
      @@ Set.union cnf
      @@ if full_clauses then params.Params.stable_clauses else Set.Poly.empty

let old_formula_of ?(full_clauses = true) pcsp =
  LogicOld.Formula.and_of @@ Set.to_list @@ old_formulas_of ~full_clauses pcsp

let num_constrs pcsp = Set.length @@ formulas_of pcsp
let num_pvars pcsp = Set.length @@ pvs_of pcsp
let num_unknowns pcsp = Map.Poly.length @@ senv_of pcsp

let dtenv_of_def pcsp =
  let exi_senv = (params_of pcsp).senv in
  Set.fold ~init:Map.Poly.empty (formulas_of pcsp) ~f:(fun ret ->
      ExtTerm.to_old_fml exi_senv
      >> LogicOld.DTEnv.of_formula
      >> LogicOld.DTEnv.force_merge ret)

let map_params ~f = function
  | Raw (phis, params) -> Raw (phis, f params)
  | Cnf (cls, params) -> Cnf (cls, f params)

let update_params pcsp params =
  match pcsp with
  | Raw (phis, _) -> Raw (phis, params)
  | Cnf (cls, _) -> Cnf (cls, params)

let update_params_dtenv pcsp =
  update_params pcsp
  @@ {
       (params_of pcsp) with
       dtenv = Map.force_merge (dtenv_of pcsp) @@ dtenv_of_def pcsp;
     }

let set_params_sol_space pcsp sol_space =
  update_params pcsp { (params_of pcsp) with sol_space }

let is_raw = function Raw _ -> true | Cnf _ -> false
let is_cnf = function Raw _ -> false | Cnf _ -> true

let map_if_raw ~f = function
  | Raw (phis, params) -> Raw (f phis, params)
  | _cnf -> failwith "cnf not supported"

let map_if_raw_no_exn ~f = function
  | Raw (phis, params) -> Raw (f phis, params)
  | cnf -> cnf

let map_if_raw_old ~f pcsp =
  let exi_senv = (params_of pcsp).senv in
  let f =
    Set.Poly.map ~f:(fun (uni_senv, phi) ->
        ( Map.of_set_exn @@ Map.to_set @@ to_old_sort_env_map uni_senv,
          ExtTerm.to_old_fml exi_senv (uni_senv, phi) ))
    >> f
    >> Set.Poly.map ~f:ExtTerm.of_old
  in
  map_if_raw ~f pcsp

let map ~f = function
  | Raw (phis, params) -> Raw (Set.Poly.map ~f phis, params)
  | Cnf (cls, params) -> Cnf (ClauseSet.map_formula ~f cls, params)

let map_old ~f pcsp =
  let exi_senv = (params_of pcsp).senv in
  let f =
    (fun (uni_senv, phi) ->
      ( Map.of_set_exn @@ Map.to_set @@ to_old_sort_env_map uni_senv,
        ExtTerm.to_old_fml exi_senv (uni_senv, phi) ))
    >> f >> ExtTerm.of_old
  in
  map ~f pcsp

type pcsp = { clauses : string list; unknowns : (string * string) list }
[@@deriving to_yojson]

let to_yojson pcsp =
  let exi_senv = (params_of pcsp).senv in
  {
    clauses =
      pcsp |> formulas_of
      |> Set.Poly.map ~f:(uncurry (ExtTerm.str_of_formula exi_senv))
      |> Set.to_list;
    unknowns =
      senv_of pcsp |> Map.Poly.to_alist
      |> List.map ~f:(fun (Ident.Tvar name, sort) ->
             (name, ExtTerm.str_of_sort sort));
  }
  |> pcsp_to_yojson

let str_of pcsp =
  sprintf
    "%s\n\nsort env: %s\n\ndatatype env:\n%s\n\nfun env:\n%s\n\nsol_space: %s"
    (String.concat_map_set ~sep:"\n" (formulas_of pcsp)
       ~f:(fun (uni_senv, phi) ->
         String.bracket (string_of_int (Map.Poly.length uni_senv))
         ^ " "
         ^ ExtTerm.str_of_formula (params_of pcsp).senv uni_senv phi))
    (str_of_sort_env_list (fun (s, k) ->
         ExtTerm.str_of_sort s ^ " @ " ^ Kind.short_str_of k)
    @@ Map.Poly.to_alist
    @@ Map.Poly.mapi ~f:(fun ~key ~data ->
           (data, try kind_of pcsp key with _ -> Kind.Ord (*ToDo*)))
    @@ senv_of pcsp)
    (LogicOld.DTEnv.str_of @@ dtenv_of pcsp)
    (LogicOld.FunEnv.str_of @@ fenv_of pcsp)
    (SolSpace.str_of @@ sol_space_of pcsp)
(*let str_of_senv pcsp = "sort env: " ^ str_of_sort_env_map ExtTerm.str_of_sort @@ senv_of pcsp*)

let str_of_info pcsp =
  sprintf "number of unknowns: %d, number of constraints: %d"
    (num_unknowns pcsp) (num_constrs pcsp)

let str_of_solution ?(print_witness = false) = function
  | Sat subst ->
      "sat"
      ^
      if print_witness then
        " where\n" ^ Logic.str_of_term_subst ExtTerm.str_of subst
      else ""
  | Unsat _ -> "unsat"
  | Unknown -> "unknown"
  | OutSpace pvs ->
      sprintf "out_space: %s"
      @@ String.concat_map_list ~sep:"," pvs ~f:Ident.name_of_tvar
  | Timeout -> "timeout"

let str_of_sol_with_witness = str_of_solution ~print_witness:true
let str_of_solution = str_of_solution ~print_witness:false

let str_of_sygus_solution = function
  | Sat sol -> SyGuS.Printer.str_of_solution @@ CandSolOld.of_subst sol
  | Unsat _ -> SyGuS.Printer.str_of_unsat ()
  | Unknown -> SyGuS.Printer.str_of_unknown ()
  | OutSpace pvs ->
      sprintf "out_space: %s"
      @@ String.concat_map_list ~sep:"," pvs ~f:Ident.name_of_tvar
  | Timeout -> "timeout" (*ToDo*)

(* expand existential quantification over boolean variables *)
let rec qelim xs body =
  let open LogicOld in
  match xs with
  | [] -> body
  | (x, sort) :: xs' ->
      assert (Term.is_bool_sort sort);
      let body = qelim xs' body in
      Formula.or_of
        [
          Formula.apply_pred (x, body) @@ T_bool.mk_true ();
          Formula.apply_pred (x, body) @@ T_bool.mk_false ();
        ]

let add_non_emptiness (pvar, sorts) =
  let open LogicOld in
  function
  | Raw (phis, p_params) ->
      let params = sort_env_list_of_sorts sorts in
      let bool_params, arith_params =
        List.partition_tf params ~f:(snd >> Term.is_bool_sort)
      in
      let pvs =
        List.map arith_params ~f:(fun (tvar, sort) ->
            let pvar =
              Ident.Pvar ("FN" ^ Ident.divide_flag ^ Ident.name_of_tvar tvar)
            in
            ( ExtTerm.of_old_sort_bind @@ Term.pred_to_sort_bind (pvar, [ sort ]),
              Formula.mk_atom
              @@ Atom.mk_pvar_app pvar [ sort ] [ Term.mk_var tvar sort ] ))
      in
      let phis =
        Set.add phis
        @@ ( Map.Poly.of_alist_exn @@ of_old_sort_env_list params,
             BoolTerm.elim_imp @@ ExtTerm.of_old_formula @@ Evaluator.simplify
             @@ Formula.mk_imply (Formula.and_of @@ List.map pvs ~f:snd)
             @@ qelim bool_params @@ Formula.mk_atom
             @@ Atom.mk_pvar_app pvar sorts (Term.of_sort_env params) )
      in
      let p_params =
        let fnpv_senv = Map.Poly.of_alist_exn @@ List.map pvs ~f:fst in
        {
          p_params with
          senv = Map.force_merge p_params.senv fnpv_senv;
          kind_map =
            Kind.add_kinds (Map.key_set fnpv_senv) Kind.FN p_params.kind_map;
        }
      in
      Raw (phis, p_params)
  | Cnf (_, _) -> failwith "add_non_emptiness"

let add_formula (senv, phi) = function
  | Raw (phis, params) ->
      Raw (Set.add phis (senv, BoolTerm.elim_imp phi), params)
  | Cnf (_, _) -> failwith "add_formula"

let add_formulas senv_phis = function
  | Raw (phis, params) ->
      Raw
        ( Set.union phis
            (Set.Poly.map senv_phis ~f:(fun (senv, phi) ->
                 (senv, BoolTerm.elim_imp phi))),
          params )
  | Cnf (_, _) -> failwith "add_formula"

let add_clause clause = function
  | Raw (_, _) -> failwith "The pfwCSP is not of CNF @ add_clause"
  | Cnf (cnf, params) -> Cnf (Set.add cnf clause, params)

let add_clauses clauses = function
  | Raw (_, _) -> failwith "The pfwCSP is not of CNF @ add_clauses"
  | Cnf (cnf, params) -> Cnf (Set.union cnf clauses, params)

let to_nnf = function
  | Raw (phis, params) ->
      Raw
        ( Set.Poly.map phis ~f:(fun (senv, phi) -> (senv, BoolTerm.nnf_of phi)),
          params )
  | cnf -> cnf

let to_cnf = function
  | Raw (phis, params) -> Cnf (ClauseSet.of_formulas params.senv phis, params)
  | cnf -> cnf

let divide pcsp =
  pcsp |> to_nnf |> to_cnf |> function
  | Raw (_, _) -> failwith "The pfwCSP is not of CNF @ divide"
  | Cnf (cnf, params) ->
      let cnf1, cnf2 =
        Set.partition_tf cnf
          ~f:(Clause.is_query (wfpvs_of pcsp) (fnpvs_of pcsp))
      in
      Set.to_list
      @@ Set.Poly.map cnf1 ~f:(fun c -> Cnf (Set.add cnf2 c, params))

let merge_sols _pcsp sols =
  let merge _s s' = s' (* ToDo *) in
  let rec inner sol = function
    | [] -> Sat sol
    | Sat sol' :: sols -> inner (merge sol sol') sols
    | Unsat cex :: _sols -> Unsat cex
    | Unknown :: _sols -> Unknown
    | OutSpace pvs :: _sols -> OutSpace pvs
    | Timeout :: _sols -> Timeout
  in
  inner Map.Poly.empty sols

let extend_sol sol sol' =
  match sol with
  | Sat sol -> Sat (Map.force_merge sol sol')
  | Unsat _ | Unknown | OutSpace _ | Timeout -> sol
(*let nest_subst subst =
  let keys = Map.key_set subst in
  let rec inner subst =
    let subst = Map.Poly.map subst ~f:(ExtTerm.subst subst) in
    if Map.Poly.exists subst ~f:(fun term ->
        Set.exists (ExtTerm.fvs_of term) ~f:(Set.mem keys)) then inner subst
    else subst
  in
  inner subst*)

let svs_of = function
  | Raw (phis, _params) ->
      Set.concat_map phis
        ~f:(snd >> Term.svs_of ExtTerm.svs_of_sym ExtTerm.svs_of_sort)
  | Cnf (cnf, _params) -> ClauseSet.svs_of cnf

let instantiate_svars_to_int pcsp =
  let sub =
    Map.of_set_exn
    @@ Set.Poly.map (svs_of pcsp) ~f:(fun svar -> (svar, LogicOld.T_int.SInt))
  in
  map_old pcsp ~f:(fun (uni_senv, phi) ->
      (uni_senv, LogicOld.Formula.subst_sorts sub phi))

let normalize pcsp =
  let unknowns = Map.key_set @@ senv_of pcsp in
  map_old pcsp ~f:(fun (uni_senv, phi) ->
      let phi' =
        phi
        (*|> LogicOld.Formula.elim_pvars unknowns*)
        |> Normalizer.normalize_let ~rename:true
        (* |> LogicOld.Formula.elim_let_equivalid *)
        |> LogicOld.Formula.elim_let_with_unknowns unknowns
        (* |> LogicOld.Formula.elim_let *)
        |> Normalizer.normalize
        |> Evaluator.simplify
      in
      (*print_endline @@ sprintf "[normalize] \n  before: %s\n  after: %s\n" (LogicOld.Formula.str_of phi) (LogicOld.Formula.str_of phi');*)
      (uni_senv, phi'))

let of_sygus (synth_funs, declared_vars, terms) =
  let exi_senv = Map.Poly.map synth_funs ~f:fst in
  let kind_map =
    Map.Poly.filter_map exi_senv ~f:(fun sort ->
        if ExtTerm.is_int_sort @@ Sort.ret_of sort then
          Some Kind.IntFun (*ToDo*)
        else if ExtTerm.is_regex_sort sort then Some Kind.RegEx
        else None)
  in
  List.map terms ~f:(fun t -> (declared_vars, t))
  |> Set.Poly.of_list
  |> of_formulas ~params:(Params.make ~kind_map exi_senv)
  |> normalize

let of_lts _lts = failwith "not implemented"

let remove_unused_params pcsp =
  let pcsp' =
    let bpvs = ClauseSet.pvs_of @@ stable_clauses_of pcsp in
    match pcsp with
    | Raw (phis, params) ->
        let mem =
          Set.mem @@ Set.union bpvs
          @@ Set.concat_map phis ~f:(snd >> Term.fvs_of)
        in
        Raw
          (phis, { params with senv = Map.Poly.filter_keys ~f:mem params.senv })
    | Cnf (cnf, params) ->
        let mem = Set.mem @@ Set.union bpvs @@ ClauseSet.fvs_of cnf in
        Cnf (cnf, { params with senv = Map.Poly.filter_keys ~f:mem params.senv })
  in
  let partial_sol_targets =
    let pvs = pvs_of pcsp' in
    Map.Poly.filter_keys (partial_sol_targets_of pcsp') ~f:(fun k ->
        Set.exists pvs ~f:(fun pv ->
            is_ord_pred pcsp pv && Ident.is_related_tvar pv k))
  in
  update_params pcsp' @@ { (params_of pcsp') with partial_sol_targets }

let normalize_uni_senv = function
  | Raw (phis, params) ->
      Raw
        ( Set.Poly.map phis ~f:Clause.normalize_uni_senv_formula,
          {
            params with
            stable_clauses =
              Set.Poly.map ~f:Clause.normalize_uni_senv @@ params.stable_clauses;
          } )
  | Cnf (cls, params) ->
      Cnf
        ( Set.Poly.map cls ~f:Clause.normalize_uni_senv,
          {
            params with
            stable_clauses =
              Set.Poly.map ~f:Clause.normalize_uni_senv @@ params.stable_clauses;
          } )

let ast_size_of pcsp =
  Set.fold ~init:0
    ~f:(fun acc cl -> 1 + acc + Clause.ast_size_of cl)
    (stable_clauses_of pcsp)
  +
  match pcsp with
  | Raw (phis, _) ->
      Set.fold phis ~init:0 ~f:(fun acc (_, t) -> 1 + acc + ExtTerm.ast_size t)
  | Cnf (cls, _) ->
      Set.fold cls ~init:0 ~f:(fun acc cl -> 1 + acc + Clause.ast_size_of cl)

let tag_of pcsp tvar =
  if not @@ is_nwf_pred pcsp tvar then None
  else
    match Map.Poly.find (kind_map_of pcsp) tvar with
    | Some (Kind.NWF (_, tag)) -> Some tag
    | _ -> None

let recover_elimed_params_of_sol elimed_params_logs =
  Map.Poly.mapi ~f:(fun ~key ~data:term ->
      let pvar = Ident.tvar_to_pvar key in
      if not @@ Map.Poly.mem elimed_params_logs pvar then term
      else
        let arr, args = Map.Poly.find_exn elimed_params_logs pvar in
        let senv, term = Term.let_lam term in
        let senv = ref senv in
        let senv' =
          List.mapi args ~f:(fun i arg ->
              if Array.get arr i then
                match !senv with
                | hd :: tl ->
                    senv := tl;
                    hd
                | [] -> assert false
              else (Ident.mk_fresh_tvar (), arg))
        in
        Term.mk_lambda senv' term)

let sol_of_candidate pcsp (cand : CandSol.t) =
  recover_elimed_params_of_sol (args_record_of pcsp)
  @@ Map.force_merge (sol_for_eliminated_of pcsp) (CandSol.to_subst cand)

(* assume the codomain of subst is pure *)
let subst ?(bpvs = Set.Poly.empty) ?(elim = true) subst pcsp =
  let phis = formulas_of pcsp in
  let params = params_of pcsp in
  let subst = Map.Poly.filter_keys subst ~f:(Fn.non @@ Set.mem bpvs) in
  let params' =
    if elim then
      {
        params with
        Params.senv =
          Map.Poly.filter_keys params.Params.senv ~f:(Map.Poly.mem subst >> not);
        Params.kind_map =
          Map.Poly.filter_keys params.Params.kind_map
            ~f:(Map.Poly.mem subst >> not);
      }
    else { params with Params.sol_for_eliminated = subst }
  in
  (*let c = ref 0 in*)
  let phis =
    Set.Poly.map phis ~f:(fun (univ_senv, phi) ->
        (*print_endline @@ string_of_int !c;
          c := !c + 1;*)
        (*let fvs = ExtTerm.fvs_of phi in
          let sub = Map.Poly.filter_keys subst ~f:(Set.mem fvs) in
          if Map.Poly.is_empty sub then (univ_senv, phi)
          else*)
        (univ_senv, ExtTerm.subst subst phi))
  in
  of_formulas phis ~params:params'
  |>
  if true then Fn.id
  else
    map_old ~f:(fun (uni_senv, phi) ->
        ( uni_senv,
          Z3Smt.Z3interface.qelim
            ~id:(id_of pcsp) (*(senv_of pcsp)*)
            ~fenv:(LogicOld.get_fenv ()) phi ))

let cochc_to_chc pcsp =
  let senv = senv_of pcsp in
  let sub =
    Map.Poly.filter_mapi senv ~f:(fun ~key ~data ->
        if Kind.is_ord @@ kind_of pcsp key then (
          let sargs, sret = Sort.args_ret_of data in
          let params = sort_env_list_of_sorts sargs in
          let args = List.map params ~f:(fst >> ExtTerm.mk_var) in
          assert (BoolTerm.is_bool_sort sret);
          Some
            (ExtTerm.mk_lambda params @@ BoolTerm.neg_of
            @@ ExtTerm.mk_var_app key args))
        else None)
  in
  subst ~elim:false (*ToDo*) sub pcsp

let elim_unsat_wf_predicates ~print pcsp =
  let open Logic in
  if Map.Poly.exists (kind_map_of pcsp) ~f:Kind.is_wf then
    let replace_wf_term term =
      let pv, args = ExtTerm.let_var_app term in
      if is_wf_pred pcsp pv then (
        let length = List.length args / 2 in
        assert (List.length args mod 2 = 0);
        let args_l, args_r = (List.take args length, List.drop args length) in
        if Stdlib.(args_l = args_r) then (
          print @@ lazy (sprintf "eliminating %s" @@ ExtTerm.str_of term);
          ExtTerm.mk_bool false)
        else term)
      else term
    in
    map pcsp ~f:(fun (uni_senv, phi) ->
        ( uni_senv,
          ExtTerm.nnf_of phi
          |> ExtTerm.cnf_of (senv_of pcsp) uni_senv
          |> Set.Poly.(
               map ~f:(fun (ps, ns, phi) ->
                   ( uni_senv,
                     map ps ~f:replace_wf_term,
                     map ns ~f:replace_wf_term,
                     phi )))
          |> ClauseSet.to_formula ))
  else pcsp

let elim_dup_nwf_predicate pcsp =
  let kind_map = kind_map_of pcsp in
  if Map.Poly.exists kind_map ~f:Kind.is_nwf then (
    let id_log = Hashtbl.Poly.create () in
    let visited = Hash_set.Poly.create () in
    let clauses = clauses_of @@ to_cnf @@ to_nnf pcsp in
    Set.iter clauses ~f:(fun (_, ps, ns, _) ->
        Set.iter (Set.union ps ns) ~f:(fun atm ->
            match Map.Poly.find kind_map @@ ExtTerm.pvar_of_atom atm with
            | Some (Kind.NWF (nwf, (idl, idr)))
              when not @@ Hash_set.Poly.mem visited (nwf.name, idl, idr) ->
                Hash_set.Poly.add visited (nwf.name, idl, idr);
                Hashtbl.Poly.update id_log (nwf.name, idl) ~f:(function
                  | None -> 1
                  | Some i -> i + 1);
                Hashtbl.Poly.update id_log (nwf.name, idr) ~f:(function
                  | None -> 1
                  | Some i -> i + 1)
            | _ -> ()));
    let clauses' =
      Set.Poly.filter_map clauses ~f:(fun (uni_senv, ps, ns, phi) ->
          let aux atm =
            match Map.Poly.find kind_map @@ ExtTerm.pvar_of_atom atm with
            | Some (Kind.NWF (nwf, (idl, idr))) ->
                Hashtbl.Poly.find_exn id_log (nwf.name, idl) > 1
                && Hashtbl.Poly.find_exn id_log (nwf.name, idr) > 1
            | _ -> true
          in
          if Set.exists ps ~f:(Fn.non aux) then None
          else Some (uni_senv, ps, Set.filter ns ~f:aux, phi))
    in
    match pcsp with
    | Raw (_, params) ->
        let phis' =
          Set.Poly.map clauses' ~f:(fun ((senv, _, _, _) as cl) ->
              (senv, Clause.to_formula cl))
        in
        Raw (phis', params)
    | Cnf (_, params) -> Cnf (clauses', params))
  else pcsp

let elim_dup_fn_predicate pcsp =
  let open Logic in
  if Map.Poly.exists (kind_map_of pcsp) ~f:Kind.is_fn then
    map pcsp ~f:(fun (uni_senv, phi) ->
        ( uni_senv,
          ExtTerm.nnf_of phi
          |> ExtTerm.cnf_of (senv_of pcsp) uni_senv
          |> Set.Poly.(
               map ~f:(fun (ps, ns, phi) ->
                   let fnns, ns =
                     Set.partition_map ns ~f:(fun term ->
                         let pv, args = ExtTerm.let_var_app term in
                         if is_fn_pred pcsp pv then First (pv, args)
                         else Second term)
                   in
                   let ns', phiss =
                     let fvs_ps_ns_phi =
                       Set.diff
                         (Set.union (ExtTerm.fvs_of phi)
                            (Set.concat_map (Set.union ps ns) ~f:Term.fvs_of))
                         (Map.Poly.key_set @@ senv_of pcsp)
                     in
                     List.unzip
                     @@ List.map ~f:(fun pvs ->
                            let hd, tl = List.hd_tl pvs in
                            let out = List.last_exn @@ snd hd in
                            ( uncurry ExtTerm.mk_var_app hd,
                              List.map tl ~f:(fun (_, args) ->
                                  ExtTerm.neq_of
                                    (ExtTerm.sort_of uni_senv out)
                                    out (List.last_exn args)) ))
                     @@ List.classify (fun (pv1, args1) (pv2, args2) ->
                            Stdlib.(
                              pv1 = pv2
                              && Common.Ext.List.initial args1
                                 = Common.Ext.List.initial args2))
                     @@ Set.to_list
                     @@ Set.filter fnns ~f:(fun ((_, args) as fnn) ->
                            let out = List.last_exn args in
                            let fvs_fnns =
                              Set.diff
                                (Set.concat
                                @@ Set.concat_map
                                     ~f:
                                       (snd >> List.map ~f:Term.fvs_of
                                      >> Set.Poly.of_list)
                                @@ Set.remove fnns fnn)
                                (Map.Poly.key_set @@ senv_of pcsp)
                            in
                            (not (ExtTerm.is_var out))
                            || Set.mem
                                 (Set.union fvs_ps_ns_phi fvs_fnns)
                                 (fst (ExtTerm.let_var out)))
                   in
                   ( uni_senv,
                     ps,
                     Set.union ns (Set.Poly.of_list ns'),
                     ExtTerm.or_of @@ (phi :: List.concat phiss) )))
          |> ClauseSet.to_formula ))
  else pcsp

(** assume pcsp is cnf *)
let merge_clauses pcsp =
  let mk_flag =
    Set.to_list
    >> List.map ~f:ExtTerm.pvar_of_atom
    >> List.sort ~compare:Stdlib.compare
  in
  let sorted_atms =
    Set.to_list
    >> List.sort ~compare:(fun atm1 atm2 ->
           let p1 = ExtTerm.pvar_of_atom atm1 in
           let p2 = ExtTerm.pvar_of_atom atm2 in
           Stdlib.compare p1 p2)
  in
  let unify_atm atm1 atm2 =
    let p1, args1 = ExtTerm.let_var_app atm1 in
    let p2, args2 = ExtTerm.let_var_app atm2 in
    if Stdlib.(p1 = p2) then
      let tvars1 = List.map args1 ~f:(ExtTerm.let_var >> fst) in
      let tvars2 = List.map args2 ~f:(ExtTerm.let_var >> fst) in
      Map.Poly.of_alist_exn @@ List.zip_exn tvars1 tvars2
    else Map.Poly.empty
  in
  let senv = senv_of pcsp in
  clauses_of pcsp
  |> Set.Poly.map ~f:(Clause.refresh_tvar >> Clause.refresh_pvar_args senv)
  |> Set.to_list
  |> List.map ~f:(fun (uni_senv, ps, ns, phi) ->
         ( (mk_flag ps, mk_flag ns),
           (uni_senv, sorted_atms ps, sorted_atms ns, phi) ))
  |> List.classify (fun (flag1, _) (flag2, _) -> Stdlib.(flag1 = flag2))
  |> List.concat_map ~f:(fun cls ->
         let flag_head, flag_body = fst @@ List.hd_exn cls in
         let cls = List.map ~f:snd cls in
         if
           List.length cls <= 1
           || List.length flag_head <> Set.length (Set.Poly.of_list flag_head)
           || List.length flag_body <> Set.length (Set.Poly.of_list flag_body)
         then cls
         else
           let uni_senvs, ps, ns, phiss =
             List.fold cls ~init:([], [], [], [])
               ~f:(fun (uni_senvs, ps, ns, phis) (uni_senv0, ps0, ns0, phi0) ->
                 if List.is_empty uni_senvs then
                   ([ uni_senv0 ], ps0, ns0, [ phi0 ])
                 else
                   let subst =
                     Map.force_merge_list
                     @@ List.map2_exn (ps0 @ ns0) (ps @ ns) ~f:unify_atm
                   in
                   ( uni_senv0 :: uni_senvs,
                     ps,
                     ns,
                     ExtTerm.rename subst phi0 :: phis ))
           in
           [ (Map.force_merge_list uni_senvs, ps, ns, ExtTerm.and_of phiss) ])
  |> List.map ~f:(fun (uni_senv, ps, ns, phi) ->
         (uni_senv, Set.Poly.of_list ps, Set.Poly.of_list ns, phi))
  |> Set.Poly.of_list
  |> of_clauses ~params:(params_of pcsp)

let is_qualified_partial_solution ~print pvars_the_target_pvar_depends_on
    target_pvars violated_non_query_clauses =
  not
  @@ Set.exists violated_non_query_clauses
       ~f:
         (Clause.must_be_satisfied ~print target_pvars
            pvars_the_target_pvar_depends_on)

let check_valid is_valid pcsp sol =
  Set.for_all (formulas_of pcsp) ~f:(fun (uni_senv, phi) ->
      let phi' = Term.subst sol phi in
      let res = is_valid uni_senv phi' in
      (*if not res then
        print_endline @@ sprintf "before: %s\nafter: %s"
          (LogicOld.Formula.str_of @@
           ExtTerm.to_old_fml (senv_of pcsp) (uni_senv, phi))
          (LogicOld.Formula.str_of @@
           ExtTerm.to_old_fml (senv_of pcsp) (uni_senv, phi'));*)
      res)

let make ?(skolem_pred = false) phis (envs : SMT.Problem.envs) =
  let _uni_senv = of_old_sort_env_map envs.uni_senv in
  let exi_senv = of_old_sort_env_map envs.exi_senv in
  let fenv =
    let size_fenv =
      Map.Poly.of_alist_exn
      @@ List.map ~f:LogicOld.Datatype.size_fun_of
      @@ List.filter (Map.Poly.data envs.dtenv)
           ~f:
             (Fn.non
                LogicOld.Datatype.is_poly
                (*ToDo: generate size functions for polymorphic datatypes*))
    in
    Map.force_merge size_fenv
    @@ Map.Poly.filter envs.fenv ~f:Quintuple.fth (*ToDo*)
  in
  Map.Poly.iteri envs.dtenv ~f:(fun ~key ~data ->
      if LogicOld.Datatype.is_undef data then
        LogicOld.add_dummy_term (*ToDo: unnecessary?*)
          (Ident.Tvar ("dummy_" ^ key))
          (LogicOld.T_dt.SUS (key, LogicOld.Datatype.params_of data)));
  LogicOld.update_dtenv envs.dtenv;
  LogicOld.update_fenv fenv;
  let fsenvs, phis =
    List.unzip
    @@ List.rev_map phis ~f:(fun phi ->
           let _, fsenv, phi =
             LogicOld.Formula.(
               skolemize ~use_fn_pred:skolem_pred ~only_impure:true
               @@ nnf_of phi)
           in
           let fsenv = of_old_sort_env_map fsenv in
           let uni_senv =
             Map.of_set_exn
             @@ Set.filter ~f:(fst >> Map.Poly.mem fsenv >> not)
             @@ Set.filter ~f:(fst >> Map.Poly.mem exi_senv >> not)
             @@ LogicOld.Formula.sort_env_of phi
           in
           (fsenv, (uni_senv, phi)))
  in
  if false then
    List.iter phis ~f:(fun (_, phi) ->
        print_endline ("phi: " ^ LogicOld.Formula.str_of phi));
  let kind_map =
    Kind.add_kinds
      (Set.Poly.union_list @@ List.map fsenvs ~f:Map.key_set)
      (if skolem_pred then Kind.FN else Kind.IntFun)
      envs.kind_map
  in
  let params =
    Params.make ~kind_map ~fenv ~dtenv:envs.dtenv
    @@ Map.force_merge_list @@ (exi_senv :: fsenvs)
  in
  Set.Poly.of_list phis |> of_old_formulas ~params |> update_params_dtenv
(*|> normalize*)

module V = struct
  type t = Ident.tvar option

  let compare v1 v2 =
    match (v1, v2) with
    | None, None -> 0
    | None, Some _ -> 1
    | Some _, None -> -1
    | Some v1, Some v2 -> Ident.tvar_compare v1 v2

  let equal v1 v2 =
    match (v1, v2) with
    | None, None -> true
    | None, Some _ -> false
    | Some _, None -> false
    | Some v1, Some v2 -> Ident.tvar_equal v1 v2

  let hash = Hashtbl.hash
end

module G = Persistent.Digraph.ConcreteBidirectional (V)

module Dot = Graph.Graphviz.Dot (struct
  include G

  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let name_of_false = "__false__"

  let vertex_name = function
    | None -> name_of_false
    | Some v ->
        let name = Ident.name_of_tvar v in
        assert (Stdlib.(name <> name_of_false));
        name

  let vertex_attributes _ = []
  let get_subgraph _ = None
  let default_edge_attributes _ = []
  let edge_attributes _ = []
end)

let dep_graph_of_chc =
  clauses_of
  >> Set.fold ~init:G.empty ~f:(fun g (_, ps, ns, _) ->
         match Set.to_list ps with
         | [] ->
             Set.fold ~init:g ns ~f:(fun g t ->
                 let src = Option.return @@ Term.pvar_of_atom t in
                 G.add_edge g src None)
         | [ t ] ->
             let des = Option.return @@ Term.pvar_of_atom t in
             Set.fold ~init:g ns ~f:(fun g t ->
                 let src = Option.return @@ Term.pvar_of_atom t in
                 G.add_edge g src des)
         | _ ->
             (*ToDo*)
             Set.fold ~init:g ps ~f:(fun g t ->
                 let des = Option.return @@ Term.pvar_of_atom t in
                 Set.fold ~init:g ns ~f:(fun g t ->
                     let src = Option.return @@ Term.pvar_of_atom t in
                     G.add_edge g src des)))

let output_graph = Dot.output_graph

let str_of_graph g =
  let buffer = Format.stdbuf in
  Buffer.clear buffer;
  Dot.fprint_graph Format.str_formatter g;
  Buffer.contents buffer
