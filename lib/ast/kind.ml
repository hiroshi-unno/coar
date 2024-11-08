open Core
open Logic
open Common.Ext
open Common.Combinator

type nwf = {
  name : Ident.tvar;
  param_sorts : Sort.t list;
  tag_infos : (Ident.tvar, Sort.t list) Hashtbl.Poly.t;
}

type t =
  | Ord
  | FN
  | NE
  | WF
  | DWF
  | NWF of nwf * (Ident.tvar * Ident.tvar)
  | Adm of (* conditioning *) bool
  | Integ
  | IntFun
  | RegEx

type map = (Ident.tvar, t) Map.Poly.t

let is_ord = function Ord -> true | _ -> false
let is_fn = function FN -> true | _ -> false
let is_ne = function NE -> true | _ -> false
let is_wf = function WF -> true | _ -> false
let is_dwf = function DWF -> true | _ -> false
let is_nwf = function NWF _ -> true | _ -> false
let is_adm = function Adm _ -> true | _ -> false
let is_adm_with_cond = function Adm true -> true | _ -> false
let is_integ = function Integ -> true | _ -> false
let is_int_fun = function IntFun -> true | _ -> false
let is_regex = function RegEx -> true | _ -> false

let is_pred = function
  (* predicates *)
  | Ord | FN | NE | WF | DWF | NWF _ | Adm _ | Integ -> true
  (* functions *)
  | IntFun | RegEx -> false

let str_of = function
  (* predicates *)
  | Ord -> "ordinary predicate"
  | FN -> "functional predicate"
  | NE -> "non-empty predicate"
  | WF -> "well-founded predicate"
  | DWF -> "disjunctively well-founded predicate"
  | NWF _ -> "well-founded predicate"
  | Adm true -> "admissible predicate w/ conditioning"
  | Adm false -> "admissible predicate w/o conditioning"
  | Integ -> "integrable predicate"
  (* functions *)
  | IntFun -> "integer function"
  | RegEx -> "regular expression"

let short_str_of = function
  (* predicates *)
  | Ord -> "Ord"
  | FN -> "FN"
  | NE -> "NE"
  | WF -> "WF"
  | DWF -> "DWF"
  | NWF _ -> "NWF"
  | Adm true -> "AdmC"
  | Adm false -> "Adm"
  | Integ -> "Itg"
  (* functions *)
  | IntFun -> "Int"
  | RegEx -> "Reg"

let kind_of (kind_map : map) tv = Map.Poly.find_exn kind_map tv

let add_kind tv kind (kind_map : map) =
  if Map.Poly.mem kind_map tv then
    let kind' = kind_of kind_map tv in
    if Stdlib.(kind' = kind) then kind_map
    else
      failwith
      @@ sprintf "%s is defined as %s and %s" (Ident.name_of_tvar tv)
           (str_of kind) (str_of kind')
  else Map.Poly.add_exn kind_map ~key:tv ~data:kind

let add_kinds senv kind (kind_map : map) =
  Set.fold ~init:kind_map senv ~f:(fun kind_map key ->
      add_kind key kind kind_map)

let add_funs (exi_senv, kind_map) kind senv =
  ( Map.force_merge exi_senv senv,
    add_kinds (Map.Poly.key_set senv) kind kind_map )

let add_pred_env_set (exi_senv, kind_map) kind pvs =
  ( Map.force_merge exi_senv
      (Map.of_set_exn
      @@ Set.Poly.map pvs ~f:(fun (pvar, sargs) ->
             ( Ident.pvar_to_tvar pvar,
               Sort.mk_fun (ExtTerm.of_old_sort_list sargs @ [ ExtTerm.SBool ])
             ))),
    Map.force_merge kind_map
      (Map.of_set_exn
      @@ Set.Poly.map pvs ~f:(fun (pv, _) -> (Ident.pvar_to_tvar pv, kind))) )

let pred_sort_env_map_of (exi_senv, kind_map) =
  Map.Poly.filter_mapi exi_senv ~f:(fun ~key ~data ->
      if is_pred @@ kind_of kind_map key then
        Some (List.map ~f:ExtTerm.to_old_sort @@ Sort.args_of data)
      else None)
  |> Map.change_keys ~f:Ident.tvar_to_pvar

let pvars_of (exi_senv, kind_map) =
  Set.Poly.map ~f:Ident.tvar_to_pvar
  @@ Set.filter (Map.Poly.key_set exi_senv) ~f:(kind_of kind_map >> is_pred)

(* NWF related *)

let create_nwf tvar params_sorts : nwf =
  {
    name = tvar;
    param_sorts = params_sorts;
    tag_infos = Hashtbl.Poly.create ();
  }

let mk_nwf_tvar nwf = Ident.mk_nwf_tvar nwf.name
let set_tag nwf tag sorts = Hashtbl.Poly.set nwf.tag_infos ~key:tag ~data:sorts
let sorts_of_tag nwf = Hashtbl.Poly.find_exn nwf.tag_infos

let kind_map_of_nwf nwf : map =
  let tags = Hashtbl.Poly.to_alist nwf.tag_infos in
  Map.Poly.of_alist_exn
  @@ List.concat_map tags ~f:(fun (tag_l, _) ->
         List.map tags ~f:(fun (tag_r, _) ->
             (mk_nwf_tvar nwf tag_l tag_r, NWF (nwf, (tag_l, tag_r)))))

let app_nwf_predicate nwf params (tag_l, params_l) (tag_r, params_r) =
  assert (List.length params = List.length nwf.param_sorts);
  let wfp = mk_nwf_tvar nwf tag_l tag_r in
  assert (
    Hashtbl.Poly.mem nwf.tag_infos tag_l && Hashtbl.Poly.mem nwf.tag_infos tag_r);
  let sorts_l = sorts_of_tag nwf tag_l in
  let sorts_r = sorts_of_tag nwf tag_r in
  assert (
    List.length sorts_l = List.length params_l
    && List.length sorts_r = List.length params_r);
  ( wfp,
    Sort.mk_fun @@ nwf.param_sorts @ sorts_l @ sorts_r @ [ ExtTerm.SBool ],
    ExtTerm.mk_var_app wfp @@ params @ params_l @ params_r )

let app_nwf_predicate_old nwf params (tag_l, params_l) (tag_r, params_r) =
  let params_new = List.map params ~f:ExtTerm.of_old_term in
  let params_l_new = List.map params_l ~f:ExtTerm.of_old_term in
  let params_r_new = List.map params_r ~f:ExtTerm.of_old_term in
  let wfp, psort, term =
    app_nwf_predicate nwf params_new (tag_l, params_l_new) (tag_r, params_r_new)
  in
  let uni_senv =
    params @ params_l @ params_r
    |> List.map ~f:LogicOld.Term.sort_env_of
    |> Set.Poly.union_list |> Set.to_list |> of_old_sort_env_list
    |> Map.Poly.of_alist_exn
  in
  ( wfp,
    ExtTerm.to_old_sort psort,
    ExtTerm.to_old_formula (Map.Poly.singleton wfp psort) uni_senv term [] )

let app_nwf_predicate_and_add_tag nwf params (tag_l, sorts_l, params_l)
    (tag_r, sorts_r, params_r) =
  set_tag nwf tag_l sorts_l;
  set_tag nwf tag_r sorts_r;
  app_nwf_predicate nwf params (tag_l, params_l) (tag_r, params_r)

let app_nwf_predicate_and_add_tag_old nwf params (tag_l, sorts_l, params_l)
    (tag_r, sorts_r, params_r) =
  set_tag nwf tag_l sorts_l;
  set_tag nwf tag_r sorts_r;
  app_nwf_predicate_old nwf params (tag_l, params_l) (tag_r, params_r)
