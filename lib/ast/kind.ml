open Core
open Common.Ext
open Common.Combinator
open Logic

type nwf = {
  name : Ident.tvar;
  sorts_shared : Sort.t list;
  sorts_map : (Ident.tvar, Sort.t list) Hashtbl.Poly.t;
  max_pri : int; (* maximum priority *)
  sigma : (Ident.tvar, int) Map.Poly.t; (* priority function *)
  trunc : int -> int; (* truncation function *)
  acc_set : int Set.Poly.t (* accepting states I *);
}

let dummy_nwf =
  {
    name = Ident.Tvar "";
    sorts_shared = [];
    sorts_map = Hashtbl.Poly.create ();
    max_pri = 0;
    sigma = Map.Poly.empty;
    trunc = Fn.id;
    acc_set = Set.Poly.empty;
  }

type t =
  | Ord
  | FN
  | NE
  | WF
  | DWF
  | NWF of nwf * (Ident.tvar * Ident.tvar)
  | Parity of nwf * (Ident.tvar * Ident.tvar)
  | Adm of (* conditioning *) bool
  | Integ
  | IntFun
  | RealFun
  | RegEx

type map = (Ident.tvar, t) Map.Poly.t

let is_ord = function Ord -> true | _ -> false
let is_fn = function FN -> true | _ -> false
let is_ne = function NE -> true | _ -> false
let is_wf = function WF -> true | _ -> false
let is_dwf = function DWF -> true | _ -> false
let is_nwf = function NWF _ -> true | _ -> false
let is_parity = function Parity _ -> true | _ -> false
let is_adm = function Adm _ -> true | _ -> false
let is_adm_with_cond = function Adm true -> true | _ -> false
let is_integ = function Integ -> true | _ -> false
let is_int_fun = function IntFun -> true | _ -> false
let is_real_fun = function RealFun -> true | _ -> false
let is_regex = function RegEx -> true | _ -> false

let is_pred = function
  (* predicates *)
  | Ord | FN | NE | WF | DWF | NWF _ | Parity _ | Adm _ | Integ -> true
  (* functions *)
  | IntFun | RealFun | RegEx -> false

let str_of = function
  (* predicates *)
  | Ord -> "ordinary predicate"
  | FN -> "functional predicate"
  | NE -> "non-empty predicate"
  | WF -> "well-founded predicate"
  | DWF -> "disjunctively well-founded predicate"
  | NWF _ -> "global well-founded predicate"
  | Parity _ -> "parity predicate"
  | Adm true -> "admissible predicate w/ conditioning"
  | Adm false -> "admissible predicate w/o conditioning"
  | Integ -> "integrable predicate"
  (* functions *)
  | IntFun -> "integer function"
  | RealFun -> "real function"
  | RegEx -> "regular expression"

let short_str_of = function
  (* predicates *)
  | Ord -> "Ord"
  | FN -> "FN"
  | NE -> "NE"
  | WF -> "WF"
  | DWF -> "DWF"
  | NWF _ -> "NWF"
  | Parity _ -> "Prty"
  | Adm true -> "AdmC"
  | Adm false -> "Adm"
  | Integ -> "Itg"
  (* functions *)
  | IntFun -> "Int"
  | RealFun -> "Real"
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
            Sort.mk_fun (ExtTerm.of_old_sort_list sargs @ [ ExtTerm.SBool ]) ))
      ),
    Map.force_merge kind_map
      (Map.of_set_exn
      @@ Set.Poly.map pvs ~f:(fun (pv, _) -> (Ident.pvar_to_tvar pv, kind))) )

let pred_sort_env_map_of (exi_senv, kind_map) =
  Map.change_keys ~f:Ident.tvar_to_pvar
  @@ Map.Poly.filter_mapi exi_senv ~f:(fun ~key ~data ->
      if is_pred @@ kind_of kind_map key then
        Some (List.map ~f:ExtTerm.to_old_sort @@ Sort.args_of data)
      else None)

let pvars_of (exi_senv, kind_map) =
  Set.Poly.map ~f:Ident.tvar_to_pvar
  @@ Set.filter (Map.Poly.key_set exi_senv) ~f:(kind_of kind_map >> is_pred)

(* NWF related *)

let kind_map_of_nwf nwf : map =
  let sorts_map = Hashtbl.Poly.to_alist nwf.sorts_map in
  Map.Poly.of_alist_exn
  @@ List.concat_map sorts_map ~f:(fun (tag_l, _) ->
      List.map sorts_map ~f:(fun (tag_r, _) ->
          (Ident.mk_nwf_tvar nwf.name tag_l tag_r, NWF (nwf, (tag_l, tag_r)))))

let app_nwf_predicate nwf params (tag_l, params_l) (tag_r, params_r) =
  assert (List.length params = List.length nwf.sorts_shared);
  let wfp = Ident.mk_nwf_tvar nwf.name tag_l tag_r in
  assert (Hashtbl.Poly.(mem nwf.sorts_map tag_l && mem nwf.sorts_map tag_r));
  let sorts_l = Hashtbl.Poly.find_exn nwf.sorts_map tag_l in
  let sorts_r = Hashtbl.Poly.find_exn nwf.sorts_map tag_r in
  assert (
    List.length sorts_l = List.length params_l
    && List.length sorts_r = List.length params_r);
  ( wfp,
    Sort.mk_fun @@ nwf.sorts_shared @ sorts_l @ sorts_r @ [ ExtTerm.SBool ],
    ExtTerm.mk_var_app wfp @@ params @ params_l @ params_r )

(*
let app_nwf_predicate_and_add_tag nwf params (tag_l, sorts_l, params_l)
    (tag_r, sorts_r, params_r) =
  Hashtbl.Poly.set nwf.sorts_map ~key:tag_l ~data:sorts_l;
  Hashtbl.Poly.set nwf.sorts_map ~key:tag_r ~data:sorts_r;
  app_nwf_predicate nwf params (tag_l, params_l) (tag_r, params_r)

let app_nwf_predicate_and_add_tag_old nwf params (tag_l, sorts_l, params_l)
    (tag_r, sorts_r, params_r) =
  Hashtbl.Poly.set nwf.sorts_map ~key:tag_l ~data:sorts_l;
  Hashtbl.Poly.set nwf.sorts_map ~key:tag_r ~data:sorts_r;
  let params_new = List.map params ~f:ExtTerm.of_old_term in
  let params_l_new = List.map params_l ~f:ExtTerm.of_old_term in
  let params_r_new = List.map params_r ~f:ExtTerm.of_old_term in
  let wfp, psort, term =
    app_nwf_predicate nwf params_new (tag_l, params_l_new) (tag_r, params_r_new)
  in
  let uni_senv =
    Map.of_set_exn @@ of_old_sort_env_set @@ Set.Poly.union_list
    @@ List.map ~f:LogicOld.Term.sort_env_of (params @ params_l @ params_r)
  in
  ( wfp,
    ExtTerm.to_old_sort psort,
    ExtTerm.to_old_fml (Map.Poly.singleton wfp psort) uni_senv term )
*)

(* Parity related *)

let kind_map_of_parity nwf : map =
  let sorts_map = Hashtbl.Poly.to_alist nwf.sorts_map in
  Map.Poly.of_alist_exn
  @@ List.concat_map sorts_map ~f:(fun (tag_l, _) ->
      List.map sorts_map ~f:(fun (tag_r, _) ->
          ( Ident.mk_parity_tvar nwf.name
              (Ident.Tvar
                 (Ident.name_of_tvar tag_l ^ "@" ^ string_of_int
                 @@ Map.Poly.find_exn nwf.sigma tag_l))
              (Ident.Tvar
                 (Ident.name_of_tvar tag_r ^ "@" ^ string_of_int
                 @@ Map.Poly.find_exn nwf.sigma tag_r)),
            Parity (nwf, (tag_l, tag_r)) )))

let app_parity_predicate nwf (tag_l, params_l) (tag_r, params_r) =
  assert (List.is_empty nwf.sorts_shared);
  let wfp = Ident.mk_nwf_tvar nwf.name tag_l tag_r in
  assert (Hashtbl.Poly.(mem nwf.sorts_map tag_l && mem nwf.sorts_map tag_r));
  let sorts_l = Hashtbl.Poly.find_exn nwf.sorts_map tag_l in
  let sorts_r = Hashtbl.Poly.find_exn nwf.sorts_map tag_r in
  assert (
    List.length sorts_l = List.length params_l
    && List.length sorts_r = List.length params_r);
  ( wfp,
    Sort.mk_fun @@ sorts_l @ sorts_r @ [ ExtTerm.SBool ],
    ExtTerm.mk_var_app wfp @@ params_l @ params_r )
