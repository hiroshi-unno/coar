open Core
open Logic

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
  | NWF of nwf * (Ident.tvar * Ident.tvar)
  | Adm of bool
  (* conditioning *)
  | Integ
  | IntFun
  | RegEx

type map = (Ident.tvar, t) Map.Poly.t

let create_nwf tvar params_sorts : nwf =
  {
    name = tvar;
    param_sorts = params_sorts;
    tag_infos = Hashtbl.Poly.create ();
  }

let mk_nwf_tvar nwf = Ident.mk_nwf_tvar nwf.name

let kind_map_of_nwf nwf =
  let tags = Hashtbl.Poly.to_alist nwf.tag_infos in
  Map.Poly.of_alist_exn
  @@ List.concat_map tags ~f:(fun (tag_l, _) ->
         List.map tags ~f:(fun (tag_r, _) ->
             (mk_nwf_tvar nwf tag_l tag_r, NWF (nwf, (tag_l, tag_r)))))

let set_tag nwf tag sorts = Hashtbl.Poly.set nwf.tag_infos ~key:tag ~data:sorts
let sorts_of_tag nwf = Hashtbl.Poly.find_exn nwf.tag_infos

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
    |> Set.Poly.union_list |> Set.to_list
    |> List.map ~f:(fun (v, s) -> (v, ExtTerm.of_old_sort s))
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

let is_ord = function Ord -> true | _ -> false
let is_fn = function FN -> true | _ -> false
let is_ne = function NE -> true | _ -> false
let is_wf = function WF -> true | _ -> false
let is_nwf = function NWF _ -> true | _ -> false
let is_adm = function Adm _ -> true | _ -> false
let is_adm_with_cond = function Adm true -> true | _ -> false
let is_integ = function Integ -> true | _ -> false
let is_int_fun = function IntFun -> true | _ -> false
let is_regex = function RegEx -> true | _ -> false

let str_of = function
  | Ord -> "ordinary predicate"
  | FN -> "functional predicate"
  | NE -> "non-emptiness predicate"
  | WF -> "well-foundedness predicate"
  | NWF _ -> "well-foundedness predicate"
  | Adm true -> "admissible predicate w/ conditioning"
  | Adm false -> "admissible predicate w/o conditioning"
  | Integ -> "integrable predicate"
  | IntFun -> "integer function"
  | RegEx -> "regular expression"

let add_kinds tvs kind kind_map =
  Set.fold tvs ~init:kind_map ~f:(fun acc key ->
      if Map.Poly.mem acc key then
        let kind' = Map.Poly.find_exn acc key in
        if Stdlib.(kind' = kind) then acc
        else
          failwith
          @@ sprintf "%s is defined as %s and %s" (Ident.name_of_tvar key)
               (str_of kind) (str_of kind')
      else Map.Poly.add_exn acc ~key ~data:kind)
