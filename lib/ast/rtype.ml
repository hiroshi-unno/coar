open Core
open Common
open Common.Ext
open Common.Combinator
open Ident
open LogicOld

type config = {
  depend_on_func_args: bool;
  depend_on_unit_args: bool;
  (* instantiate unbound sort variables to int *)
  instantiate_svars_to_int: bool;
  (* generate refinement predicates for function types *)
  gen_ref_pred_for_fun_types: bool;
  (* generate refinement type templates for constructors *)
  gen_type_temp_for_constrs: bool;
  (* no assertion failure *)
  never_fail: bool;
  (* only total applications can cause assertion failures *)
  can_fail_only_at_total_apps: bool;
  (* only total applications can cause temporal effects *)
  can_cause_temp_eff_only_at_total_apps: bool;
  (* enable dependent temporal control effects *)
  enable_temp_eff: bool
} [@@ deriving yojson]

(** refinement predicates x.\phi *)
type p = Ident.tvar(*x*) * Formula.t(*\phi*)
(** temporal effects \Phi *)
type e = p * p
(** control effects S *)
type s =
  | Pure
  | (* (forall x.C1) => C2 *) Eff of Ident.tvar(*x*) * c(*C1*) * c(*C2*)
(** operation signatures \Sigma *)
and o = (string, t) Util.ALMap.t
(** computation types \Sigma |> T & \Phi / S *)
and c = o(*\Sigma*) * t(*T*) * e(*\Phi*) * s(*S*)
(** value types T *)
and t =
  (** {x: (T_1, ... , T_n) T | \phi}*)
  | RGeneral of t list(*(T_1, ... , T_n)*) * Sort.t(*T*) * p(*x.\phi*)
  (** {x: T_1 * ... * T_n | \phi} *)
  | RTuple of t list(*(T_1, ... , T_n)*) * p(*x.\phi*)
  (** {x: (y:T) -> C | \phi} *)
  | RArrow of Ident.tvar(*y*) * t(*T*) * c(*C*) * p(*x.\phi*)
  (** bounded predicate polymorphism: forall ~(X:~s) s.t. ~\phi(~X). C *)
  | RForall of pred_sort_env_map(*~(X:~s)*) * Formula.t Set.Poly.t(*~\phi(~X)*) * c(*C*)
  (** type polymorphism: forall ~\alpha. C *)
  | RPoly of Ident.svar Set.Poly.t(*~\alpha*) * c(*C*)
(** refinement type environments *)
type env = (tvar, t) Map.Poly.t * Formula.t Set.Poly.t

(** Morphisms *)
let map_pred ~f (x, phi) = (x, f phi)

let rec cont_eff_map_formula ~f = function
  | Pure -> Pure
  | Eff (x, c1, c2) -> Eff (x, comp_map_formula ~f c1, comp_map_formula ~f c2)
and temp_eff_map_formula ~f (p1, p2) = (map_pred ~f p1, map_pred ~f p2)
and opsig_map_formula ~f opsig = Util.ALMap.map ~f:(val_map_formula ~f) opsig
and comp_map_formula ~f (o, t, e, s) =
  opsig_map_formula ~f o, val_map_formula ~f t,
  temp_eff_map_formula ~f e, cont_eff_map_formula ~f s
and val_map_formula ~f = function
  | RGeneral (params, sort, pred) ->
    RGeneral (List.map params ~f:(val_map_formula ~f), sort, map_pred ~f pred)
  | RTuple (ts, pred) ->
    RTuple (List.map ts ~f:(val_map_formula ~f), map_pred ~f pred)
  | RArrow (x, t, c, pred) ->
    RArrow (x, val_map_formula ~f t, comp_map_formula ~f c, map_pred ~f pred)
  | RForall (penv, constrs, c) ->
    RForall (penv, Set.Poly.map ~f constrs, comp_map_formula ~f c)
  | RPoly (svs, c) ->
    RPoly (svs, comp_map_formula ~f c)

(** Observation *)

let is_trivial (_, phi) = Formula.is_true phi(*ToDo*)
let is_pure_cont_eff = function Pure -> true | Eff _ -> false
let is_pure_temp_eff(*ToDo*) ((x1, phi1), (_, phi2)) =
  Formula.is_false phi2 &&
  Formula.is_eq phi1 && let t1, t2, _ = Formula.let_eq phi1 in
  Term.is_var t1 &&
  let (x, sort), _ = Term.let_var t1 in
  String.(Ident.name_of_tvar x = Ident.name_of_tvar x1) &&
  Stdlib.(sort = T_sequence.SFinSequence) &&
  (*Stdlib.(t2 = T_sequence.mk_eps ())*)
  Term.is_app t2 &&
  let fsym, args, _ = Term.let_app t2 in Stdlib.(fsym = T_sequence.Epsilon) &&
                                         List.is_empty args
let is_trivial_temp_eff (p1, p2) = is_trivial p1 && is_trivial p2
let is_empty_opsig = Util.ALMap.is_empty

let is_pure_comp ~config (o, _t, e, s) =
  is_empty_opsig o && (not config.enable_temp_eff || is_pure_temp_eff e) && is_pure_cont_eff s

(** Construction *)

let mk_fresh_tvar_with pre = Ident.mk_fresh_tvar ~prefix:(Some ("$" ^ pre)) ()
let mk_fresh_trivial_pred () = mk_fresh_tvar_with "v", Formula.mk_true ()
let mk_rtuple x ts phi = RTuple (ts, (x, phi))
let mk_rarrow x t c p = RArrow (x, t, c, p)
let mk_type_poly ~config svs1 = function
  | (_, t, _, _) as c when is_pure_comp ~config c ->
    (match t with
     | RPoly (svs2, c) -> RPoly (Set.Poly.union svs1 svs2, c)
     | _ -> if Set.Poly.is_empty svs1 then t else RPoly (svs1, c))
  | c -> assert (Fn.non Set.Poly.is_empty svs1); RPoly (svs1, c)
let mk_pred_poly ~config penv1 constrs1 = function
  | (_, RForall (penv2, constrs2, c), _, _) as t when is_pure_comp ~config t ->
    RForall (Map.force_merge penv1 penv2, Set.Poly.union constrs1 constrs2, c)
  | c -> RForall (penv1, constrs1, c)

let empty_opsig : o = Util.ALMap.empty
let singleton_opsig op_name op_type = Util.ALMap.singleton op_name op_type
let append_opsig curr_sig op_name op_type =
  Util.ALMap.add_exn ~key:op_name ~data:op_type curr_sig

let position_of position id = sprintf "%s[:%d]" position id
let papp_of ~config either dom v sort =
  let args, sorts =
    List.unzip @@ List.filter dom ~f:(fun (_, sort) ->
        if Sort.is_arrow sort then config.depend_on_func_args
        else if ConstDatatype.is_unit sort then config.depend_on_unit_args
        else true)
  in
  let pvar_name =
    match either with
    | First (Some name, position, id) -> sprintf "%s%s" name (position_of position id)
    | First (None, _, _) -> name_of_pvar @@ mk_fresh_pvar ()
    | Second prefix -> name_of_pvar @@ mk_fresh_pvar ~prefix:(Some prefix) ()
  in
  Formula.mk_atom @@ Atom.mk_pvar_app (Pvar pvar_name)
    (sorts @ [sort]) (args @ [Term.mk_var v sort])
let mk_temp_eff_val () =
  let x = mk_fresh_tvar_with "fin" in
  (x, Formula.eq (Term.mk_var x T_sequence.SFinSequence) @@ T_sequence.mk_eps ()),
  (mk_fresh_tvar_with "inf", Formula.mk_false ())
let mk_temp_eff_trivial () =
  (mk_fresh_tvar_with "fin", Formula.mk_true ()),
  (mk_fresh_tvar_with "inf", Formula.mk_true ())
let mk_temp_eff_fresh ~config dom =
  let x = mk_fresh_tvar_with "fin" in
  (x, papp_of ~config (Second "fin_pred") dom x T_sequence.SFinSequence),
  let y = mk_fresh_tvar_with "inf" in
  (y, papp_of ~config (Second "inf_pred") dom y T_sequence.SInfSequence)

let rec nu_of_cont x = function
  | Pure -> Formula.mk_true ()
  | Eff (_, _, c) -> nu_of_comp x c
and nu_of_comp x (_, _, ((_, _), (y, phi)), s) =
  Formula.and_of [Formula.rename (Map.Poly.singleton y x) phi; nu_of_cont x s]

let rec cont_of_cont_eff = function
  | Pure -> Sort.Pure
  | Eff (_, (o1, t1, _, s1), (o2, t2, _, s2)) ->
    Sort.Eff (sopsig_of_ropsig o1, sort_of_val t1, cont_of_cont_eff s1,
              sopsig_of_ropsig o2, sort_of_val t2, cont_of_cont_eff s2)
and full_sort_of_comp (o, t, _e, s) = sopsig_of_ropsig o, sort_of_val t, cont_of_cont_eff s
and sort_of_val = function
  | RGeneral (params, T_dt.SDT dt, _) ->
    T_dt.SDT (Datatype.update_args dt @@ List.map params ~f:sort_of_val)
  | RGeneral (_params, (T_dt.SUS (_name, _tys) as sort), _) ->
    (*ToDo: check params with tys*)
    sort
  | RGeneral (args, sort, _) ->
    assert (List.is_empty args); sort
  | RTuple (params, _) ->
    T_tuple.STuple (List.map params ~f:sort_of_val)
  | RArrow (_, t, c, _) ->
    Sort.SArrow (sort_of_val t, full_sort_of_comp c)
  | RForall (_, _, c) ->
    (match full_sort_of_comp c with
     | (o, s, Sort.Pure) when Sort.is_empty_opsig o -> s
     | _ -> failwith "sort_of_val")
  | RPoly (svs, c) ->
    Sort.mk_poly svs @@
    match full_sort_of_comp c with
    | (o, s, Sort.Pure) when Sort.is_empty_opsig o -> s
    | _ -> failwith "sort_of_val"
and sopsig_of_ropsig opsig = Sort.OpSig (Util.ALMap.map opsig ~f:sort_of_val, None)
let sort_of_comp (_o, t, _e, _s) = sort_of_val t

let rec mk_rgeneral ~config x ?(params=[]) sort phi =
  let params =
    if List.is_empty params then
      match sort with
      | T_dt.SDT dt -> List.map (Datatype.args_of dt) ~f:(mk_simple_val_rtype ~config)  
      | _ -> []
    else params
  in
  RGeneral (params, sort, (x, phi))
and mk_simple_comp_rtype ~config ~opsig ~cont sort =
  comp_type_of ~config ~temp:false ~opsig:(`Sort opsig) ~cont [] @@ mk_simple_val_rtype ~config sort
and mk_simple_val_rtype ~config = function
  | T_dt.SDT dt ->
    RGeneral (List.map (Datatype.args_of dt) ~f:(mk_simple_val_rtype ~config),
              T_dt.SDT dt,
              mk_fresh_trivial_pred ())
  | T_tuple.STuple sorts ->
    RTuple (List.map sorts ~f:(mk_simple_val_rtype ~config),
            mk_fresh_trivial_pred ())
  | Sort.SArrow (sort1, (opsig, sort2, cont)) ->
    RArrow (mk_fresh_tvar_with "x",
            mk_simple_val_rtype ~config sort1,
            mk_simple_comp_rtype ~config ~opsig ~cont sort2,
            mk_fresh_trivial_pred ())
  | Sort.SPoly (svs, sort) ->
    mk_type_poly ~config svs @@
    mk_simple_comp_rtype ~config
      ~opsig:(Sort.empty_closed_opsig) ~cont:Sort.Pure sort
  | s ->
    RGeneral ([], s, mk_fresh_trivial_pred ())
and val_type_of_sort (*~print*) ~config ?(name=None) dom =
  let rec aux ?(refine = true) name position id dom = function
    | Sort.SPoly (svs, s) ->
      mk_type_poly ~config svs @@
      comp_type_of ~config [] @@ aux ~refine(*ToDo*) name position id dom s
    | Sort.SArrow (sort1, (opsig, sort2, cont)) as sort ->
      let x = mk_fresh_tvar_with "x" in
      let t =
        let position, id =
          if Sort.is_arrow sort1 then position_of position id, 0 else position, id
        in
        aux ~refine:(Fn.non Sort.is_pure cont (*ToDo:[opsig]?*)||
                     not (config.never_fail ||
                          config.can_fail_only_at_total_apps && Sort.is_arrow sort2))
          name position id dom sort1
      in
      let c =
        let dom' = dom @ [Term.mk_var x sort1, sort1] in
        let temp = not (config.can_cause_temp_eff_only_at_total_apps && Sort.is_arrow sort2) in
        comp_type_of ~config ~temp ~opsig:(`Sort opsig) ~cont dom' @@
        aux name position (id + 1) dom' sort2
      in
      mk_rarrow x t c @@
      if refine && config.gen_ref_pred_for_fun_types then
        let v = mk_fresh_tvar_with "v" in
        let name = match name with Some name -> Some (name ^ "$fun"(*ToDo*)) | None -> None in
        v, papp_of ~config (First (name, position, id)) dom v sort
      else mk_fresh_trivial_pred ()
    | T_tuple.STuple sorts as sort ->
      let v = mk_fresh_tvar_with "v" in
      let ts = List.map sorts ~f:(aux None "" 0 dom) in
      mk_rtuple v ts @@
      if refine then papp_of ~config (First (name, position, id)) dom v sort else Formula.mk_true ()
    | T_dt.SDT dt as sort ->
      let v = mk_fresh_tvar_with "v" in
      let params = List.map (Datatype.args_of dt) ~f:(mk_simple_val_rtype ~config) in
      mk_rgeneral ~config v ~params sort @@
      if refine then papp_of ~config (First (name, position, id)) dom v sort else Formula.mk_true ()
    | T_dt.SUS (_, params) as sort ->
      let v = mk_fresh_tvar_with "v" in
      let params = List.map params ~f:(mk_simple_val_rtype ~config) in
      mk_rgeneral ~config v ~params sort @@
      if refine then papp_of ~config (First (name, position, id)) dom v sort else Formula.mk_true ()
    | sort ->
      let v = mk_fresh_tvar_with "v" in
      mk_rgeneral ~config v ~params:[] sort @@
      if refine then papp_of ~config (First (name, position, id)) dom v sort else Formula.mk_true ()
  in
  fun sort ->
    let rty = aux name "" 0 dom sort in
    (*print @@ lazy (sprintf "val_type_of_sort(%s) = %s" (Term.str_of_sort sort) (str_of_val ~config rty));*)
    rty
and comp_type_of ~config
    ?(temp = false) ?(opsig = `Refined empty_opsig) ?(cont = Sort.Pure)
    dom val_type =
  let ropsig =
    match opsig with
    | `Refined ropsig -> ropsig
    | `Sort Sort.OpSig (opmap, _r) -> Util.ALMap.map opmap ~f:(val_type_of_sort ~config dom)
    | _ -> failwith "[comp_type_of]"
  in
  let temp_eff =
    if config.enable_temp_eff then
      if temp then mk_temp_eff_fresh ~config dom else mk_temp_eff_val ()
    else mk_temp_eff_trivial ()
  in
  let cont_eff =
    match cont with
    | Sort.Pure -> Pure
    | Sort.Eff (o1, s1, cont1, o2, s2, cont2) ->
      let x = mk_fresh_tvar_with "x" in
      let c1 =
        let dom' = let sort = sort_of_val val_type in dom @ [Term.mk_var x sort, sort] in
        comp_type_of ~config ~temp ~opsig:(`Sort o1) ~cont:cont1 dom' @@ val_type_of_sort ~config dom' s1
      in
      let c2 =
        comp_type_of ~config ~temp ~opsig:(`Sort o2) ~cont:cont2 dom @@ val_type_of_sort ~config dom s2
      in
      Eff (x, c1, c2)
    | _ -> failwith @@ sprintf "[comp_type_of] %s not supported" (Term.str_of_cont cont)
  in
  ropsig, val_type, temp_eff, cont_eff

(** Destruction *)

(*** value types *)
let let_rgeneral = function RGeneral (params, s, pred) -> params, s, pred | _ -> assert false
let let_rarrow = function RArrow (x, t1, t2, pred) -> x, t1, t2, pred | _ -> assert false
let let_rtuple = function RTuple (ts, pred) -> ts, pred | _ -> assert false
let let_pred_poly = function RForall (penv, constrs, c) -> penv, constrs, c | _ -> assert false
let let_type_poly = function RPoly (svs, c) -> svs, c | _ -> assert false

(*** computation types *)
let opsig_of (o, _, _, _) = o
let val_type_of (_, t, _, _) = t
let temp_eff_of (_, _, e, _) = e
let cont_eff_of (_, _, _, s) = s

(** Observation *)
let is_rgeneral = function RGeneral _ -> true | _ -> false
let is_rarrow = function RArrow _ -> true | _ -> false
let is_rtuple = function RTuple _ -> true | _ -> false
let is_pred_poly = function RForall _ -> true | _ -> false
let is_type_poly = function RPoly _ -> true | _ -> false

let rec is_simple_comp (o, t, e, s) =
  is_empty_opsig o && is_simple_val t && is_trivial_temp_eff e && is_pure_cont_eff s
and is_simple_val = function
  | RArrow (_, t, c, pred) ->
    is_trivial pred && is_simple_val t && is_simple_comp c
  | RGeneral (ts, _, pred) | RTuple (ts, pred) ->
    is_trivial pred && List.for_all ts ~f:is_simple_val
  | RForall (_, _, _) | RPoly (_, _) -> false

let tvar_of_val = function
  | RGeneral (_, _, (x, _)) | RTuple (_, (x, _)) | RArrow (_, _, _, (x, _)) -> x
  | _ -> assert false

let rec pvs_of_cont_eff = function
  | Pure -> Set.Poly.empty
  | Eff (_, c1, c2) -> Set.Poly.union (pvs_of_comp c1) (pvs_of_comp c2)
and pvs_of_temp_eff ((_, phi1), (_, phi2)) =
  Set.Poly.union (Formula.pvs_of phi1) (Formula.pvs_of phi2)
and pvs_of_opsig (opmap: o) =
  opmap |> Util.ALMap.data |> List.map ~f:pvs_of_val |> Set.Poly.union_list
and pvs_of_comp (o, t, e, s) =
  Set.Poly.union_list [pvs_of_opsig o; pvs_of_val t; pvs_of_temp_eff e; pvs_of_cont_eff s]
and pvs_of_val = function
  | RGeneral (ts, _, (_, phi)) | RTuple (ts, (_, phi)) ->
    Set.Poly.union_list @@ Formula.pvs_of phi :: List.map ~f:pvs_of_val ts
  | RArrow (_, t, c, (_, phi)) ->
    Set.Poly.union_list [pvs_of_val t; pvs_of_comp c; Formula.pvs_of phi]
  | RForall (penv, phis, c) ->
    Set.Poly.diff
      (Set.Poly.union (Set.concat_map ~f:Formula.pvs_of phis) (pvs_of_comp c))
      (Set.Poly.of_list @@ Map.Poly.keys penv)
  | RPoly (_svs, c) -> pvs_of_comp c

let rec pred_sort_env_of_cont_eff ?(bpvs = Set.Poly.empty) = function
  | Pure -> Set.Poly.empty
  | Eff (_, c1, c2) ->
    Set.Poly.union (pred_sort_env_of_comp ~bpvs c1) (pred_sort_env_of_comp ~bpvs c2)
and pred_sort_env_of_temp_eff ?(bpvs = Set.Poly.empty) ((_, phi1), (_, phi2)) =
  Set.Poly.union (Formula.pred_sort_env_of ~bpvs phi1) (Formula.pred_sort_env_of ~bpvs phi2)
and pred_sort_env_of_opsig ?(bpvs = Set.Poly.empty) opsig =
  opsig |> Util.ALMap.data |> List.map ~f:(pred_sort_env_of_val ~bpvs) |> Set.Poly.union_list
and pred_sort_env_of_comp ?(bpvs = Set.Poly.empty) (o, t, e, s) =
  Set.Poly.union_list
    [pred_sort_env_of_opsig ~bpvs o; pred_sort_env_of_val ~bpvs t;
     pred_sort_env_of_temp_eff ~bpvs e; pred_sort_env_of_cont_eff ~bpvs s]
and pred_sort_env_of_val ?(bpvs = Set.Poly.empty) = function
  | RGeneral (params, _, (_, phi)) | RTuple (params, (_, phi)) ->
    Set.Poly.union_list @@
    Formula.pred_sort_env_of ~bpvs phi :: List.map params ~f:(pred_sort_env_of_val ~bpvs)
  | RArrow (_, t, c, (_, phi)) ->
    Set.Poly.union_list
      [pred_sort_env_of_val ~bpvs t;
       pred_sort_env_of_comp ~bpvs c;
       Formula.pred_sort_env_of ~bpvs phi]
  | RForall (penv, phis, c) ->
    let bpvs = Set.Poly.union bpvs @@ Set.Poly.of_list @@ Map.Poly.keys penv in
    Set.Poly.union
      (Set.concat_map ~f:(Formula.pred_sort_env_of ~bpvs) phis)
      (pred_sort_env_of_comp ~bpvs c)
  | RPoly (_svs, c) -> pred_sort_env_of_comp ~bpvs c

let rec args_of_comp_rtype (_, t, _, _) = args_of_val_rtype t
and args_of_val_rtype = function RArrow (x, t, c, _) -> (x, t) :: args_of_comp_rtype c | _ -> []
let rec ret_of_comp_rtype (_, t, _, _) = ret_of_val_rtype t
and ret_of_val_rtype = function RArrow (_, _, c, _) -> ret_of_comp_rtype c | t -> t
let rec args_ret_of_comp_type (_, t, _, _) = args_ret_of_val_type t
and args_ret_of_val_type = function
  | RArrow (x, t, c, _) ->
    let args, ret = args_ret_of_comp_type c in
    (x, t) :: args, ret
  | t -> [], t

(** *)

let rec tvar_map_of_temp_eff ~from ~to_ map =
  match from, to_ with
  | ((x1, _), (y1, _)), ((x2, _), (y2, _)) ->
    Map.Poly.set map ~key:x1 ~data:x2 |> Map.Poly.set ~key:y1 ~data:y2
and tvar_map_of_cont_eff ~from ~to_ map =
  match from, to_ with
  | Eff (x1, c11, c12), Eff (x2, c21, c22) ->
    Map.Poly.set map ~key:x1 ~data:x2
    |> tvar_map_of_comp ~from:c11 ~to_:c21
    |> tvar_map_of_comp ~from:c12 ~to_:c22
  | _, _ -> map
and tvar_map_of_opsig ~(from: o) ~(to_: o) map =
  let lefts, boths, rights = Util.ALMap.split_lbr from to_ in
  if List.is_empty lefts && List.is_empty rights then
    List.fold boths ~init:map ~f:(fun acc (_op, (t1, t2)) ->
        tvar_map_of_val ~from:t1 ~to_:t2 acc)
  else failwith "tvar_map_of_opsig"
and tvar_map_of_comp ~from ~to_ map =
  match from, to_ with
  | (o1, t1, e1, s1), (o2, t2, e2, s2) ->
    tvar_map_of_val ~from:t1 ~to_:t2 map
    |> tvar_map_of_opsig ~from:o1 ~to_:o2
    |> tvar_map_of_temp_eff ~from:e1 ~to_:e2
    |> tvar_map_of_cont_eff ~from:s1 ~to_:s2
and tvar_map_of_val ~from ~to_ map =
  match from, to_ with
  | RGeneral (args1, _, (tvar1, _)), RGeneral (args2, _, (tvar2, _)) ->
    let map' = Map.Poly.set map ~key:tvar1 ~data:tvar2 in
    List.fold2_exn args1 args2 ~init:map' ~f:(fun acc arg1 arg2 ->
        tvar_map_of_val ~from:arg1 ~to_:arg2 acc)
  | RTuple (ts1, (tvar1, _)), RTuple (ts2, (tvar2, _)) ->
    let map' = Map.Poly.set map ~key:tvar1 ~data:tvar2 in
    List.fold2_exn ts1 ts2 ~init:map' ~f:(fun acc arg1 arg2 ->
        tvar_map_of_val ~from:arg1 ~to_:arg2 acc)
  | RArrow (tvar1, t1, c1, (tvar1', _)), RArrow (tvar2, t2, c2, (tvar2', _)) ->
    map
    |> Map.Poly.set ~key:tvar1 ~data:tvar2
    |> Map.Poly.set ~key:tvar1' ~data:tvar2'
    |> tvar_map_of_val ~from:t1 ~to_:t2
    |> tvar_map_of_comp ~from:c1 ~to_:c2
  | RForall (_penv1, _, c1), RForall (_penv2, _, c2) ->
    (** ToDo: penv1 and penv2 may differ *)
    tvar_map_of_comp ~from:c1 ~to_:c2 map
  | RPoly (_svs1, c1), RPoly (_svs2, c2) ->
    (** ToDo: svs1 and svs2 may differ *)
    tvar_map_of_comp ~from:c1 ~to_:c2 map
  | _, _ -> map

let rec set_sort_temp_eff subst ((x1, phi1), (x2, phi2)) =
  (x1,
   Typeinf.typeinf_formula @@
   Formula.subst (Map.Poly.set subst ~key:x1 ~data:(Term.mk_var x1 T_sequence.SFinSequence)) phi1),
  (x2,
   Typeinf.typeinf_formula @@
   Formula.subst (Map.Poly.set subst ~key:x2 ~data:(Term.mk_var x2 T_sequence.SInfSequence)) phi2)
and set_sort_cont_eff subst sort = function
  | Pure -> Pure
  | Eff (x, c1, c2) ->
    Eff (x,
         set_sort_comp (Map.Poly.set subst ~key:x ~data:(Term.mk_var x sort)) c1,
         set_sort_comp subst c2)
and set_sort_opsig subst (o: o) : o = Util.ALMap.map o ~f:(set_sort_val subst)
and set_sort_comp subst (o, t, e, s) =
  set_sort_opsig subst o,
  set_sort_val subst t,
  set_sort_temp_eff subst e,
  set_sort_cont_eff subst (sort_of_val t) s
and set_sort_val subst = function
  | RGeneral (params, sort, (x, phi)) ->
    let params = List.map params ~f:(set_sort_val subst) in
    let phi =
      Typeinf.typeinf_formula @@
      Formula.subst (Map.Poly.set subst ~key:x ~data:(Term.mk_var x sort)) phi
    in
    RGeneral (params, sort, (x, phi))
  | RTuple (ts, (x, phi)) as ty ->
    let sort = sort_of_val ty in
    let ts = List.map ts ~f:(set_sort_val subst) in
    let phi =
      Typeinf.typeinf_formula @@
      Formula.subst (Map.Poly.set subst ~key:x ~data:(Term.mk_var x sort)) phi
    in
    RTuple (ts, (x, phi))
  | RArrow (y, t, c, (x, phi)) as ty ->
    let sort = sort_of_val ty in
    let t = set_sort_val subst t in
    let c =
      let subst = Map.Poly.set subst ~key:y ~data:(Term.mk_var y @@ sort_of_val t) in
      set_sort_comp subst c
    in
    let phi =
      Typeinf.typeinf_formula @@
      Formula.subst (Map.Poly.set subst ~key:x ~data:(Term.mk_var x sort)) phi
    in
    RArrow (y, t, c, (x, phi))
  | RForall (penv, phis, c) ->
    let phis =
      Set.Poly.map phis ~f:(fun phi -> Typeinf.typeinf_formula @@ Formula.subst subst phi)
    in
    RForall (penv, phis, set_sort_comp subst c)
  | RPoly (svs, c) -> RPoly (svs, set_sort_comp subst c)

(** Printer *)

let str_of_pred (x, phi) = sprintf "%s. %s" (Ident.name_of_tvar x) (Formula.str_of phi)
let rec str_of_temp_eff (pred1, pred2) =
  sprintf (*"(" ^ *)"%s, %s"(* ^ ")"*) (str_of_pred pred1) (str_of_pred pred2)
and str_of_cont_eff ~config = function
  | Pure -> "_"
  | Eff (x, c1, c2) ->
    sprintf  "(forall %s. %s) => %s"
      (Ident.name_of_tvar x) (str_of_comp ~config c1) (str_of_comp ~config c2)
and str_of_opsig ~config (opsig: o) =
  opsig
  |> Util.ALMap.to_alist
  |> String.concat_map_list ~sep:", " ~f:(fun (op, t) -> op ^ ": " ^ str_of_val ~config t)
  |> sprintf "{%s}"
and str_of_comp ~config (o, t, e, s) =
  (if is_empty_opsig o && (not config.enable_temp_eff || is_pure_temp_eff e) && is_pure_cont_eff s then "" else "(") ^
  (if is_empty_opsig o then "" else str_of_opsig ~config o ^ " |> ") ^
  str_of_val ~config t ^
  (if not config.enable_temp_eff || is_pure_temp_eff e then "" else " & " ^ str_of_temp_eff e) ^
  (if is_pure_cont_eff s then "" else " / " ^ str_of_cont_eff ~config s) ^
  (if is_empty_opsig o && (not config.enable_temp_eff || is_pure_temp_eff e) && is_pure_cont_eff s then "" else ")")
and str_of_val ~config = function
  | RGeneral (params, sort, (x, phi)) ->
    let sort_name =
      match sort with T_dt.SDT dt -> Datatype.name_of dt | _ -> Term.str_of_sort sort
    in
    if is_trivial (x, phi) then
      if List.is_empty params then sort_name
      else
        sprintf "(%s) %s"
          (*(Ident.name_of_tvar x)*)
          (String.concat_map_list ~sep:"," params ~f:(str_of_val ~config))
          sort_name
    else if List.is_empty params then
      sprintf "{%s: %s | %s}" (Ident.name_of_tvar x) sort_name (Formula.str_of phi)
    else
      sprintf "{%s: (%s) %s | %s}"
        (Ident.name_of_tvar x)
        (String.concat_map_list ~sep:"," params ~f:(str_of_val ~config))
        sort_name
        (Formula.str_of phi)
  | RTuple (ts, (x, phi)) ->
    if is_trivial (x, phi) then
      String.concat_map_list ~sep:" * " ts ~f:(str_of_val ~config)
    else
      sprintf "{%s: %s | %s}"
        (Ident.name_of_tvar x)
        (String.concat_map_list ~sep:" * " ts ~f:(str_of_val ~config))
        (Formula.str_of phi)
  | RArrow (y, t, c, (x, phi)) ->
    if is_trivial (x, phi) then
      sprintf "(%s:%s) -> %s"
        (Ident.name_of_tvar y) (str_of_val ~config t) (str_of_comp ~config c)
    else
      sprintf "{%s: (%s:%s) -> %s | %s}"
        (Ident.name_of_tvar x)
        (Ident.name_of_tvar y) (str_of_val ~config t) (str_of_comp ~config c)
        (Formula.str_of phi)
  | RForall (penv, phis, c) ->
    if Map.Poly.is_empty penv && Set.Poly.is_empty phis then
      str_of_comp ~config c
    else if Set.Poly.is_empty phis then
      sprintf "forall %s. %s"
        (String.concat_map_list ~sep:"," ~f:Ident.name_of_pvar @@ Map.Poly.keys penv)
        (str_of_comp ~config c)
    else
      sprintf "forall (%s | %s). %s"
        (String.concat_map_list ~sep:"," ~f:Ident.name_of_pvar @@ Map.Poly.keys penv)
        (String.concat_set ~sep:"; " @@ Set.Poly.map phis ~f:Formula.str_of)
        (str_of_comp ~config c)
  | RPoly (svs, c) ->
    if Set.Poly.is_empty svs then failwith "[str_of_val.RPoly]"(*str_of_comp ~config c*)
    else if Set.is_singleton svs then
      sprintf "forall %s. %s"
        (Ident.name_of_svar @@ Set.Poly.choose_exn svs)
        (str_of_comp ~config c)
    else
      sprintf "forall (%s). %s"
        (String.concat_set ~sep:"," @@ Set.Poly.map ~f:Ident.name_of_svar svs)
        (str_of_comp ~config c)

(** Substitution *)

let rec subst_temp_eff sub ((x1, phi1), (x2, phi2)) =
  (x1, Formula.subst (Map.Poly.remove sub x1) phi1),
  (x2, Formula.subst (Map.Poly.remove sub x2) phi2)
and subst_cont_eff sub = function
  | Pure -> Pure
  | Eff (x, c1, c2) ->
    Eff (x, subst_comp_type (Map.Poly.remove sub x) c1, subst_comp_type sub c2)
and subst_opsig sub (opsig: o) : o = Util.ALMap.map opsig ~f:(subst_val_type sub)
and subst_comp_type sub (o, t, e, s) =
  subst_opsig sub o, subst_val_type sub t, subst_temp_eff sub e, subst_cont_eff sub s
and subst_val_type sub = function
  | RGeneral (params, sort, (x, phi)) ->
    RGeneral (List.map params ~f:(subst_val_type sub), sort,
              (x, Formula.subst (Map.Poly.remove sub x) phi))
  | RTuple (ts, (x, phi)) ->
    RTuple (List.map ts ~f:(subst_val_type sub),
            (x, Formula.subst (Map.Poly.remove sub x) phi))
  | RArrow (y, t, c, (x, phi)) ->
    RArrow (y, subst_val_type sub t, subst_comp_type (Map.Poly.remove sub y) c,
            (x, Formula.subst (Map.Poly.remove sub x) phi))
  | RForall (penv, phis, c) ->
    RForall (penv, Set.Poly.map ~f:(Formula.subst sub) phis, subst_comp_type sub c)
  | RPoly (svs, c) ->
    RPoly (svs, subst_comp_type sub c)

let rec subst_preds_temp_eff sub ((x1, phi1), (x2, phi2)) =
  (x1, Formula.subst_preds sub phi1), (x2, Formula.subst_preds sub phi2)
and subst_preds_cont_eff sub = function
  | Pure -> Pure
  | Eff (x, c1, c2) -> Eff (x, subst_preds_comp_type sub c1, subst_preds_comp_type sub c2)
and subst_preds_opsig sub (opsig: o) : o = Util.ALMap.map opsig ~f:(subst_preds_val_type sub)
and subst_preds_comp_type sub (o, t, e, s) =
  subst_preds_opsig sub o, subst_preds_val_type sub t,
  subst_preds_temp_eff sub e, subst_preds_cont_eff sub s
and subst_preds_val_type sub = function
  | RGeneral (params, sort, (x, phi)) ->
    RGeneral (List.map params ~f:(subst_preds_val_type sub), sort,
              (x, Formula.subst_preds sub phi))
  | RTuple (ts, (x, phi)) ->
    RTuple (List.map ts ~f:(subst_preds_val_type sub), (x, Formula.subst_preds sub phi))
  | RArrow (y, t, c, (x, phi)) ->
    RArrow (y, subst_preds_val_type sub t, subst_preds_comp_type sub c,
            (x, Formula.subst_preds sub phi))
  | RForall (penv, phis, c) ->
    let sub' = Map.remove_keys sub @@ Map.Poly.keys penv in
    RForall (penv, Set.Poly.map ~f:(Formula.subst_preds sub) phis, subst_preds_comp_type sub' c)
  | RPoly (svs, c) ->
    RPoly (svs, subst_preds_comp_type sub c)

let rec subst_sorts_temp_eff map ((x1, phi1), (x2, phi2)) =
  (x1, Formula.subst_sorts map phi1), (x2, Formula.subst_sorts map phi2)
and subst_sorts_cont_eff ~config map = function
  | Pure -> Pure
  | Eff (x, c1, c2) ->
    Eff (x, subst_sorts_comp_type ~config map c1, subst_sorts_comp_type ~config map c2)
and subst_sorts_opsig ~config sub (opsig: o) : o =
  Util.ALMap.map opsig ~f:(subst_sorts_val_type ~config sub)
and subst_sorts_comp_type ~config map (o, t, e, s) =
  subst_sorts_opsig ~config map o, subst_sorts_val_type ~config map t,
  subst_sorts_temp_eff map e, subst_sorts_cont_eff ~config map s
and subst_sorts_val_type ~config sub = function
  | RGeneral ([], sort, (x, phi)) ->
    let sort = Term.subst_sorts_sort sub sort in
    let phi = Formula.subst_sorts sub phi in
    (match sort with
     | T_dt.SDT dt ->
       let params = List.map ~f:(mk_simple_val_rtype(*ToDo*) ~config) @@ Datatype.args_of dt in
       RGeneral (params, sort, (x, phi))
     | T_tuple.STuple sorts ->
       let ts = List.map sorts ~f:(mk_simple_val_rtype(*ToDo*) ~config) in
       RTuple (ts, (x, phi))
     | Sort.SArrow (sort1, (opsig2, sort2, cont2)) ->
       RArrow (mk_fresh_tvar (),
               mk_simple_val_rtype(*ToDo*) ~config sort1,
               mk_simple_comp_rtype(*ToDo*) ~config ~opsig:opsig2 ~cont:cont2 sort2,
               (x, phi))
     | Sort.SPoly (_svs, _sort) ->
       failwith "instantiation with a type polymorphic type is not supported"
     | _ -> RGeneral ([], sort, (x, phi)))
  | RGeneral (params, T_dt.SDT dt, (x, phi)) ->
    let params = List.map params ~f:(subst_sorts_val_type ~config sub) in
    let dt = Datatype.subst_sorts sub dt in
    let phi = Formula.subst_sorts sub phi in
    RGeneral (params, T_dt.SDT dt, (x, phi))
  | RTuple (ts, (x, phi)) ->
    let ts = List.map ts ~f:(subst_sorts_val_type ~config sub) in
    let phi = Formula.subst_sorts sub phi in
    RTuple (ts, (x, phi))
  | RArrow (y, t, c, (x, phi)) ->
    let t = subst_sorts_val_type ~config sub t in
    let c = subst_sorts_comp_type ~config sub c in
    let phi = Formula.subst_sorts sub phi in
    RArrow (y, t, c, (x, phi))
  | RForall (penv, phis, c) ->
    let penv = Map.Poly.map ~f:(List.map ~f:(Term.subst_sorts_sort sub)) penv in
    let phis = Set.Poly.map ~f:(Formula.subst_sorts sub) phis in
    let c = subst_sorts_comp_type ~config sub c in
    RForall (penv, phis, c)
  | RPoly (svs, c) ->
    let sub = Map.remove_keys sub @@ Set.Poly.to_list svs in
    let c = subst_sorts_comp_type ~config sub c in
    RPoly (svs, c)
  | _ -> failwith "subst_sorts_val_type"

let rename_var map from = match Map.Poly.find map from with Some v -> v | None -> from
let rec rename_temp_eff map ((x1, phi1), (x2, phi2)) =
  (x1, Formula.rename (Map.Poly.remove map x1) phi1),
  (x2, Formula.rename (Map.Poly.remove map x2) phi2)
and rename_cont_eff map = function
  | Pure -> Pure
  | Eff (x, c1, c2) ->
    Eff (x, rename_comp_type (Map.Poly.remove map x) c1, rename_comp_type map c2)
and rename_opsig map (opsig: o) : o = Util.ALMap.map opsig ~f:(rename_val_type map)
and rename_comp_type map (o, t, e, s) =
  rename_opsig map o, rename_val_type map t, rename_temp_eff map e, rename_cont_eff map s
and rename_val_type map = function
  | RGeneral (params, sort, (x, phi)) ->
    RGeneral (List.map params ~f:(rename_val_type map), sort,
              (x, Formula.rename (Map.Poly.remove map x) phi))
  | RTuple (ts, (x, phi)) ->
    RTuple (List.map ts ~f:(rename_val_type map),
            (x, Formula.rename (Map.Poly.remove map x) phi))
  | RArrow (y, t, c, (x, phi)) ->
    RArrow (y, rename_val_type map t, rename_comp_type (Map.Poly.remove map y) c,
            (x, Formula.rename (Map.Poly.remove map x) phi))
  | RForall (penv, phis, c) ->
    RForall (penv, Set.Poly.map ~f:(Formula.rename map) phis, rename_comp_type map c)
  | RPoly (svs, c) ->
    RPoly (svs, rename_comp_type map c)

let rec rename_pvars_temp_eff map ((x1, phi1), (x2, phi2)) =
  (x1, Formula.rename_pvars map phi1), (x2, Formula.rename_pvars map phi2)
and rename_pvars_cont_eff map = function
  | Pure -> Pure
  | Eff (x, c1, c2) ->
    Eff (x, rename_pvars_comp_type map c1, rename_pvars_comp_type map c2)
and rename_pvars_opsig map (opsig: o) : o = Util.ALMap.map opsig ~f:(rename_pvars_val_type map)
and rename_pvars_comp_type map (o, t, e, s) =
  rename_pvars_opsig map o, rename_pvars_val_type map t,
  rename_pvars_temp_eff map e, rename_pvars_cont_eff map s
and rename_pvars_val_type map = function
  | RGeneral (params, sort, (x, phi)) ->
    RGeneral (List.map params ~f:(rename_pvars_val_type map), sort,
              (x, Formula.rename_pvars map phi))
  | RTuple (ts, (x, phi)) ->
    RTuple (List.map ts ~f:(rename_pvars_val_type map), (x, Formula.rename_pvars map phi))
  | RArrow (y, t, c, (x, phi)) ->
    RArrow (y, rename_pvars_val_type map t, rename_pvars_comp_type map c,
            (x, Formula.rename_pvars map phi))
  | RForall (penv, phis, c) ->
    let map = Map.remove_keys map (Map.Poly.keys penv) in
    RForall (penv, Set.Poly.map ~f:(Formula.rename_pvars map) phis,
             rename_pvars_comp_type map c)
  | RPoly (svs, c) -> RPoly (svs, rename_pvars_comp_type map c)

let rec aconv_temp_eff map (pred1, pred2) =
  aconv_pred ~prefix:"x" map pred1 T_sequence.SFinSequence,
  aconv_pred ~prefix:"y" map pred2 T_sequence.SInfSequence
and aconv_cont_eff map sort = function
  | Pure -> Pure
  | Eff (x, c1, c2) ->
    let x' = mk_fresh_tvar_with "x" in
    Eff (x',
         aconv_comp_type (Map.Poly.set map ~key:x ~data:(Term.mk_var x' sort)) c1,
         aconv_comp_type map c2)
and aconv_opsig map (opsig: o) : o = Util.ALMap.map opsig ~f:(aconv_val_type map)
and aconv_comp_type map (o, t, e, s) =
  aconv_opsig map o, aconv_val_type map t,
  aconv_temp_eff map e, aconv_cont_eff map (sort_of_val t) s
and aconv_pred ?(prefix = "v") map (x, phi) sort =
  let v = mk_fresh_tvar_with prefix in
  (v, Formula.subst (Map.Poly.set map ~key:x ~data:(Term.mk_var v sort)) phi)
and aconv_val_type map = function
  | RGeneral (params, sort, pred) ->
    RGeneral (List.map params ~f:(aconv_val_type map), sort, aconv_pred map pred sort)
  | RTuple (ts, pred) as ty ->
    RTuple (List.map ts ~f:(aconv_val_type map), aconv_pred map pred @@ sort_of_val ty)
  | RArrow (x, t, c, pred) as ty ->
    let sort = sort_of_val ty in
    let x' = mk_fresh_tvar_with "x" in
    RArrow (x',
            aconv_val_type map t,
            aconv_comp_type (Map.Poly.set map ~key:x ~data:(Term.mk_var x' @@ sort_of_val t)) c,
            aconv_pred map pred sort)
  | RForall (penv, phis, c) ->
    RForall (penv, Set.Poly.map ~f:(Formula.subst map) phis, aconv_comp_type map c)
  | RPoly (svs, c) ->
    RPoly (svs, aconv_comp_type map c)

let rec tsub_of_cont ~config sub (s, cont) =
  match s, cont with
  | Pure, Sort.Pure -> sub
  | Eff (_, c1, c2), Sort.Eff (o1, s1, cont1, o2, s2, cont2) ->
    let sub' = tsub_of_comp ~config sub (c1, o1, s1, cont1) in
    tsub_of_comp ~config sub' (c2, o2, s2, cont2)
  | _ -> failwith @@
    sprintf "[tsub_of_cont] %s and %s" (str_of_cont_eff ~config s) (Term.str_of_cont cont)
and tsub_of_opsig ~config sub = function
  | opsig, Sort.OpSig (opmap, _) ->
    let lefts, boths, _rights = Util.ALMap.split_lbr opsig opmap in
    if List.is_empty lefts (* && List.is_empty rights *) then
      List.fold boths ~init:sub ~f:(fun acc (_op, (t, sort)) ->
          tsub_of_val ~config acc (t, sort))
    else failwith "tsub_of_opsig"
  | _ -> failwith "tsub_of_opsig"
and tsub_of_comp ~config sub ((o, t, _e(*ToDo*), s), opsig, sort, cont) =
  let sub' = tsub_of_val ~config sub (t, sort) in
  let sub'' = tsub_of_opsig ~config sub' (o, opsig) in
  tsub_of_cont ~config sub'' (s, cont)
and tsub_of_val ~config sub = function
  | RGeneral ([], sort, _), sort' ->
    let omap, smap, emap = Term.pat_match_sort sort sort' in
    assert (Map.Poly.is_empty emap && Map.Poly.is_empty omap);
    Map.force_merge sub smap ~catch_dup:(fun (svar, s1, s2) ->
        failwith @@ sprintf "duplicate definition of %s as %s and %s"
          (Ident.name_of_svar svar) (Term.str_of_sort s1) (Term.str_of_sort s2))
  | RGeneral (params, T_dt.SDT dt, _), T_dt.SDT dt'
    when String.(Datatype.name_of dt = Datatype.name_of dt') ->
    let sorts = Datatype.args_of dt' in
    (try List.fold2_exn params sorts ~init:sub ~f:(fun sub -> curry2 (tsub_of_val ~config sub))
     with _ ->
       failwith @@ sprintf "[tsub_of_val] (%s) and (%s)"
         (String.concat_map_list ~sep:"," ~f:(str_of_val ~config) params)
         (String.concat_map_list ~sep:"," ~f:Term.str_of_sort sorts))
  | RGeneral (params, T_dt.SUS (name, _), _), T_dt.SDT dt'
    when String.(name = Datatype.name_of dt') ->
    let sorts = Datatype.args_of dt' in
    (try List.fold2_exn params sorts ~init:sub ~f:(fun sub -> curry2 (tsub_of_val ~config sub))
     with _ ->
       failwith @@ sprintf "[tsub_of_val] (%s) and (%s)"
         (String.concat_map_list ~sep:"," ~f:(str_of_val ~config) params)
         (String.concat_map_list ~sep:"," ~f:Term.str_of_sort sorts))
  | RTuple (ts, _), T_tuple.STuple sorts ->
    List.fold2_exn ts sorts ~init:sub ~f:(fun sub -> curry2 (tsub_of_val ~config sub))
  | RArrow ((*assume fresh*)_, t, c, _), Sort.SArrow (sort1, (opsig, sort2, cont)) ->
    tsub_of_comp ~config (tsub_of_val ~config sub (t, sort1)) (c, opsig, sort2, cont)
  | RForall (_penv, _phis, c), sort' ->
    tsub_of_comp ~config sub (c, Sort.mk_fresh_empty_open_opsig (), sort', Sort.Pure)
  | RPoly (svs1, c), Sort.SPoly (svs2, sort)
    when Fn.non Set.Poly.is_empty @@ Set.Poly.inter svs1 svs2 ->
    tsub_of_val ~config sub
      (mk_type_poly ~config (Set.Poly.diff svs1 svs2) c,
       Sort.mk_poly (Set.Poly.diff svs2 svs1) sort)
  | RPoly (svs, c), sort' ->
    Map.remove_keys
      (tsub_of_comp ~config sub (c, Sort.mk_fresh_empty_open_opsig (), sort', Sort.Pure)) @@
    Set.Poly.to_list svs
  | ty, sort ->
    failwith @@ sprintf "cannot instantiate %s with %s"
      (str_of_val ty ~config) (Term.str_of_sort sort)

let eq_dt sort1 sort2 =
  match sort1, sort2 with
  | T_dt.SDT dt1, T_dt.SDT dt2 ->
    String.(dt1.name = dt2.name) && Stdlib.(Datatype.args_of dt1 = Datatype.args_of dt2)
  | T_dt.SDT dt1, T_dt.SUS (name2, sorts2) ->
    String.(dt1.name = name2) && Stdlib.(Datatype.args_of dt1 = sorts2)
  | T_dt.SUS (name1, sorts1), T_dt.SDT dt2 ->
    String.(name1 = dt2.name) && Stdlib.(sorts1 = Datatype.args_of dt2)
  | T_dt.SUS (n1, sorts1), T_dt.SUS (n2, sorts2) ->
    String.(n1 = n2) && Stdlib.(sorts1 = sorts2)
  | _ -> false

let rec instantiate_comp ~print ~config sub (o, t, e, s) sort =
  let t, constrs = instantiate_val ~print ~config sub t sort in
  (subst_sorts_opsig ~config sub o, t,
   subst_sorts_temp_eff sub e, subst_sorts_cont_eff ~config sub s), constrs
and instantiate_val ~print ~config sub ty0 sort0 =
  let subst_sorts_pred sub (x, phi) = x, Formula.subst_sorts sub phi in
  match ty0, sort0 with
  | RGeneral ([], sort, pred), sort' ->
    let sort = Term.subst_sorts_sort sub sort in
    let pred = subst_sorts_pred sub pred in
    if Stdlib.(sort <> sort') && not (eq_dt sort sort') then
      failwith @@ sprintf "[instantiate_val] %s and %s does not match"
        (Term.str_of_sort sort) (Term.str_of_sort sort');
    (match sort with
     | T_dt.SDT dt ->
       (*print_endline @@ Datatype.str_of dt ^ " => " ^ Datatype.str_of dt';*)
       let sorts = Datatype.args_of dt in
       let params = List.map ~f:(mk_simple_val_rtype(*ToDo*) ~config) sorts in
       RGeneral (params, sort, pred), Set.Poly.empty
     | T_tuple.STuple sorts ->
       let ts = List.map sorts ~f:(mk_simple_val_rtype(*ToDo*) ~config) in
       RTuple (ts, pred), Set.Poly.empty
     | Sort.SArrow (sort1, (opsig2, sort2, cont2)) ->
       RArrow (mk_fresh_tvar (),
               mk_simple_val_rtype(*ToDo*) ~config sort1,
               mk_simple_comp_rtype(*ToDo*) ~config ~opsig:opsig2 ~cont:cont2 sort2,
               pred), Set.Poly.empty
     | Sort.SPoly (_svs, _sort) ->
       failwith "instantiation with a type polymorphic type is not supported"
     | _ -> RGeneral ([], sort, pred), Set.Poly.empty)
  | RGeneral (params, T_dt.SDT dt, pred), T_dt.SDT dt' when String.(dt.name = dt'.name) ->
    let dt = Datatype.subst_sorts sub dt in
    let pred = subst_sorts_pred sub pred in
    (*print_endline @@ Datatype.str_of dt ^ " and " ^ Datatype.str_of dt';*)
    let params, constrss =
      List.unzip @@ List.map2_exn params (Datatype.args_of dt')
        ~f:(instantiate_val ~print ~config sub)
    in
    RGeneral (params, T_dt.SDT dt, pred), Set.Poly.union_list constrss
  | RGeneral (params, T_dt.SUS (name, _), pred), T_dt.SDT dt' when String.(name = dt'.name) ->
    let pred = subst_sorts_pred sub pred in
    let params, constrss =
      List.unzip @@ List.map2_exn params (Datatype.args_of dt')
        ~f:(instantiate_val ~print ~config sub)
    in
    RGeneral (params, T_dt.SDT dt', pred), Set.Poly.union_list constrss
  | RTuple (ts, pred), T_tuple.STuple sorts ->
    let pred = subst_sorts_pred sub pred in
    let ts, constrss =
      List.unzip @@ List.map2_exn ts sorts ~f:(instantiate_val ~print ~config sub)
    in
    RTuple (ts, pred), Set.Poly.union_list constrss
  | RArrow (x, t, c, pred), Sort.SArrow (sort1, (_opsig, sort2, _cont)) ->
    (*assume [cont] matches with c*)
    let pred = subst_sorts_pred sub pred in
    let t, constrs1 = instantiate_val ~print ~config sub t sort1 in
    let c, constrs2 = instantiate_comp ~print ~config sub c sort2 in
    RArrow (x, t, c, pred), Set.Poly.union constrs1 constrs2
  | RForall (penv, constrs, c), sort ->
    if is_empty_opsig (opsig_of c) &&
       (not config.enable_temp_eff || is_pure_temp_eff (temp_eff_of c)) &&
       is_pure_cont_eff (cont_eff_of c) then begin
      print @@ lazy
        (sprintf "instantiate %s with %s" (str_of_val ~config ty0) (Term.str_of_sort sort));
      let penv = Map.Poly.map penv ~f:(List.map ~f:(Term.subst_sorts_sort sub)) in
      let constrs = Set.Poly.map constrs ~f:(Formula.subst_sorts sub) in
      let t, constrs' = instantiate_val ~print ~config sub (val_type_of c) sort in
      let pmap =
        Map.Poly.mapi penv ~f:(fun ~key ~data ->
            ignore data;
            Ident.mk_fresh_pvar ()
              ~prefix:(Some (Ident.name_of_pvar key
                             (*^ "[" ^ Term.str_of_sort(* ToDo *) sort ^ "]"*) ^ "@")))
      in
      let constrs'' =
        Set.Poly.map ~f:(Formula.rename_pvars pmap) @@ Set.Poly.union constrs constrs'
      in
      let t' = rename_pvars_val_type pmap t in
      print @@ lazy
        (sprintf "instantiated type: %s\nconstraints: %s"
           (str_of_val ~config t')
           (Formula.str_of @@ Formula.and_of @@ Set.Poly.to_list constrs''));
      t', constrs''
    end else failwith "not supported"
  | RPoly (svs1, c), Sort.SPoly (svs2, sort)
    when Fn.non Set.Poly.is_empty @@ Set.Poly.inter svs1 svs2 ->
    instantiate_val ~print ~config sub
      (mk_type_poly ~config (Set.Poly.diff svs1 svs2) c)
      (Sort.mk_poly (Set.Poly.diff svs2 svs1) sort)
  | RPoly (_svs, c), _ ->
    if is_empty_opsig (opsig_of c) &&
       (not config.enable_temp_eff || is_pure_temp_eff (temp_eff_of c)) &&
       is_pure_cont_eff (cont_eff_of c) then begin
      print @@ lazy
        (sprintf "instantiate %s with %s" (str_of_val ~config ty0) (Term.str_of_sort sort0));
      let t, constrs =
        let t = val_type_of c in
        let sub = tsub_of_val ~config sub (t, sort0) in
        (*print_endline @@ str_of_sort_subst Term.str_of_sort sub;*)
        instantiate_val ~print ~config sub t sort0
      in
      print @@ lazy
        (sprintf "instantiated type: %s\nconstraints: %s"
           (str_of_val ~config t)
           (Formula.str_of @@ Formula.and_of @@ Set.Poly.to_list constrs));
      t, constrs
    end else failwith "not supported"
  | _, _ ->
    failwith @@ sprintf "cannot instantiate %s with %s"
      (str_of_val ty0 ~config) (Term.str_of_sort sort0)

(** Refinement type environments *)
module Env = struct
  type t = env
  let mk_empty (): t = Map.Poly.empty, Set.Poly.empty
  let to_sort_env (senv, _phis) = Map.Poly.map senv ~f:sort_of_val
  let of_list l = Map.of_list_exn l, Set.Poly.empty
  let add_phi (senv, phis) phi: t = senv, Set.Poly.add phis phi
  let add_phis (senv, phis1) phis2: t = senv, Set.Poly.union phis1 phis2
  let set_ty (senv, phis) tvar ty: t = Map.Poly.set senv ~key:tvar ~data:ty, phis
  let remove (senv, phis) tvar = Map.Poly.remove senv tvar, phis
  let look_up (senv, _) tvar = Map.Poly.find senv tvar
  let look_up_exn (senv, _) tvar = Map.Poly.find_exn senv tvar
  let disj_union (senv1, phis1) (senv2, phis2) : t =
    try Map.force_merge senv1 senv2, Set.Poly.union phis1 phis2
    with _ -> failwith @@
      "duplicate definition: " ^
      String.concat_set ~sep:"," @@ Set.Poly.map ~f:Ident.name_of_tvar @@
      Set.Poly.inter
        (Set.Poly.of_list @@ Map.Poly.keys senv1)
        (Set.Poly.of_list @@ Map.Poly.keys senv2)
  let disj_union_list = List.fold ~init:(mk_empty ()) ~f:disj_union
  let set_with (senv1, phis1) (senv2, phis2) =
    Map.force_merge (Map.Poly.filter_keys senv1 ~f:(Fn.non @@ Map.Poly.mem senv2)) senv2,
    Set.Poly.union phis1 phis2
  let update_with (senv1, phis1) (senv2, phis2) =
    let shared =
      Set.Poly.inter
        (Set.Poly.of_list @@ Map.Poly.keys senv1)
        (Set.Poly.of_list @@ Map.Poly.keys senv2)
    in
    (* variables in senv1 that are masked by senv2 are renamed *)
    let map = Map.of_set_exn @@ Set.Poly.map shared ~f:(fun x -> x, Ident.mk_fresh_tvar ()) in
    let senv1 =
      Map.Poly.map (Map.rename_keys senv1 ~f:(Map.Poly.find map)) ~f:(rename_val_type map)
    in
    let phis1 = Set.Poly.map ~f:(Formula.rename map) phis1 in
    let senv2 = Map.Poly.map senv2 ~f:(rename_val_type map)(*ToDo: check correctness*) in
    let phis2 = Set.Poly.map ~f:(Formula.rename map) phis2(*ToDo: check correctness*) in
    (Map.force_merge senv1 senv2, Set.Poly.union phis1 phis2), map
  let singleton_ty tvar ty = Map.Poly.singleton tvar ty, Set.Poly.empty
  let singleton_phi phi = Map.Poly.empty, Set.Poly.singleton phi
  let dep_args_of (senv, _) =
    List.filter_map (Map.Poly.to_alist senv) ~f:(fun (var, ty) ->
        if is_rarrow ty || is_pred_poly ty || is_type_poly ty then None
        else Some (Term.mk_var var @@ sort_of_val ty, sort_of_val ty))
  let str_of ~config (senv, phis) =
    String.concat ~sep:"\n" @@
    (List.map ~f:(fun (tvar, ty) ->
         sprintf "%s : %s" (name_of_tvar tvar) (str_of_val ~config ty)) @@
     Map.Poly.to_alist senv) @
    List.map ~f:Formula.str_of @@ Set.Poly.to_list phis

  let svs_of (senv, phis) =
    Set.Poly.union (Set.concat_map phis ~f:Formula.svs_of)
      (Set.Poly.union_list @@ Map.Poly.data @@
       Map.Poly.map senv ~f:(fun t -> Term.svs_of_sort @@ sort_of_val t))

  let pure_formula_of (_, phis) = phis |> Set.Poly.to_list |> Formula.and_of

  let pred_sort_env_of ?(bpvs = Set.Poly.empty) (renv, phis) =
    let pred_senv =
      Map.Poly.fold renv ~init:Set.Poly.empty ~f:(fun ~key:_ ~data acc ->
          Set.Poly.union acc @@ pred_sort_env_of_val ~bpvs data)
    in
    let pred_senv =
      Set.Poly.fold phis ~init:pred_senv
        ~f:(fun acc phi -> Set.Poly.union acc @@ Formula.pred_sort_env_of ~bpvs phi)
    in
    try Map.of_set_exn pred_senv with _ ->
      failwith @@ String.concat_set ~sep:"\n" @@
      Set.Poly.map pred_senv ~f:(fun (pvar, sorts) ->
          Ident.name_of_pvar pvar ^ ": (" ^
          (String.concat_map_list ~sep:"," sorts ~f:Term.str_of_sort) ^ ")")
end

let rec val_rtype_of_term ~config ?(top = true) term = function
  | RGeneral (params, sort, (v, phi)) ->
    mk_rgeneral ~config v ~params sort @@
    Formula.and_of
      [Formula.eq (Term.mk_var v sort) term; if top then Formula.mk_true () else phi]
  | RTuple (ts, (v, phi)) ->
    let sorts = List.map ts ~f:sort_of_val in
    let ts =
      List.mapi ts ~f:(fun i ->
          val_rtype_of_term ~config ~top:false (T_tuple.mk_tuple_sel sorts term i))
    in
    let sort = (T_tuple.STuple sorts) in
    mk_rtuple v ts @@
    Formula.and_of
      [Formula.eq (Term.mk_var v sort) term; if top then Formula.mk_true () else phi]
  | RArrow (x, t, c, pred) -> mk_rarrow x t c pred
  | RForall (_penv, _constrs, _c) -> failwith "predicate polymorphism not supported"
  | RPoly (_svs, _c) -> failwith "type polymorphism not supported"
let comp_rtype_of_term ~config term t =
  comp_type_of ~config [] @@ val_rtype_of_term ~config term t

let of_fsym ~print ~config fsym sort =
  let args_sorts, ret_sort = Sort.args_ret_of sort in
  let rec inner ts sorts =
    let v = mk_fresh_tvar_with "v" in
    let x = mk_fresh_tvar_with "x" in
    match sorts with
    | [] ->
      mk_rgeneral ~config v ret_sort @@
      Formula.eq (Term.mk_var v ret_sort) (Term.mk_fsym_app fsym @@ List.rev ts)
    | s :: tl ->
      mk_rarrow x (mk_simple_val_rtype ~config s)
        (comp_type_of ~config [] @@ inner (Term.mk_var x s :: ts) tl) @@
      mk_fresh_trivial_pred ()
  in
  inner [] args_sorts
  |> (fun t ->
      print @@ lazy
        (sprintf "[Rtype.of_fsym] %s : %s" (Term.str_of_funsym fsym) (str_of_val ~config t));
      t)
let of_psym ~print ~config psym sort =
  let args_sorts, ret_sort = Sort.args_ret_of sort in
  assert (Term.is_bool_sort ret_sort);
  let rec inner ts sorts =
    match sorts with
    | [] ->
      let v = Ident.mk_fresh_tvar () in
      mk_rgeneral ~config v ret_sort @@
      Formula.eq
        (Term.mk_var v T_bool.SBool)
        (T_bool.of_atom @@ Atom.mk_psym_app psym @@ List.rev ts)
    | s :: tl ->
      let x = mk_fresh_tvar_with "x" in
      mk_rarrow x (mk_simple_val_rtype ~config s)
        (comp_type_of ~config [] @@ inner (Term.mk_var x s :: ts) tl) @@
      mk_fresh_trivial_pred ()
  in
  let res = inner [] args_sorts in
  print @@ lazy
    (sprintf "[Rtype.of_psym] %s : %s" (Predicate.str_of_predsym psym) (str_of_val ~config res));
  res
let of_unop ~config = function
  | Formula.Not ->
    let x = mk_fresh_tvar_with "x" in
    let r = mk_fresh_tvar_with "r" in
    mk_rarrow x (mk_rgeneral ~config (mk_fresh_tvar_with "v") T_bool.SBool @@ Formula.mk_true ())
      (comp_type_of ~config [] @@ mk_rgeneral ~config r T_bool.SBool @@
       Formula.neq (Term.mk_var r T_bool.SBool) (Term.mk_var x T_bool.SBool)) @@
    mk_fresh_trivial_pred ()
let of_binop ~config = function
  | Formula.And ->
    let rec inner ts sorts =
      let v = Ident.mk_fresh_tvar () in
      let x = mk_fresh_tvar_with "x" in
      match sorts with
      | [] ->
        mk_rgeneral ~config v T_bool.SBool @@
        Formula.eq (Term.mk_var v T_bool.SBool) @@
        T_bool.of_formula @@ Formula.and_of @@ List.map ts ~f:Formula.of_bool_term
      | s :: tl ->
        mk_rarrow x (mk_rgeneral ~config v s @@ Formula.mk_true ())
          (comp_type_of ~config [] @@ inner (Term.mk_var x s :: ts) tl) @@
        mk_fresh_trivial_pred ()
    in
    inner [] [T_bool.SBool; T_bool.SBool]
  | Formula.Or ->
    let rec inner ts sorts =
      let v = Ident.mk_fresh_tvar () in
      let x = mk_fresh_tvar_with "x" in
      match sorts with
      | [] ->
        mk_rgeneral ~config v T_bool.SBool @@
        Formula.eq (Term.mk_var v T_bool.SBool) @@
        T_bool.of_formula @@ Formula.or_of @@ List.map ts ~f:Formula.of_bool_term
      | s :: tl ->
        mk_rarrow x (mk_rgeneral ~config v s @@ Formula.mk_true ())
          (comp_type_of ~config [] @@ inner (Term.mk_var x s :: ts) tl) @@
        mk_fresh_trivial_pred ()
    in
    inner [] [T_bool.SBool; T_bool.SBool]
  | Imply | Iff | Xor -> failwith "unsupported bop"

let is_fsym = function
  | "Stdlib.+" | "Stdlib.-" | "Stdlib.*" | "Stdlib./"
  | "Stdlib.+." | "Stdlib.-." | "Stdlib.*." | "Stdlib./."
  | "Stdlib.~-" -> true
  | _ -> false
let is_psym = function
  | "Stdlib.>" | "Stdlib.<" | "Stdlib.>=" | "Stdlib.<="
  | "Stdlib.=" | "Stdlib.==" | "Stdlib.<>" | "Stdlib.!=" -> true
  | _ -> false
let is_unop = function "Stdlib.not" -> true | _ -> false
let is_binop = function
  | "Stdlib.&&" | "Stdlib.&" | "Stdlib.||" | "Stdlib.or" -> true
  | _ -> false
let fsym_of_str = function
  | "Stdlib.+" -> T_int.Add
  | "Stdlib.-" -> T_int.Sub
  | "Stdlib.*" -> T_int.Mult
  | "Stdlib./" -> T_int.Div
  | "Stdlib.+." -> T_real.RAdd
  | "Stdlib.-." -> T_real.RSub
  | "Stdlib.*." -> T_real.RMult
  | "Stdlib./." -> T_real.RDiv
  | "Stdlib.~-" -> T_int.Neg
  | s -> failwith @@ "unknown fsym: " ^ s
let psym_of_str sort = function
  | "Stdlib.>" -> (match sort with T_int.SInt -> T_int.Gt | T_real.SReal -> T_real.RGt | _ -> T_num.NGt (mk_fresh_svar ()))
  | "Stdlib.<" -> (match sort with T_int.SInt -> T_int.Lt | T_real.SReal -> T_real.RLt | _ -> T_num.NLt (mk_fresh_svar ()))
  | "Stdlib.>=" -> (match sort with T_int.SInt -> T_int.Geq | T_real.SReal -> T_real.RGeq | _ -> T_num.NGeq (mk_fresh_svar ()))
  | "Stdlib.<=" -> (match sort with T_int.SInt -> T_int.Leq | T_real.SReal -> T_real.RLeq | _ -> T_num.NLeq (mk_fresh_svar ()))
  | "Stdlib.=" | "Stdlib.=="(* ToDo *) -> T_bool.Eq
  | "Stdlib.<>" | "Stdlib.!="(* ToDo *) -> T_bool.Neq
  | s -> failwith @@ "unknown psym: " ^ s
let unop_of_str = function
  | "Stdlib.not" -> Formula.Not
  | s -> failwith @@ "unknown unop: " ^ s
let binop_of_str = function
  | "Stdlib.&&" | "Stdlib.&" -> Formula.And
  | "Stdlib.||" | "Stdlib.or" -> Formula.Or
  | s -> failwith @@ "unknown binop: " ^ s

(** refinement types of constants *)
let of_term ~print ~config term =
  let v =  mk_fresh_tvar_with "v" in
  let sort = Term.sort_of term in
  if Term.is_var term then
    let (tvar, sort), _ = Term.let_var term in
    let name = Ident.name_of_tvar tvar in
    if is_fsym name then
      of_fsym ~print ~config (fsym_of_str name) sort
    else if is_psym name then
      of_psym ~print ~config (psym_of_str (List.hd_exn @@ Sort.args_of sort) name) sort
    else if is_unop name then
      of_unop ~config (unop_of_str name)
    else if is_binop name then
      of_binop ~config (binop_of_str name)
    else mk_rgeneral ~config v sort @@ Formula.eq (Term.mk_var v sort) term
  else mk_rgeneral ~config v sort @@ Formula.eq (Term.mk_var v sort) term

(** refinement types of constructors *)
let dtrenv = ref Map.Poly.empty
let of_constructor ~print ~config cons_name dt =
  let rec inner rev_args sorts =
    let x = mk_fresh_tvar_with "x" in
    match sorts with
    | [] ->
      let x_term = Term.mk_var x (T_dt.SDT dt) in
      let params =
        List.map (Datatype.args_of dt) ~f:(fun s ->
            if config.gen_type_temp_for_constrs then
              val_type_of_sort ~config (List.rev rev_args) s
            else mk_simple_val_rtype ~config s)
      in
      mk_rgeneral ~config ~params x (T_dt.SDT dt) @@
      Formula.and_of @@
      (Formula.mk_atom @@ T_dt.mk_is_cons dt cons_name x_term) ::
      List.mapi (List.rev rev_args) ~f:(fun i (term, _) ->
          Formula.eq term @@ T_dt.mk_sel dt (ConstDatatype.name_of_sel cons_name i) x_term)
    | hd :: tl ->
      let argt =
        if config.gen_type_temp_for_constrs then val_type_of_sort ~config (List.rev rev_args) hd
        else mk_simple_val_rtype ~config hd(* ToDo: use [Datatype.args_of dt] *)
      in
      mk_rarrow x argt
        (comp_type_of ~config [] @@ inner ((Term.mk_var x hd, hd) :: rev_args) tl) @@
      mk_fresh_trivial_pred ()
  in
  match Map.Poly.find !dtrenv (cons_name, dt) with
  | Some t -> t (* the refinement type template for the constructor already generated *)
  | None ->
    let svs =
      Set.Poly.of_list @@ List.filter_map (Datatype.args_of dt)
        ~f:(function Sort.SVar svar -> Some svar | _ -> None)
    in
    let t =
      mk_type_poly ~config svs @@ comp_type_of ~config [] @@
      inner [] @@ Datatype.sorts_of_cons_name dt cons_name
    in
    print @@ lazy ("assigning " ^ cons_name ^ " : " ^ str_of_val ~config t);
    dtrenv := Map.Poly.add_exn !dtrenv ~key:(cons_name, dt) ~data:t;
    t

(** auxiliary functions for constraint generation *)

let rec constr_of ~print ~config ?(depth = 0(*ToDo*)) (renv, phis) =
  Formula.and_of @@ Set.Poly.to_list @@ Set.Poly.union phis @@
  Set.Poly.filter_map (Map.to_set renv) ~f:(fun (x, ty) ->
      let x_term = Term.mk_var x @@ sort_of_val ty in
      match ty with
      | RGeneral ([], _sort, (v, phi)) ->
        Some (Formula.subst (Map.Poly.singleton v x_term) phi)
      | RGeneral (_params, T_dt.SDT dt, (v, phi)) ->
        Option.return @@
        if depth > 0 then
          Formula.and_of @@
          Formula.subst (Map.Poly.singleton v x_term) phi ::
          (*let dt = Datatype.update_args dt @@ List.map params ~f:sort_of_val in*)
          List.map (Datatype.conses_of dt) ~f:(fun cons ->
              (*print @@ lazy cons.name;*)
              let ty, _constrs(* [constrs] is empty *) =
                let cty = of_constructor ~print ~config cons.name dt in
                instantiate_val ~print ~config Map.Poly.empty cty (sort_of_val cty)
              in
              let args, _ret = args_ret_of_val_type @@ aconv_val_type Map.Poly.empty ty in
              let sub = Map.of_list_exn @@ List.mapi args ~f:(fun i (v, _) ->
                  v, T_dt.mk_sel_by_cons dt cons.name i x_term) in
              Formula.mk_imply
                (Formula.mk_atom @@ T_dt.mk_is_cons dt cons.name x_term)
                (Formula.subst sub @@ constr_of ~print ~config ~depth:(depth - 1)
                   (Map.Poly.of_alist_exn args, Set.Poly.empty)))
        else Formula.subst (Map.Poly.singleton v x_term) phi
      | RTuple (ts, (v, phi)) ->
        let args = List.map ts ~f:(fun t -> mk_fresh_tvar_with "v", t) in
        let sorts = List.map ts ~f:sort_of_val in
        let sub = Map.of_list_exn @@ List.mapi args ~f:(fun i (v, _) ->
            v, T_tuple.mk_tuple_sel sorts x_term i) in
        Option.return @@ Formula.and_of
          [Formula.subst (Map.Poly.singleton v x_term) phi;
           Formula.subst sub @@ constr_of ~print ~config ~depth
             (Map.Poly.of_alist_exn args, Set.Poly.empty)]
      | RArrow (_y, _t, _c, (v, phi)) ->
        Some (Formula.subst (Map.Poly.singleton v x_term) phi)
      | _ -> None)

let compose_temp_eff es =
  let fin, infs =
    List.fold_left ~init:(T_sequence.mk_eps (), []) es ~f:(fun (s, acc) ((x, _), (y, _)) ->
        T_sequence.concat ~fin:true s @@ Term.mk_var x T_sequence.SFinSequence,
        (T_sequence.concat ~fin:false s @@ Term.mk_var y T_sequence.SInfSequence) :: acc)
  in
  let x = mk_fresh_tvar_with "fin" in
  let y = mk_fresh_tvar_with "inf" in
  let xs = List.map es ~f:(fun ((x, _), _) -> x(*assume distinct*), T_sequence.SFinSequence) in
  let ys = List.map es ~f:(fun (_, (y, _)) -> y(*assume distinct*), T_sequence.SInfSequence) in
  let fin_senvs, fin_phis =
    List.unzip @@ List.map es ~f:(fun ((_, phi), _) ->
        Formula.split_exists @@ Formula.aconv_tvar phi)
  in
  let inf_senvs, inf_phis =
    List.unzip @@ List.map es ~f:(fun (_, (_, phi)) ->
        Formula.split_exists @@ Formula.aconv_tvar phi)
  in
  (x,
   Formula.exists (List.concat @@ xs :: fin_senvs) @@ Formula.and_of @@
   Formula.eq (Term.mk_var x T_sequence.SFinSequence) fin :: fin_phis),
  (y,
   Formula.exists (List.concat @@ xs :: ys :: fin_senvs @ inf_senvs) @@ Formula.and_of @@
   (Formula.or_of @@
    List.map2_exn (List.rev infs) inf_phis ~f:(fun inf inf_phi ->
        Formula.and_of [Formula.eq (Term.mk_var y T_sequence.SInfSequence) inf; inf_phi])) ::
   fin_phis)
let rec compose_temp_cont es = function
  | Pure -> Pure
  | Eff (x, c1, c2) -> Eff (x, c1, compose_temp_comp es c2)
and compose_temp_comp es (o, t, e, s) = o, t, compose_temp_eff (es @ [e]), compose_temp_cont es s

let rec compose_cont_temp s es = match s with
  | Pure -> Pure
  | Eff (x, c1, c2) -> Eff (x, c1, compose_comp_temp c2 es)
and compose_comp_temp (o, t, e, s) es = o, t, compose_temp_eff (e :: es), compose_cont_temp s es

let compose_temp_eff_inv ~print ~config renv ((x1, phi1), (y1, psi1)) ((x2, phi2), (y2, psi2)) =
  let sub1 =
    Map.Poly.singleton x2 @@ T_sequence.concat ~fin:true
      (Term.mk_var x1 T_sequence.SFinSequence)
      (Term.mk_var x2 T_sequence.SFinSequence)
  in
  let sub2 =
    Map.Poly.singleton y2 @@ T_sequence.concat ~fin:false
      (Term.mk_var x1 T_sequence.SFinSequence)
      (Term.mk_var y2 T_sequence.SInfSequence)
  in
  let _, psi1 = Formula.split_exists(*ToDo*) psi1 in
  let _, phi1 = Formula.split_exists(*ToDo*) phi1 in
  (if config.enable_temp_eff then
     (Set.Poly.singleton @@ Formula.mk_imply
        (Evaluator.simplify @@ constr_of ~print ~config @@ Env.add_phi renv psi1)
        (Evaluator.simplify @@ Formula.rename (Map.Poly.singleton y2 y1) psi2))
   else Set.Poly.empty),
  ((x2, Formula.forall [x1, T_sequence.SFinSequence] @@
    Evaluator.simplify @@ Formula.mk_imply phi1 @@ Formula.subst sub1 phi2),
   (y2, Formula.forall [x1, T_sequence.SFinSequence] @@
    Evaluator.simplify @@ Formula.mk_imply phi1 @@ Formula.subst sub2 psi2))
let rec compose_temp_cont_inv ~print ~config renv e = function
  | Pure -> Set.Poly.empty, Pure
  | Eff (x, c1, c2) ->
    let constrs, c2' = compose_temp_comp_inv ~print ~config renv e c2 in
    constrs, Eff (x, c1, c2')
and compose_temp_comp_inv ~print ~config renv e (o, t, e', s) =
  let constrs1, e'' = compose_temp_eff_inv ~print ~config renv e e' in
  let constrs2, s' = compose_temp_cont_inv ~print ~config renv e s in
  Set.Poly.union constrs1 constrs2, (o, t, e'', s')

let fresh_eff_pvars_temp ~print ((x1, phi1), (x2, phi2)) =
  if Formula.is_atom phi1 && Formula.is_atom phi2 then
    let atm1, _ = Formula.let_atom phi1 in
    let atm2, _ = Formula.let_atom phi2 in
    if Atom.is_pvar_app atm1 && Atom.is_pvar_app atm2 then begin
      let pvar1, sorts1, ts1, info1 = Atom.let_pvar_app atm1 in
      let pvar2, sorts2, ts2, info2 = Atom.let_pvar_app atm2 in
      let pvar1' = mk_fresh_pvar () in
      print @@ lazy
        (sprintf "a new predicate variable %s represents the inductive predicate %s"
           (Ident.name_of_pvar pvar1') (Ident.name_of_pvar pvar1));
      let pvar2' = mk_fresh_pvar () in
      print @@ lazy
        (sprintf "a new predicate variable %s represents the coinductive predicate %s"
           (Ident.name_of_pvar pvar2') (Ident.name_of_pvar pvar2));
      let phi1' = Formula.mk_atom @@ Atom.mk_pvar_app pvar1' sorts1 ts1 ~info:info1 in
      let phi2' = Formula.mk_atom @@ Atom.mk_pvar_app pvar2' sorts2 ts2 ~info:info2 in
      ((x1, phi1'), (x2, phi2')),
      Map.Poly.of_alist_exn [(pvar1, `LFP pvar1'); (pvar2, `GFP pvar2')]
    end else ((x1, phi1), (x2, phi2)), Map.Poly.empty(*ToDo*)
  else ((x1, phi1), (x2, phi2)), Map.Poly.empty(*ToDo*)
let rec fresh_eff_pvars_val_cont ~print = function
  | Pure -> Pure, Map.Poly.empty
  | Eff (x, c1, c2) ->
    let c2', map2 = fresh_eff_pvars_comp ~print c2 in
    Eff (x, c1, c2'), map2
and fresh_eff_pvars_comp ~print (o, t, e, s) =
  let e', map1 = fresh_eff_pvars_temp ~print e in
  let s', map2 = fresh_eff_pvars_val_cont ~print s in
  (o, t, e', s'), Map.force_merge_list [map1; map2]
and fresh_eff_pvars_val ~print = function
  | RArrow (y, t, c, (x, phi)) ->
    let c, map = fresh_eff_pvars_comp ~print c in
    RArrow (y, t, c, (x, phi)), map
  | t -> t, Map.Poly.empty

let rec of_args_ret ~config ?(temp = false) ?(ropsig = empty_opsig) ?(cont = None) dom xs args ret =
  match xs, args with
  | [], [] ->
    assert Stdlib.(cont = None || cont = Some []);
    [], ret
  | x :: xs', arg :: args' ->
    let dom' = let sort = sort_of_val arg in dom @ [Term.mk_var x sort, sort] in
    let cont'', cont' =
      match cont with
      | None -> Sort.Pure, None
      | Some (eff :: effs') -> eff, Some effs'
      | _ -> failwith "of_args_ret"
    in
    let cs, ret' = of_args_ret ~config ~temp ~ropsig ~cont:cont' dom' xs' args' ret in
    let c = comp_type_of ~config ~temp ~opsig:(`Refined ropsig) ~cont:cont'' dom ret' in
    c :: cs, mk_rarrow x arg c @@ mk_fresh_trivial_pred ()
  | _ -> assert false
