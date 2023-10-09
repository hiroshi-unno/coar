open Core
open Common.Ext
open Common.Util
open Common.Combinator
open Ident
open LogicOld

type config = {
  depend_on_func_args: bool;
  depend_on_ref_args: bool;
  depend_on_unit_args: bool;
  (* generate a refinement predicate for each type variable *)
  gen_ref_pred_for_type_vars: bool;
  (* share a refinement predicate with all occurrences of the same type variable *)
  share_ref_pred_with_same_type_vars: bool;
  (* generate a refinement predicate for each function type *)
  gen_ref_pred_for_fun_types: bool;
  (* generate a refinement predicate for each ref type *)
  gen_ref_pred_for_ref_types: bool;
  (* generate a refinement predicate for each tuple element *)
  gen_ref_pred_for_tup_elems: bool;
  (* generate a refinement predicate for each datatype parameter *)
  gen_ref_pred_for_dt_params: bool;
  (* generate a refinement type template for each constructor *)
  gen_ref_type_temp_for_constructors: bool;
  (* no assertion failure *)
  never_fail: bool;
  (* only total applications can cause assertion failures *)
  can_fail_only_at_total_apps: bool;
  (* only total applications can cause temporal effects *)
  can_cause_temp_eff_only_at_total_apps: bool;
  (* enable dependent temporal control effects *)
  enable_temp_eff: bool;
  (* enable predicate polymorphism for constructors *)
  enable_pred_poly_for_constructors: bool;
  (* enable predicate polymorphism for ref types *)
  enable_pred_poly_for_ref_types: bool;
  (* instantiate unbound sort variables to int before constraint solving *)
  instantiate_svars_to_int: bool
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
and o = (string, t) ALMap.t
(** computation types \Sigma |> T & \Phi / S *)
and c = o(*\Sigma*) * t(*T*) * e(*\Phi*) * s(*S*)
(** value types T *)
and t =
  (** {x: (T_1, ... , T_n) T | \phi}*)
  | RGeneral of t list(*(T_1, ... , T_n)*) * Sort.t(*T*) * p(*x.\phi*)
  (** {x: T_1 * ... * T_n | \phi} *)
  | RTuple of t list(*(T_1, ... , T_n)*) * p(*x.\phi*)
  (** {x: T ref | \phi} *)
  | RRef of t(*T*) * p(*x.\phi*)
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

let rec map_formula_cont ~f = function
  | Pure -> Pure
  | Eff (x, c1, c2) -> Eff (x, map_formula_comp ~f c1, map_formula_comp ~f c2)
and map_formula_temp ~f (p1, p2) = (map_pred ~f p1, map_pred ~f p2)
and map_formula_opsig ~f opsig = ALMap.map ~f:(map_formula_val ~f) opsig
and map_formula_comp ~f (o, t, e, s) =
  map_formula_opsig ~f o, map_formula_val ~f t,
  map_formula_temp ~f e, map_formula_cont ~f s
and map_formula_val ~f = function
  | RGeneral (params, sort, pred) ->
    RGeneral (List.map params ~f:(map_formula_val ~f), sort, map_pred ~f pred)
  | RTuple (elems, pred) ->
    RTuple (List.map elems ~f:(map_formula_val ~f), map_pred ~f pred)
  | RRef (elem, pred) ->
    RRef (map_formula_val ~f elem, map_pred ~f pred)
  | RArrow (x, t, c, pred) ->
    RArrow (x, map_formula_val ~f t, map_formula_comp ~f c, map_pred ~f pred)
  | RForall (penv, constrs, c) ->
    RForall (penv, Set.Poly.map ~f constrs, map_formula_comp ~f c)
  | RPoly (svs, c) ->
    RPoly (svs, map_formula_comp ~f c)

(** Destruction *)

(*** value types *)
let let_rgeneral = function RGeneral (params, s, pred) -> params, s, pred | _ -> assert false
let let_rarrow = function RArrow (x, t1, t2, pred) -> x, t1, t2, pred | _ -> assert false
let let_rtuple = function RTuple (ts, pred) -> ts, pred | _ -> assert false
let let_rref = function RRef (t, pred) -> t, pred | _ -> assert false
let let_pred_poly = function
  | RForall (penv, constrs, (_, t, _, _)(*ToDo*)) -> penv, constrs, t
  | t -> Map.Poly.empty, Set.Poly.empty, t
let let_type_poly = function
  | RPoly (svs, (_, t, _, _)(*ToDo*)) -> svs, t
  | t -> Set.Poly.empty, t

let tvar_of_val = function
  | RGeneral (_, _, (x, _)) | RTuple (_, (x, _))
  | RRef (_, (x, _)) | RArrow (_, _, _, (x, _)) -> x
  | _ -> assert false

(*** computation types *)
let opsig_of_comp (o, _, _, _) = o
let val_of_comp (_, t, _, _) = t
let temp_of_comp (_, _, e, _) = e
let cont_of_comp (_, _, _, s) = s

(** Observation *)

let is_trivial_pred (_, phi) = Formula.is_true phi(*ToDo*)
let is_trivial_temp (p1, p2) = is_trivial_pred p1 && is_trivial_pred p2
let is_pure_cont = function Pure -> true | Eff _ -> false
let is_pure_temp ((x1, phi1), (_, phi2)) =(*ToDo*)
  Formula.is_false phi2 &&
  Formula.is_eq phi1 && let t1, t2, _ = Formula.let_eq phi1 in
  Term.is_var t1 && let (x, sort), _ = Term.let_var t1 in
  String.(Ident.name_of_tvar x = Ident.name_of_tvar x1) &&
  Stdlib.(sort = T_sequence.SSequence true) &&
  (*Stdlib.(t2 = T_sequence.mk_eps ())*)
  Term.is_app t2 && let fsym, args, _ = Term.let_app t2 in
  Stdlib.(fsym = T_sequence.SeqEpsilon) && List.is_empty args
let is_pure_comp ~config (o, _t, e, s) =
  ALMap.is_empty o && (not config.enable_temp_eff || is_pure_temp e) && is_pure_cont s

let is_rgeneral = function RGeneral _ -> true | _ -> false
let is_rarrow = function RArrow _ -> true | _ -> false
let is_rtuple = function RTuple _ -> true | _ -> false
let is_rref = function RRef _ -> true | _ -> false
let is_pred_poly = function RForall _ -> true | _ -> false
let is_type_poly = function RPoly _ -> true | _ -> false

let rec is_simple_comp (o, t, e, s) =
  ALMap.is_empty o && is_simple_val t && is_trivial_temp e && is_pure_cont s
and is_simple_val = function
  | RArrow (_, t, c, p) ->
    is_trivial_pred p && is_simple_val t && is_simple_comp c
  | RGeneral (ts, _, p) | RTuple (ts, p) ->
    is_trivial_pred p && List.for_all ts ~f:is_simple_val
  | RRef (_, _) | RForall (_, _, _) | RPoly (_, _) -> false

let rec tvs_of_cont = function
  | Pure -> Set.Poly.empty
  | Eff (x, c1, c2) ->
    Set.union (Set.remove (tvs_of_comp c1) x) (tvs_of_comp c2)
and tvs_of_pred (x, phi) = Set.remove (Formula.tvs_of phi) x
and tvs_of_temp (p1, p2) = Set.union (tvs_of_pred p1) (tvs_of_pred p2)
and tvs_of_opsig (opmap: o) =
  opmap |> ALMap.data |> List.map ~f:tvs_of_val |> Set.Poly.union_list
and tvs_of_comp (o, t, e, s) =
  Set.Poly.union_list [tvs_of_opsig o; tvs_of_val t; tvs_of_temp e; tvs_of_cont s]
and tvs_of_val = function
  | RGeneral (ts, _, p) | RTuple (ts, p) ->
    Set.Poly.union_list @@ tvs_of_pred p :: List.map ~f:tvs_of_val ts
  | RRef (t, p) ->
    Set.union (tvs_of_pred p) (tvs_of_val t)
  | RArrow (x, t, c, p) ->
    Set.Poly.union_list [tvs_of_val t; Set.remove (tvs_of_comp c) x; tvs_of_pred p]
  | RForall (_penv, phis, c) ->
    Set.union (Set.concat_map ~f:Formula.tvs_of phis) (tvs_of_comp c)
  | RPoly (_svs, c) -> tvs_of_comp c

let rec pvs_of_cont = function
  | Pure -> Set.Poly.empty
  | Eff (_, c1, c2) -> Set.union (pvs_of_comp c1) (pvs_of_comp c2)
and pvs_of_pred (_, phi) = Formula.pvs_of phi
and pvs_of_temp (p1, p2) = Set.union (pvs_of_pred p1) (pvs_of_pred p2)
and pvs_of_opsig (opmap: o) =
  opmap |> ALMap.data |> List.map ~f:pvs_of_val |> Set.Poly.union_list
and pvs_of_comp (o, t, e, s) =
  Set.Poly.union_list [pvs_of_opsig o; pvs_of_val t; pvs_of_temp e; pvs_of_cont s]
and pvs_of_val = function
  | RGeneral (ts, _, p) | RTuple (ts, p) ->
    Set.Poly.union_list @@ pvs_of_pred p :: List.map ~f:pvs_of_val ts
  | RRef (t, p) ->
    Set.union (pvs_of_pred p) (pvs_of_val t)
  | RArrow (_, t, c, p) ->
    Set.Poly.union_list [pvs_of_val t; pvs_of_comp c; pvs_of_pred p]
  | RForall (penv, phis, c) ->
    Set.diff
      (Set.union (Set.concat_map ~f:Formula.pvs_of phis) (pvs_of_comp c))
      (Set.Poly.of_list @@ Map.Poly.keys penv)
  | RPoly (_svs, c) -> pvs_of_comp c

let rec pred_sort_env_of_cont ?(bpvs = Set.Poly.empty) = function
  | Pure -> Set.Poly.empty
  | Eff (_, c1, c2) ->
    Set.union (pred_sort_env_of_comp ~bpvs c1) (pred_sort_env_of_comp ~bpvs c2)
and pred_sort_env_of_pred ?(bpvs = Set.Poly.empty) (_, phi) =
  Formula.pred_sort_env_of ~bpvs phi
and pred_sort_env_of_temp ?(bpvs = Set.Poly.empty) (p1, p2) =
  Set.union (pred_sort_env_of_pred ~bpvs p1) (pred_sort_env_of_pred ~bpvs p2)
and pred_sort_env_of_opsig ?(bpvs = Set.Poly.empty) =
  ALMap.data >> List.map ~f:(pred_sort_env_of_val ~bpvs) >> Set.Poly.union_list
and pred_sort_env_of_comp ?(bpvs = Set.Poly.empty) (o, t, e, s) =
  Set.Poly.union_list
    [pred_sort_env_of_opsig ~bpvs o; pred_sort_env_of_val ~bpvs t;
     pred_sort_env_of_temp ~bpvs e; pred_sort_env_of_cont ~bpvs s]
and pred_sort_env_of_val ?(bpvs = Set.Poly.empty) = function
  | RGeneral (params, _, p) | RTuple (params, p) ->
    Set.Poly.union_list @@
    pred_sort_env_of_pred ~bpvs p :: List.map params ~f:(pred_sort_env_of_val ~bpvs)
  | RRef (param, p) ->
    Set.union (pred_sort_env_of_pred ~bpvs p) (pred_sort_env_of_val ~bpvs param)
  | RArrow (_, t, c, p) ->
    Set.Poly.union_list
      [pred_sort_env_of_val ~bpvs t; pred_sort_env_of_comp ~bpvs c;
       pred_sort_env_of_pred ~bpvs p]
  | RForall (penv, phis, c) ->
    let bpvs = Set.union bpvs @@ Set.Poly.of_list @@ Map.Poly.keys penv in
    Set.union
      (Set.concat_map ~f:(Formula.pred_sort_env_of ~bpvs) phis)
      (pred_sort_env_of_comp ~bpvs c)
  | RPoly (_svs, c) -> pred_sort_env_of_comp ~bpvs c

let rec args_of_comp (_, t, _, _) = args_of_val t
and args_of_val = function RArrow (x, t, c, _) -> (x, t) :: args_of_comp c | _ -> []
let rec ret_of_comp (_, t, _, _) = ret_of_val t
and ret_of_val = function RArrow (_, _, c, _) -> ret_of_comp c | t -> t
let rec args_ret_of_comp (_, t, _, _) = args_ret_of_val t
and args_ret_of_val = function
  | RArrow (x, t, c, _) ->
    let args, ret = args_ret_of_comp c in
    (x, t) :: args, ret
  | t -> [], t
let rec mono_type_of_comp (_, t, _, _) = mono_type_of_val t
and mono_type_of_val = function
  | RForall (_, _, c) -> mono_type_of_comp c
  | RPoly (_, c) -> mono_type_of_comp c
  | t -> t

let eq_dt sort1 sort2 =
  match sort1, sort2 with
  | T_dt.SDT dt1, T_dt.SDT dt2 ->
    String.(dt1.name = dt2.name) && Stdlib.(Datatype.params_of dt1 = Datatype.params_of dt2)
  | T_dt.SDT dt1, T_dt.SUS (name2, sorts2) ->
    String.(dt1.name = name2) && Stdlib.(Datatype.params_of dt1 = sorts2)
  | T_dt.SUS (name1, sorts1), T_dt.SDT dt2 ->
    String.(name1 = dt2.name) && Stdlib.(sorts1 = Datatype.params_of dt2)
  | T_dt.SUS (n1, sorts1), T_dt.SUS (n2, sorts2) ->
    String.(n1 = n2) && Stdlib.(sorts1 = sorts2)
  | _ -> false

let rec opsig_of opsig = Sort.OpSig (ALMap.map opsig ~f:sort_of_val, None)
and cont_of = function
  | Pure -> Sort.Pure
  | Eff (_, (o1, t1, _, s1), (o2, t2, _, s2)) ->
    Sort.Eff (opsig_of o1, sort_of_val t1, cont_of s1,
              opsig_of o2, sort_of_val t2, cont_of s2)
and full_sort_of_comp (o, t, _e, s) =
  opsig_of o, sort_of_val t, cont_of s
and sort_of_val = function
  | RGeneral (params, T_dt.SDT dt, _) ->
    let sorts = List.map params ~f:sort_of_val in
    (*assert Stdlib.(sorts = Datatype.params_of dt);*)
    T_dt.SDT (Datatype.update_params dt sorts)
  | RGeneral (params, T_dt.SUS (name, _sorts'), _) ->
    let sorts = List.map params ~f:sort_of_val in
    (*assert Stdlib.(sorts = sorts');*)
    T_dt.SUS (name, sorts)
  | RGeneral (params, sort, _) ->
    if List.is_empty params then sort
    else failwith @@ Term.str_of_sort sort ^ " has non-empty parameters: "
  (*^ String.concat_map_list ~sep:", " params ~f:(str_of_val ~config:!cgen_config(*ToDo*))*)
  | RTuple (elems, _) ->
    T_tuple.STuple (List.map elems ~f:sort_of_val)
  | RRef (elem, _) ->
    T_ref.SRef (sort_of_val elem)
  | RArrow (_, t, c, _) ->
    Sort.SArrow (sort_of_val t, full_sort_of_comp c)
  | RForall (_, _, c) ->
    (match full_sort_of_comp c with
     | o, s, Sort.Pure when Sort.is_empty_opsig o -> s
     | _ -> failwith "sort_of_val")
  | RPoly (svs, c) ->
    Sort.mk_poly svs @@
    match full_sort_of_comp c with
    | o, s, Sort.Pure when Sort.is_empty_opsig o -> s
    | _ -> failwith "sort_of_val"
let sort_of_comp (_o, t, _e, _s) = sort_of_val t

(** Printer *)

let str_of_pred (x, phi) = sprintf "%s. %s" (Ident.name_of_tvar x) (Formula.str_of phi)
let rec str_of_temp (pred1, pred2) =
  (*String.paren @@*) sprintf "%s, %s" (str_of_pred pred1) (str_of_pred pred2)
and str_of_cont ~config = function
  | Pure -> "_"
  | Eff (x, c1, c2) ->
    sprintf  "(forall %s. %s) => %s"
      (Ident.name_of_tvar x) (str_of_comp ~config c1) (str_of_comp ~config c2)
and str_of_opsig ~config (opsig: o) =
  opsig
  |> ALMap.to_alist
  |> String.concat_map_list ~sep:", " ~f:(fun (op, t) -> op ^ ": " ^ str_of_val ~config t)
  |> sprintf "{%s}"
and str_of_comp ~config (o, t, e, s) =
  let b = not config.enable_temp_eff || is_pure_temp e in
  sprintf
    (if ALMap.is_empty o && b && is_pure_cont s then "%s%s%s%s" else "(%s%s%s%s)")
    (if ALMap.is_empty o then "" else str_of_opsig ~config o ^ " |> ")
    (str_of_val ~config t)
    (if b then "" else " & " ^ str_of_temp e)
    (if is_pure_cont s then "" else " / " ^ str_of_cont ~config s)
and with_pred (x, phi) s =
  if is_trivial_pred (x, phi) then s
  else sprintf "{%s: %s | %s}" (Ident.name_of_tvar x) s (Formula.str_of phi)
and str_of_val ~config = function
  | RGeneral (params, sort, pred) ->
    let sort_name =
      match sort with T_dt.SDT dt -> Datatype.name_of dt | _ -> Term.str_of_sort sort
    in
    with_pred pred @@
    if List.is_empty params then sort_name
    else String.concat_map_list_append ~sep:"," params ~f:(str_of_val ~config) sort_name
  | RTuple (elems, pred) ->
    with_pred pred @@
    String.concat_map_list ~sep:" * " elems ~f:(str_of_val ~config)
  | RRef (elem, pred) ->
    with_pred pred @@
    sprintf "%s ref" @@ String.paren @@ str_of_val ~config elem
  | RArrow (x, t, c, pred) ->
    with_pred pred @@
    if Set.mem (tvs_of_comp c) x then
      sprintf "(%s:%s) -> %s"
        (Ident.name_of_tvar x) (str_of_val ~config t) (str_of_comp ~config c)
    else
      let s = sort_of_val t in
      sprintf "%s -> %s"
        ((if Sort.is_arrow s || Sort.is_poly s then String.paren else Fn.id) @@
         str_of_val ~config t)
        (str_of_comp ~config c)
  | RForall (penv, phis, c) ->
    if Map.Poly.is_empty penv && Set.is_empty phis then
      str_of_comp ~config c
    else if Set.is_empty phis then
      sprintf "forall %s. %s"
        (String.concat_map_list ~sep:"," ~f:Ident.name_of_pvar @@ Map.Poly.keys penv)
        (str_of_comp ~config c)
    else
      sprintf "forall (%s | %s). %s"
        (String.concat_map_list ~sep:"," ~f:Ident.name_of_pvar @@ Map.Poly.keys penv)
        (String.concat_set ~sep:"; " @@ Set.Poly.map phis ~f:Formula.str_of)
        (str_of_comp ~config c)
  | RPoly (svs, c) ->
    if Set.is_empty svs then failwith "[str_of_val.RPoly]"(*str_of_comp ~config c*)
    else if Set.is_singleton svs then
      sprintf "forall %s. %s"
        (Ident.name_of_svar @@ Set.choose_exn svs)
        (str_of_comp ~config c)
    else
      sprintf "forall (%s). %s"
        (String.concat_set ~sep:"," @@ Set.Poly.map ~f:Ident.name_of_svar svs)
        (str_of_comp ~config c)

(** Construction *)

let mk_fresh_tvar_with pre = Ident.mk_fresh_tvar ~prefix:(Some ("$" ^ pre)) ()
let mk_fresh_trivial_pred () = mk_fresh_tvar_with "v", Formula.mk_true ()
let mk_rbase sort p = RGeneral ([], sort, p)
let mk_rcompound params sort p = RGeneral (params, sort, p)
let mk_rdt params dt p = RGeneral (params, T_dt.SDT dt, p)
let mk_rus params name sorts p = RGeneral (params, T_dt.SUS (name, sorts), p)
let mk_rtuple elems p = RTuple (elems, p)
let mk_rref elem p = RRef (elem, p)
let mk_rarrow x t c p = RArrow (x, t, c, p)
let mk_type_poly ~config svs1 = function
  | (_, t, _, _) as c when is_pure_comp ~config c ->
    (match t with
     | RPoly (svs2, c) -> RPoly (Set.union svs1 svs2, c)
     | _ -> if Set.is_empty svs1 then t else RPoly (svs1, c))
  | c -> assert (Fn.non Set.is_empty svs1); RPoly (svs1, c)
let mk_pred_poly ~config penv1 constrs1 = function
  | (_, t, _, _) as c when is_pure_comp ~config c ->
    (match t with
     | RForall (penv2, constrs2, c) ->
       RForall (Map.force_merge penv1 penv2, Set.union constrs1 constrs2, c)
     | _ ->
       if Map.Poly.is_empty penv1 && Set.is_empty constrs1 then t
       else RForall (penv1, constrs1, c))
  | c -> assert (Fn.non Map.Poly.is_empty penv1); RForall (penv1, constrs1, c)

let filter_dom ~config =
  List.filter ~f:(fun (_, sort) ->
      if Sort.is_arrow sort then config.depend_on_func_args
      else if T_ref.is_ref_sort sort then config.depend_on_ref_args
      else if Datatype.is_unit_sort sort then config.depend_on_unit_args
      else true)
let mk_refpred ~config pv dom v sort =
  let args, sorts = List.unzip @@ filter_dom ~config dom in
  (*let sort = Sort.pure_sort_of sort in
    let sorts = List.map ~f:Sort.pure_sort_of sorts in*)
  Formula.mk_atom @@ Atom.mk_pvar_app pv
    (sorts @ [sort]) (args @ [Term.mk_var v sort])
let position_of position id = sprintf "%s[:%d]" position id
let papp_of ~config either dom v sort =
  let name =
    match either with
    | First (Some (base, position, id)) -> base ^ position_of position id
    | First None -> name_of_pvar @@ mk_fresh_pvar ()
    | Second prefix -> name_of_pvar @@ mk_fresh_pvar ~prefix:(Some prefix) ()
  in
  mk_refpred ~config (Pvar name) dom v sort
let mk_temp_val () =
  let x = mk_fresh_tvar_with "fin" in
  (x, Formula.eq (Term.mk_var x @@ T_sequence.SSequence true) @@ T_sequence.mk_eps ()),
  (mk_fresh_tvar_with "inf", Formula.mk_false ())
let mk_temp_trivial () =
  (mk_fresh_tvar_with "fin", Formula.mk_true ()),
  (mk_fresh_tvar_with "inf", Formula.mk_true ())
let mk_temp_fresh ~config dom =
  let x = mk_fresh_tvar_with "fin" in
  (x, papp_of ~config (Second "fin_pred") dom x @@ T_sequence.SSequence true),
  let y = mk_fresh_tvar_with "inf" in
  (y, papp_of ~config (Second "inf_pred") dom y @@ T_sequence.SSequence false)

let rec nu_of_cont x = function
  | Pure -> Formula.mk_true ()
  | Eff (_, _, c) -> nu_of_comp x c
and nu_of_comp x (_, _, ((_, _), (y, phi)), s) =
  Formula.and_of [Formula.rename (Map.Poly.singleton y x) phi; nu_of_cont x s]

let conj_pred_val (z, psi) = function
  | RGeneral (params, sort, (x, phi)) ->
    let psi = Formula.rename (Map.Poly.singleton z x) psi in
    mk_rcompound params sort (x, Formula.and_of [phi; psi])
  | RTuple (elems, (x, phi)) ->
    let psi = Formula.rename (Map.Poly.singleton z x) psi in
    mk_rtuple elems (x, Formula.and_of [phi; psi])
  | RRef (elem, (x, phi)) ->
    let psi = Formula.rename (Map.Poly.singleton z x) psi in
    mk_rref elem (x, Formula.and_of [phi; psi])
  | RArrow (y, t, c, (x, phi)) ->
    let psi = Formula.rename (Map.Poly.singleton z x) psi in
    mk_rarrow y t c (x, Formula.and_of [phi; psi])
  | RForall (_penv, _phis, _c) -> failwith "not supported"
  | RPoly (_svs, _c) -> failwith "not supported"

let rec simple_val_of_sort ~config ?(svmap=Map.Poly.empty) = function
  | Sort.SPoly (svs, sort) ->
    mk_type_poly ~config svs @@
    simple_pure_comp_of_sort ~config ~svmap sort
  | Sort.SArrow (sort1, (opsig, sort2, cont)) ->
    mk_rarrow (mk_fresh_tvar_with "x") (simple_val_of_sort ~config ~svmap sort1)
      (simple_comp_of_sort ~config ~svmap ~temp:false ~opsig:(`Sort opsig) ~cont sort2)
      (mk_fresh_trivial_pred ())
  | Sort.SVar svar when Map.Poly.mem svmap svar ->
    Map.Poly.find_exn svmap svar
  | T_tuple.STuple sorts ->
    let elems = List.map sorts ~f:(simple_val_of_sort ~config ~svmap) in
    mk_rtuple elems @@ mk_fresh_trivial_pred ()
  | T_dt.SDT dt ->
    let sorts = Datatype.params_of dt in
    let params = List.map sorts ~f:(simple_val_of_sort ~config ~svmap) in
    mk_rdt params dt @@ mk_fresh_trivial_pred ()
  | T_dt.SUS (name, sorts) ->
    let params = List.map sorts ~f:(simple_val_of_sort ~config ~svmap) in
    mk_rcompound params (T_dt.SUS (name, sorts)) @@ mk_fresh_trivial_pred ()
  | T_ref.SRef sort ->
    mk_rref (simple_val_of_sort ~config ~svmap sort) (mk_fresh_trivial_pred ())
  | sort -> mk_rbase sort @@ mk_fresh_trivial_pred ()
and simple_comp_of_val ~config ?(svmap=Map.Poly.empty)
    ?(temp=false) ?(opsig=`Refined ALMap.empty) ?(cont=Sort.Pure) val_type =
  let ropsig =
    match opsig with
    | `Refined ropsig -> ropsig
    | `Sort Sort.OpSig (opmap, _r) ->
      ALMap.map opmap ~f:(simple_val_of_sort ~config ~svmap)
    | _ -> failwith "[simple_comp_of_val]"
  in
  let temp_eff = mk_temp_trivial () in
  let cont_eff =
    match cont with
    | Sort.Pure -> Pure
    | Sort.Eff (o1, s1, cont1, o2, s2, cont2) ->
      let x = mk_fresh_tvar_with "x" in
      let c1 =
        simple_comp_of_sort ~config ~svmap ~temp ~opsig:(`Sort o1) ~cont:cont1 s1
      in
      let c2 =
        simple_comp_of_sort ~config ~svmap ~temp ~opsig:(`Sort o2) ~cont:cont2 s2
      in
      Eff (x, c1, c2)
    | _ -> failwith @@ sprintf "[comp_of_val] %s not supported" (Term.str_of_cont cont)
  in
  ropsig, val_type, temp_eff, cont_eff
and simple_pure_comp_of_val ~config ?(svmap=Map.Poly.empty) =
  simple_comp_of_val ~config ~svmap ~temp:false
    ~opsig:(`Refined ALMap.empty) ~cont:Sort.Pure
and simple_comp_of_sort ~config ?(svmap=Map.Poly.empty) ~temp ~opsig ~cont sort =
  simple_comp_of_val ~config ~svmap ~temp ~opsig ~cont @@
  simple_val_of_sort ~config ~svmap sort
and simple_pure_comp_of_sort ~config ?(svmap=Map.Poly.empty) sort =
  simple_pure_comp_of_val ~config ~svmap @@ simple_val_of_sort ~config ~svmap sort

let rec val_of_sort (*~print*) ~config
    ?(refine=true) ?(svmap=Map.Poly.empty) ?(name=None) dom = function
  | Sort.SVar svar as sort ->
    if Map.Poly.mem svmap svar then Map.Poly.find_exn svmap svar
    else
      mk_rbase sort @@
      let v = mk_fresh_tvar_with "v" in
      v,
      if refine && config.gen_ref_pred_for_type_vars then
        papp_of ~config (First name) dom v sort
      else Formula.mk_true ()
  | Sort.SArrow (sort1, (opsig, sort2, cont)) as sort ->
    let x = mk_fresh_tvar_with "x" in
    let name_arg =
      if config.gen_ref_pred_for_fun_types || Sort.is_arrow sort1 then
        match name with
        | Some (base, position, id) -> Some (base, position_of position id, 0)
        | None -> None
      else name
    in
    let name_ret =
      match if Sort.is_arrow sort1 then name else name_arg with
      | Some (base, position, id) -> Some (base, position, id + 1)
      | None -> None
    in
    let t =
      let refine =
        Fn.non Sort.is_pure cont (*ToDo:[opsig]?*)||
        not (config.never_fail || config.can_fail_only_at_total_apps && Sort.is_arrow sort2)
      in
      val_of_sort ~config ~refine ~svmap ~name:name_arg dom sort1
    in
    let c =
      let dom' = dom @ [Term.mk_var x sort1, sort1] in
      let temp =
        not (config.can_cause_temp_eff_only_at_total_apps && Sort.is_arrow sort2)
      in
      let opsig = `Sort opsig in
      let refine = true(*ToDo*) in
      comp_of_sort ~config ~refine ~svmap ~temp ~opsig ~cont ~name:name_ret dom' sort2
    in
    mk_rarrow x t c @@
    let v = mk_fresh_tvar_with "v" in
    v,
    if refine && config.gen_ref_pred_for_fun_types then
      papp_of ~config (First name) dom v sort
    else Formula.mk_true ()
  | Sort.SPoly (svs, s) ->
    let refine = refine(*ToDo*) in
    mk_type_poly ~config svs @@
    pure_comp_of_sort ~config ~refine ~svmap ~name dom s
  | T_tuple.STuple sorts as sort ->
    let elems =
      let refine = config.gen_ref_pred_for_tup_elems in
      List.mapi sorts ~f:(fun i s ->
          let name =
            match name with
            | Some (base, position, id) -> Some (base, position_of position id, i)
            | None -> None
          in
          val_of_sort ~config ~refine ~svmap ~name dom s)
    in
    mk_rtuple elems @@
    let v = mk_fresh_tvar_with "v" in
    v,
    if refine then papp_of ~config (First name) dom v sort
    else Formula.mk_true ()
  | T_dt.SDT dt as sort ->
    let params =
      let refine = config.gen_ref_pred_for_dt_params in
      List.mapi (Datatype.params_of dt) ~f:(fun i s ->
          let name =
            match name with
            | Some (base, position, id) -> Some (base, position_of position id, i)
            | None -> None
          in
          val_of_sort ~config ~refine ~svmap ~name dom s)
    in
    mk_rdt params dt @@
    let v = mk_fresh_tvar_with "v" in
    v,
    if refine then papp_of ~config (First name) dom v sort
    else Formula.mk_true ()
  | T_dt.SUS (_, params) as sort ->
    let params =
      let refine = config.gen_ref_pred_for_dt_params in
      List.mapi params ~f:(fun i s ->
          let name =
            match name with
            | Some (base, position, id) -> Some (base, position_of position id, i)
            | None -> None
          in
          val_of_sort ~config ~refine ~svmap ~name dom s)
    in
    mk_rcompound params sort @@
    let v = mk_fresh_tvar_with "v" in
    v,
    if refine then papp_of ~config (First name) dom v sort
    else Formula.mk_true ()
  | T_ref.SRef s as sort ->
    let refine = true(*ToDo*) in
    let name_elem =
      match name with
      | Some (base, position, id) -> Some (base, position_of position id, 0)
      | None -> None
    in
    let elem = val_of_sort ~config ~refine ~svmap ~name:name_elem dom s in
    mk_rref elem @@
    let v = mk_fresh_tvar_with "v" in
    v,
    if refine && config.gen_ref_pred_for_ref_types then
      papp_of ~config (First name) dom v sort
    else Formula.mk_true ()
  | sort ->
    mk_rbase sort @@
    let v = mk_fresh_tvar_with "v" in
    v,
    if refine then papp_of ~config (First name) dom v sort
    else Formula.mk_true ()
and comp_of_val ~config ?(svmap=Map.Poly.empty)
    ?(temp=false) ?(opsig=`Refined ALMap.empty) ?(cont=Sort.Pure) dom val_type =
  let ropsig =
    match opsig with
    | `Refined ropsig -> ropsig
    | `Sort Sort.OpSig (opmap, _r) ->
      let refine = true(*ToDo*) in
      ALMap.map opmap ~f:(val_of_sort ~config ~refine ~svmap dom)
    | _ -> failwith "[comp_of_val]"
  in
  let temp_eff =
    if config.enable_temp_eff then
      if temp then mk_temp_fresh ~config dom else mk_temp_val ()
    else mk_temp_trivial ()
  in
  let cont_eff =
    match cont with
    | Sort.Pure -> Pure
    | Sort.Eff (o1, s1, cont1, o2, s2, cont2) ->
      let x = mk_fresh_tvar_with "x" in
      let c1 =
        let dom' =
          let sort = sort_of_val val_type in dom @ [Term.mk_var x sort, sort]
        in
        let refine = true(*ToDo*) in
        let opsig = `Sort o1 in
        comp_of_sort ~config ~refine ~svmap ~temp ~opsig ~cont:cont1 dom' s1
      in
      let c2 =
        let refine = true(*ToDo*) in
        let opsig = `Sort o2 in
        comp_of_sort ~config ~refine ~svmap ~temp ~opsig ~cont:cont2 dom s2
      in
      Eff (x, c1, c2)
    | _ -> failwith @@ sprintf "[comp_of_val] %s not supported" (Term.str_of_cont cont)
  in
  ropsig, val_type, temp_eff, cont_eff
and pure_comp_of_val ~config =
  comp_of_val ~config ~svmap:Map.Poly.empty ~temp:false ~opsig:(`Refined ALMap.empty) ~cont:Sort.Pure []
and comp_of_sort ~config ?(refine=true) ?(svmap=Map.Poly.empty)
    ~temp ~opsig ~cont ?(name=None) dom sort =
  comp_of_val ~config ~svmap ~temp ~opsig ~cont dom @@
  val_of_sort ~config ~refine ~svmap ~name dom sort
and pure_comp_of_sort ~config ?(refine=true) ?(svmap=Map.Poly.empty) ?(name=None) dom sort =
  pure_comp_of_val ~config @@ val_of_sort ~config ~refine ~svmap ~name dom sort

let rec of_args_ret ~config ?(temp=false) ?(opsig=`Refined ALMap.empty) ?(cont=None)
    dom xs args ret =
  match xs, args with
  | [], [] -> assert Stdlib.(cont = None || cont = Some []);
    [], dom, ret
  | x :: xs', arg :: args' ->
    let dom' = let sort = sort_of_val arg in dom @ [Term.mk_var x sort, sort] in
    let cont'', cont' =
      match cont with
      | None -> Sort.Pure, None
      | Some (eff :: effs') -> eff, Some effs'
      | _ -> failwith "of_args_ret"
    in
    let cs, dom'', ret' =
      of_args_ret ~config ~temp ~opsig ~cont:cont' dom' xs' args' ret
    in
    let c = comp_of_val ~config ~temp ~opsig ~cont:cont'' dom ret' in
    c :: cs, dom'', mk_rarrow x arg c @@ mk_fresh_trivial_pred ()
  | _ -> assert false

let rec val_of_term ~config ?(top = true) term = function
  | RGeneral (params, sort, (v, phi)) ->
    mk_rcompound params(*ToDo*) sort @@
    (v, Formula.and_of [Formula.eq (Term.mk_var v sort) term;
                        if top then Formula.mk_true () else phi])
  | RTuple (elems, (v, phi)) ->
    let sorts = List.map elems ~f:sort_of_val in
    let elems = List.mapi elems ~f:(T_tuple.mk_tuple_sel sorts term >>
                                    val_of_term ~config ~top:false) in
    mk_rtuple elems @@
    (v, Formula.and_of [Formula.eq (Term.mk_var v @@ T_tuple.STuple sorts) term;
                        if top then Formula.mk_true () else phi])
  | RRef (elem, pred) -> mk_rref elem pred
  | RArrow (x, t, c, pred) -> mk_rarrow x t c pred
  | RForall (_penv, _constrs, _c) -> failwith "predicate polymorphism not supported"
  | RPoly (_svs, _c) -> failwith "type polymorphism not supported"
let comp_of_term ~config t ty = pure_comp_of_val ~config @@ val_of_term ~config t ty

let mk_val ~config ?(svmap=Map.Poly.empty) sort =
  let params =
    List.map ~f:(simple_val_of_sort ~config ~svmap) @@
    match sort with
    | T_dt.SDT dt -> (Datatype.params_of dt)
    | T_dt.SUS (_name, params) -> params
    | _ -> []
  in
  mk_rcompound params sort

(** Transformation *)

let compose_temp_eff es =
  let fin, infs =
    List.fold_left ~init:(T_sequence.mk_eps (), []) es
      ~f:(fun (s, acc) ((x, _), (y, _)) ->
          T_sequence.mk_concat ~fin:true s @@ Term.mk_var x @@ T_sequence.SSequence true,
          (T_sequence.mk_concat ~fin:false s @@ Term.mk_var y @@ T_sequence.SSequence false) :: acc)
  in
  let x = mk_fresh_tvar_with "fin" in
  let y = mk_fresh_tvar_with "inf" in
  let xs = List.map es ~f:(fun ((x, _), _) -> x(*assume distinct*),
                                              T_sequence.SSequence true) in
  let ys = List.map es ~f:(fun (_, (y, _)) -> y(*assume distinct*),
                                              T_sequence.SSequence false) in
  let fin_senvs, fin_phis =
    List.unzip @@
    List.map es ~f:(fst >> snd >> Formula.aconv_tvar >> Formula.split_exists)
  in
  let inf_senvs, inf_phis =
    List.unzip @@
    List.map es ~f:(snd >> snd >> Formula.aconv_tvar >> Formula.split_exists)
  in
  (x,
   Formula.exists (List.concat @@ xs :: fin_senvs) @@ Formula.and_of @@
   Formula.eq (Term.mk_var x @@ T_sequence.SSequence true) fin :: fin_phis),
  (y,
   Formula.exists (List.concat @@ xs :: ys :: fin_senvs @ inf_senvs) @@ Formula.and_of @@
   (Formula.or_of @@
    List.map2_exn (List.rev infs) inf_phis ~f:(fun inf inf_phi ->
        Formula.and_of [Formula.eq (Term.mk_var y @@ T_sequence.SSequence false) inf;
                        inf_phi])) :: fin_phis)
let rec compose_temp_cont es = function
  | Pure -> Pure
  | Eff (x, c1, c2) -> Eff (x, c1, compose_temp_comp es c2)
and compose_temp_comp es (o, t, e, s) =
  o, t, compose_temp_eff (es @ [e]), compose_temp_cont es s

let rec compose_cont_temp s es = match s with
  | Pure -> Pure
  | Eff (x, c1, c2) -> Eff (x, c1, compose_comp_temp c2 es)
and compose_comp_temp (o, t, e, s) es =
  o, t, compose_temp_eff (e :: es), compose_cont_temp s es

let rec set_sort_temp ~print subst ((x1, phi1), (x2, phi2)) =
  (x1,
   let sub = Map.Poly.set subst ~key:x1 ~data:(Term.mk_var x1 @@ T_sequence.SSequence true) in
   Typeinf.typeinf_formula ~print @@ Formula.subst sub phi1),
  (x2,
   let sub = Map.Poly.set subst ~key:x2 ~data:(Term.mk_var x2 @@ T_sequence.SSequence false) in
   Typeinf.typeinf_formula ~print @@ Formula.subst sub phi2)
and set_sort_cont ~print subst sort = function
  | Pure -> Pure
  | Eff (x, c1, c2) ->
    Eff (x,
         set_sort_comp ~print (Map.Poly.set subst ~key:x ~data:(Term.mk_var x sort)) c1,
         set_sort_comp ~print subst c2)
and set_sort_opsig ~print subst (o : o) : o = ALMap.map o ~f:(set_sort_val ~print subst)
and set_sort_comp ~print subst (o, t, e, s) =
  set_sort_opsig ~print subst o,
  set_sort_val ~print subst t,
  set_sort_temp ~print subst e,
  set_sort_cont ~print subst (sort_of_val t) s
and set_sort_val ~print subst = function
  | RGeneral (params, sort, (x, phi)) ->
    let params = List.map params ~f:(set_sort_val ~print subst) in
    let phi =
      Typeinf.typeinf_formula ~print @@
      Formula.subst (Map.Poly.set subst ~key:x ~data:(Term.mk_var x sort)) phi
    in
    RGeneral (params, sort, (x, phi))
  | RTuple (elems, (x, phi)) as ty ->
    let sort = sort_of_val ty in
    let elems = List.map elems ~f:(set_sort_val ~print subst) in
    let phi =
      Typeinf.typeinf_formula ~print @@
      Formula.subst (Map.Poly.set subst ~key:x ~data:(Term.mk_var x sort)) phi
    in
    RTuple (elems, (x, phi))
  | RRef (elem, (x, phi)) as ty ->
    let sort = sort_of_val ty in
    let elem = set_sort_val ~print subst elem in
    let phi =
      Typeinf.typeinf_formula ~print @@
      Formula.subst (Map.Poly.set subst ~key:x ~data:(Term.mk_var x sort)) phi
    in
    RRef (elem, (x, phi))
  | RArrow (y, t, c, (x, phi)) as ty ->
    let sort = sort_of_val ty in
    let t = set_sort_val ~print subst t in
    let c =
      let subst = Map.Poly.set subst ~key:y ~data:(Term.mk_var y @@ sort_of_val t) in
      set_sort_comp ~print subst c
    in
    let phi =
      Typeinf.typeinf_formula ~print @@
      Formula.subst (Map.Poly.set subst ~key:x ~data:(Term.mk_var x sort)) phi
    in
    RArrow (y, t, c, (x, phi))
  | RForall (penv, phis, c) ->
    let phis = Set.Poly.map phis ~f:(Formula.subst subst >> Typeinf.typeinf_formula ~print) in
    RForall (penv, phis, set_sort_comp ~print subst c)
  | RPoly (svs, c) -> RPoly (svs, set_sort_comp ~print subst c)

(** Substitution *)

let rec subst_temp sub ((x1, phi1), (x2, phi2)) =
  (x1, Formula.subst (Map.Poly.remove sub x1) phi1),
  (x2, Formula.subst (Map.Poly.remove sub x2) phi2)
and subst_cont sub = function
  | Pure -> Pure
  | Eff (x, c1, c2) -> Eff (x, subst_comp (Map.Poly.remove sub x) c1, subst_comp sub c2)
and subst_opsig sub (opsig: o) : o = ALMap.map opsig ~f:(subst_val sub)
and subst_comp sub (o, t, e, s) =
  subst_opsig sub o, subst_val sub t, subst_temp sub e, subst_cont sub s
and subst_val sub = function
  | RGeneral (params, sort, (x, phi)) ->
    RGeneral (List.map params ~f:(subst_val sub), sort,
              (x, Formula.subst (Map.Poly.remove sub x) phi))
  | RTuple (elems, (x, phi)) ->
    RTuple (List.map elems ~f:(subst_val sub),
            (x, Formula.subst (Map.Poly.remove sub x) phi))
  | RRef (elem, (x, phi)) ->
    RRef (subst_val sub elem, (x, Formula.subst (Map.Poly.remove sub x) phi))
  | RArrow (y, t, c, (x, phi)) ->
    RArrow (y, subst_val sub t, subst_comp (Map.Poly.remove sub y) c,
            (x, Formula.subst (Map.Poly.remove sub x) phi))
  | RForall (penv, phis, c) ->
    RForall (penv, Set.Poly.map ~f:(Formula.subst sub) phis, subst_comp sub c)
  | RPoly (svs, c) ->
    RPoly (svs, subst_comp sub c)

let rec subst_preds_temp sub ((x1, phi1), (x2, phi2)) =
  (x1, Formula.subst_preds sub phi1), (x2, Formula.subst_preds sub phi2)
and subst_preds_cont sub = function
  | Pure -> Pure
  | Eff (x, c1, c2) -> Eff (x, subst_preds_comp sub c1, subst_preds_comp sub c2)
and subst_preds_opsig sub = ALMap.map ~f:(subst_preds_val sub)
and subst_preds_comp sub (o, t, e, s) =
  subst_preds_opsig sub o, subst_preds_val sub t,
  subst_preds_temp sub e, subst_preds_cont sub s
and subst_preds_val sub = function
  | RGeneral (params, sort, (x, phi)) ->
    let params = List.map params ~f:(subst_preds_val sub) in
    RGeneral (params, sort, (x, Formula.subst_preds sub phi))
  | RTuple (elems, (x, phi)) ->
    let elems = List.map elems ~f:(subst_preds_val sub) in
    RTuple (elems, (x, Formula.subst_preds sub phi))
  | RRef (elem, (x, phi)) ->
    RRef (subst_preds_val sub elem, (x, Formula.subst_preds sub phi))
  | RArrow (y, t, c, (x, phi)) ->
    let t = subst_preds_val sub t in
    let c = subst_preds_comp sub c in
    RArrow (y, t, c, (x, Formula.subst_preds sub phi))
  | RForall (penv, phis, c) ->
    let sub' = Map.remove_keys sub @@ Map.Poly.keys penv in
    let phis = Set.Poly.map ~f:(Formula.subst_preds sub) phis in
    RForall (penv, phis, subst_preds_comp sub' c)
  | RPoly (svs, c) ->
    RPoly (svs, subst_preds_comp sub c)

let rec subst_sorts_temp map ((x1, phi1), (x2, phi2)) =
  (x1, Formula.subst_sorts map phi1), (x2, Formula.subst_sorts map phi2)
and subst_sorts_cont ~config map = function
  | Pure -> Pure
  | Eff (x, c1, c2) ->
    Eff (x, subst_sorts_comp ~config map c1, subst_sorts_comp ~config map c2)
and subst_sorts_opsig ~config sub = ALMap.map ~f:(subst_sorts_val ~config sub)
and subst_sorts_comp ~config map (o, t, e, s) =
  subst_sorts_opsig ~config map o, subst_sorts_val ~config map t,
  subst_sorts_temp map e, subst_sorts_cont ~config map s
and subst_sorts_val ~config sub = function
  | RGeneral ([], sort, pred) ->
    let sort = Term.subst_sorts_sort sub sort in
    let pred = Formula.subst_sorts_pred sub pred in
    (match sort with
     | T_dt.SDT dt ->
       let sorts = Datatype.params_of dt in
       let params = List.map sorts ~f:(simple_val_of_sort(*ToDo*) ~config) in
       mk_rdt params dt pred
     | T_tuple.STuple sorts ->
       let elems = List.map sorts ~f:(simple_val_of_sort(*ToDo*) ~config) in
       mk_rtuple elems pred
     | T_ref.SRef sort ->
       let elem = simple_val_of_sort(*ToDo*) ~config sort in
       mk_rref elem pred
     | Sort.SArrow (sort1, (opsig2, sort2, cont2)) ->
       mk_rarrow (mk_fresh_tvar ()) (simple_val_of_sort(*ToDo*) ~config sort1)
         (comp_of_val ~config ~opsig:(`Sort opsig2) ~cont:cont2 [] @@
          simple_val_of_sort(*ToDo*) ~config sort2)
         pred
     | Sort.SPoly (_svs, _sort) ->
       failwith "instantiation with a type polymorphic type is not supported"
     | _ -> mk_rbase sort pred)
  | RGeneral (params, T_dt.SDT dt, pred) ->
    let params = List.map params ~f:(subst_sorts_val ~config sub) in
    let dt = Datatype.subst_sorts sub dt in
    let pred = Formula.subst_sorts_pred sub pred in
    mk_rdt params dt pred
  | RTuple (elems, pred) ->
    let elems = List.map elems ~f:(subst_sorts_val ~config sub) in
    let pred = Formula.subst_sorts_pred sub pred in
    mk_rtuple elems pred
  | RRef (elem, pred) ->
    let elem = subst_sorts_val ~config sub elem in
    let pred = Formula.subst_sorts_pred sub pred in
    mk_rref elem pred
  | RArrow (y, t, c, pred) ->
    let t = subst_sorts_val ~config sub t in
    let c = subst_sorts_comp ~config sub c in
    let pred = Formula.subst_sorts_pred sub pred in
    mk_rarrow y t c pred
  | RForall (penv, phis, c) ->
    let penv = Map.Poly.map ~f:(List.map ~f:(Term.subst_sorts_sort sub)) penv in
    let phis = Set.Poly.map ~f:(Formula.subst_sorts sub) phis in
    let c = subst_sorts_comp ~config sub c in
    mk_pred_poly ~config penv phis c
  | RPoly (svs, c) ->
    let sub = Map.remove_keys sub @@ Set.to_list svs in
    let c = subst_sorts_comp ~config sub c in
    mk_type_poly ~config svs c
  | _ -> failwith "subst_sorts_val"

let rename_var map from = match Map.Poly.find map from with Some v -> v | None -> from
let rec rename_temp map ((x1, phi1), (x2, phi2)) =
  (x1, Formula.rename (Map.Poly.remove map x1) phi1),
  (x2, Formula.rename (Map.Poly.remove map x2) phi2)
and rename_cont ~config map = function
  | Pure -> Pure
  | Eff (x, c1, c2) ->
    Eff (x, rename_comp ~config (Map.Poly.remove map x) c1, rename_comp ~config map c2)
and rename_opsig ~config map = ALMap.map ~f:(rename_val ~config map)
and rename_comp ~config map (o, t, e, s) =
  rename_opsig ~config map o, rename_val ~config map t,
  rename_temp map e, rename_cont ~config map s
and rename_val ~config map = function
  | RGeneral (params, sort, (x, phi)) ->
    let params = List.map params ~f:(rename_val ~config map) in
    mk_rcompound params sort (x, Formula.rename (Map.Poly.remove map x) phi)
  | RTuple (elems, (x, phi)) ->
    let elems = List.map elems ~f:(rename_val ~config map) in
    mk_rtuple elems (x, Formula.rename (Map.Poly.remove map x) phi)
  | RRef (elem, (x, phi)) ->
    mk_rref (rename_val ~config map elem)
      (x, Formula.rename (Map.Poly.remove map x) phi)
  | RArrow (y, t, c, (x, phi)) ->
    mk_rarrow y (rename_val ~config map t)
      (rename_comp ~config (Map.Poly.remove map y) c)
      (x, Formula.rename (Map.Poly.remove map x) phi)
  | RForall (penv, phis, c) ->
    mk_pred_poly ~config penv (Set.Poly.map ~f:(Formula.rename map) phis) @@
    rename_comp ~config map c
  | RPoly (svs, c) ->
    mk_type_poly ~config svs (rename_comp ~config map c)

let rec rename_pvars_temp map ((x1, phi1), (x2, phi2)) =
  (x1, Formula.rename_pvars map phi1), (x2, Formula.rename_pvars map phi2)
and rename_pvars_cont map = function
  | Pure -> Pure
  | Eff (x, c1, c2) ->
    Eff (x, rename_pvars_comp map c1, rename_pvars_comp map c2)
and rename_pvars_opsig map = ALMap.map ~f:(rename_pvars_val map)
and rename_pvars_comp map (o, t, e, s) =
  rename_pvars_opsig map o, rename_pvars_val map t,
  rename_pvars_temp map e, rename_pvars_cont map s
and rename_pvars_val map = function
  | RGeneral (params, sort, (x, phi)) ->
    let params = List.map params ~f:(rename_pvars_val map) in
    RGeneral (params, sort, (x, Formula.rename_pvars map phi))
  | RTuple (elems, (x, phi)) ->
    let elems = List.map elems ~f:(rename_pvars_val map) in
    RTuple (elems, (x, Formula.rename_pvars map phi))
  | RRef (elem, (x, phi)) ->
    RRef (rename_pvars_val map elem, (x, Formula.rename_pvars map phi))
  | RArrow (y, t, c, (x, phi)) ->
    RArrow (y, rename_pvars_val map t, rename_pvars_comp map c,
            (x, Formula.rename_pvars map phi))
  | RForall (penv, phis, c) ->
    let map' = Map.remove_keys map (Map.Poly.keys penv) in
    RForall (penv, Set.Poly.map ~f:(Formula.rename_pvars map') phis,
             rename_pvars_comp map' c)
  | RPoly (svs, c) ->
    RPoly (svs, rename_pvars_comp map c)

let rec aconv_temp map (pred1, pred2) =
  aconv_pred ~prefix:"x" map pred1 @@ T_sequence.SSequence true,
  aconv_pred ~prefix:"y" map pred2 @@ T_sequence.SSequence false
and aconv_cont map sort = function
  | Pure -> Pure
  | Eff (x, c1, c2) ->
    let x' = mk_fresh_tvar_with "x" in
    Eff (x', aconv_comp (Map.Poly.set map ~key:x ~data:(Term.mk_var x' sort)) c1,
         aconv_comp map c2)
and aconv_opsig map = ALMap.map ~f:(aconv_val map)
and aconv_comp map (o, t, e, s) =
  aconv_opsig map o, aconv_val map t,
  aconv_temp map e, aconv_cont map (sort_of_val t) s
and aconv_pred ?(prefix = "v") map (x, phi) sort =
  let v = mk_fresh_tvar_with prefix in
  (v, Formula.subst (Map.Poly.set map ~key:x ~data:(Term.mk_var v sort)) phi)
and aconv_val map = function
  | RGeneral (params, sort, pred) ->
    let params = List.map params ~f:(aconv_val map) in
    RGeneral (params, sort, aconv_pred map pred sort)
  | RTuple (elems, pred) as ty ->
    let elems = List.map elems ~f:(aconv_val map) in
    RTuple (elems, aconv_pred map pred @@ sort_of_val ty)
  | RRef (t, pred) as ty ->
    RRef (aconv_val map t, aconv_pred map pred @@ sort_of_val ty)
  | RArrow (x, t, c, pred) as ty ->
    let sort = sort_of_val ty in
    let x' = mk_fresh_tvar_with "x" in
    let map' = Map.Poly.set map ~key:x ~data:(Term.mk_var x' @@ sort_of_val t) in
    RArrow (x', aconv_val map t, aconv_comp map' c, aconv_pred map pred sort)
  | RForall (penv, phis, c) ->
    RForall (penv, Set.Poly.map ~f:(Formula.subst map) phis, aconv_comp map c)
  | RPoly (svs, c) ->
    RPoly (svs, aconv_comp map c)

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
  | RArrow (y, t, c, pred) ->
    let c, map = fresh_eff_pvars_comp ~print c in
    RArrow (y, t, c, pred), map
  | t -> t, Map.Poly.empty

let rec tsub_of_cont ~config sub = function
  | Pure, Sort.Pure -> sub
  | Eff (_, c1, c2), Sort.Eff (o1, s1, cont1, o2, s2, cont2) ->
    let sub' = tsub_of_comp ~config sub (c1, o1, s1, cont1) in
    tsub_of_comp ~config sub' (c2, o2, s2, cont2)
  | s, cont ->
    failwith @@ sprintf "[tsub_of_cont] %s and %s"
      (str_of_cont ~config s) (Term.str_of_cont cont)
and tsub_of_opsig ~config sub = function
  | opsig, Sort.OpSig (opmap, _) ->
    let lefts, boths, _rights = ALMap.split_lbr opsig opmap in
    if List.is_empty lefts (* && List.is_empty rights *) then
      List.fold boths ~init:sub ~f:(fun sub (_op, (t, sort)) ->
          tsub_of_val ~config sub (t, sort))
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
    let sorts = Datatype.params_of dt' in
    (try List.fold2_exn params sorts ~init:sub ~f:(tsub_of_val ~config >> curry2)
     with _ ->
       failwith @@ sprintf "[tsub_of_val] (%s) and (%s)"
         (String.concat_map_list ~sep:"," ~f:(str_of_val ~config) params)
         (String.concat_map_list ~sep:"," ~f:Term.str_of_sort sorts))
  | RGeneral (params, T_dt.SUS (name, _), _), T_dt.SDT dt'
    when String.(name = Datatype.name_of dt') ->
    let sorts = Datatype.params_of dt' in
    (try List.fold2_exn params sorts ~init:sub ~f:(tsub_of_val ~config >> curry2)
     with _ ->
       failwith @@ sprintf "[tsub_of_val] (%s) and (%s)"
         (String.concat_map_list ~sep:"," ~f:(str_of_val ~config) params)
         (String.concat_map_list ~sep:"," ~f:Term.str_of_sort sorts))
  | RTuple (elems, _), T_tuple.STuple sorts ->
    List.fold2_exn elems sorts ~init:sub ~f:(tsub_of_val ~config >> curry2)
  | RRef (elem, _), T_ref.SRef sort ->
    tsub_of_val ~config sub (elem, sort)
  | RArrow ((*assume fresh*)_, t, c, _), Sort.SArrow (sort1, (opsig, sort2, cont)) ->
    tsub_of_comp ~config (tsub_of_val ~config sub (t, sort1)) (c, opsig, sort2, cont)
  | RForall (_penv, _phis, c), sort' ->
    tsub_of_comp ~config sub (c, Sort.mk_fresh_empty_open_opsig (), sort', Sort.Pure)
  | RPoly (svs1, c), Sort.SPoly (svs2, sort) (*ToDo: remove this*)
    when Fn.non Set.is_empty @@ Set.inter svs1 svs2 ->
    tsub_of_val ~config sub
      (mk_type_poly ~config (Set.diff svs1 svs2) c,
       Sort.mk_poly (Set.diff svs2 svs1) sort)
  | RPoly (svs, c), sort' ->
    assert (Set.is_empty @@ Set.inter svs @@ Map.key_set sub);
    let sub' = tsub_of_comp ~config sub (c, Sort.mk_fresh_empty_open_opsig (), sort', Sort.Pure) in
    Map.remove_keys sub' @@ Set.to_list svs
  | ty, sort ->
    failwith @@ sprintf "cannot instantiate %s with %s"
      (str_of_val ty ~config) (Term.str_of_sort sort)

let update_svmap_with_sub ~config dom svmap sub =
  Map.force_merge svmap @@ Map.Poly.filter_mapi sub ~f:(fun ~key ~data ->
      if Map.Poly.mem svmap key then None(*ToDo: should fail?*)
      else
        let refine = true(*not config.gen_ref_pred_for_type_vars(*ToDo*)*) in
        let svmap = Map.Poly.empty(*ToDo*) in
        Option.some @@ val_of_sort ~config ~refine ~svmap dom data)
let rec instantiate_cont ~print ~config dom (sub, svmap) sort = function
  | Pure, Sort.Pure ->
    Pure, Set.Poly.empty
  | Eff (x, c1, c2), Sort.Eff (o1, s1, e1, o2, s2, e2) ->
    let dom' = dom @ [Term.mk_var x sort, sort] in
    let c1, cs1 = instantiate_comp ~print ~config dom' (sub, svmap) (c1, (o1, s1, e1)) in
    let c2, cs2 = instantiate_comp ~print ~config dom (sub, svmap) (c2, (o2, s2, e2)) in
    Eff (x, c1, c2), Set.union cs1 cs2
  | Eff (x, c1, c2), Sort.Pure -> Eff (x, c1, c2), Set.Poly.empty
  | s, cont ->
    failwith @@ sprintf "[instantiate_cont] %s and %s"
      (str_of_cont ~config s) (Term.str_of_cont cont)
and instantiate_opsig ~print ~config dom (sub, svmap) (o, opsig) =
  match opsig with
  | Sort.OpSig (opsig, _(*ToDo*)) ->
    let cs = ref Set.Poly.empty in
    let o =
      ALMap.mapi o ~f:(fun s t ->
          let t, constrs =
            instantiate_val ~print ~config dom (sub, svmap) (t, ALMap.find_exn s opsig)
          in
          cs := Set.union !cs constrs;
          t)
    in
    o, !cs
  | _ -> failwith "[instantiate_opsig]"
and instantiate_comp ~print ~config dom (sub, svmap) ((o, t, e, s), (opsig, sort, cont)) =
  let o, constrs1 = instantiate_opsig ~print ~config dom (sub, svmap) (o, opsig) in
  let t, constrs2 = instantiate_val ~print ~config dom (sub, svmap) (t, sort) in
  let s, constrs3 = instantiate_cont ~print ~config dom (sub, svmap) (sort_of_val t) (s, cont) in
  (o, t, subst_sorts_temp sub e, s),
  Set.Poly.union_list [constrs1; constrs2; constrs3]
and instantiate_val ~print ~config dom (sub, svmap) = function
  | RGeneral ([], sort, pred), sort' ->
    let sort_inst = Term.subst_sorts_sort sub sort in
    let pred = Formula.subst_sorts_pred sub pred in
    if Stdlib.(sort_inst <> sort') && not (eq_dt sort_inst sort') then
      failwith @@ sprintf "[instantiate_val] %s and %s does not match"
        (Term.str_of_sort sort_inst) (Term.str_of_sort sort');
    (match sort with
     | Sort.SVar svar when Map.Poly.mem svmap svar ->
       conj_pred_val pred (Map.Poly.find_exn svmap svar), Set.Poly.empty
     | Sort.SPoly (_svs, _sort) ->
       failwith "instantiation with a type polymorphic type is not supported"
     | _ -> mk_rbase sort pred, Set.Poly.empty)
  | RGeneral (params, T_dt.SDT dt, pred), T_dt.SDT dt'
    when String.(dt.name = dt'.name) ->
    let dt = Datatype.subst_sorts sub dt in
    let pred = Formula.subst_sorts_pred sub pred in
    (*print_endline @@ Datatype.str_of dt ^ " and " ^ Datatype.str_of dt';*)
    let params, constrss =
      List.unzip @@ List.map2_exn params (Datatype.params_of dt')
        ~f:(curry @@ instantiate_val ~print ~config dom (sub, svmap))
    in
    mk_rdt params dt pred, Set.Poly.union_list constrss
  | RGeneral (params, T_dt.SUS (name, _), pred), T_dt.SDT dt'
    when String.(name = dt'.name) ->
    let pred = Formula.subst_sorts_pred sub pred in
    let params, constrss =
      List.unzip @@ List.map2_exn params (Datatype.params_of dt')
        ~f:(curry @@ instantiate_val ~print ~config dom (sub, svmap))
    in
    mk_rdt params dt' pred, Set.Poly.union_list constrss
  | RGeneral (params, T_dt.SUS (name, _), pred), T_dt.SUS (name', sorts)
    when String.(name = name') ->
    let pred = Formula.subst_sorts_pred sub pred in
    let params, constrss =
      List.unzip @@ List.map2_exn params sorts
        ~f:(curry @@ instantiate_val ~print ~config dom (sub, svmap))
    in
    mk_rus params name' sorts pred, Set.Poly.union_list constrss
  | RTuple (elems, pred), T_tuple.STuple sorts ->
    let pred = Formula.subst_sorts_pred sub pred in
    let elems, constrss =
      List.unzip @@ List.map2_exn elems sorts
        ~f:(curry @@ instantiate_val ~print ~config dom (sub, svmap))
    in
    mk_rtuple elems pred, Set.Poly.union_list constrss
  | RRef (elem, pred), T_ref.SRef sort ->
    let pred = Formula.subst_sorts_pred sub pred in
    let elem, constrs = instantiate_val ~print ~config dom (sub, svmap) (elem, sort) in
    mk_rref elem pred, constrs
  | RArrow (x, t, c, pred), Sort.SArrow (sort1, full_sort2) ->
    (*assume [full_sort2] matches with c*)
    let pred = Formula.subst_sorts_pred sub pred in
    let t, constrs1 = instantiate_val ~print ~config dom (sub, svmap) (t, sort1) in
    let dom' = dom @ [Term.mk_var x sort1, sort1] in
    let c, constrs2 = instantiate_comp ~print ~config dom' (sub, svmap) (c, full_sort2) in
    mk_rarrow x t c pred, Set.union constrs1 constrs2
  | RForall (penv, constrs, c) as ty0, sort ->
    if ALMap.is_empty (opsig_of_comp c) &&
       (not config.enable_temp_eff || is_pure_temp (temp_of_comp c)) &&
       is_pure_cont (cont_of_comp c) then begin
      print @@ lazy
        (sprintf "instantiate %s with %s"
           (str_of_val ~config ty0) (Term.str_of_sort sort));
      let penv = Map.Poly.map penv ~f:(List.map ~f:(Term.subst_sorts_sort sub)) in
      let constrs = Set.Poly.map constrs ~f:(Formula.subst_sorts sub) in
      let t, constrs' =
        instantiate_val ~print ~config dom (sub, svmap) (val_of_comp c, sort)
      in
      let pmap =
        Map.Poly.mapi penv ~f:(fun ~key ~data ->
            ignore data;
            Ident.mk_fresh_pvar ()
              ~prefix:(Some (Ident.name_of_pvar key
                             (*^ "[" ^ Term.str_of_sort(* ToDo *) sort ^ "]"*) ^ "@")))
      in
      let constrs'', t' =
        Set.Poly.map ~f:(Formula.rename_pvars pmap) @@ Set.union constrs constrs',
        rename_pvars_val pmap t
      in
      print @@ lazy
        (sprintf "pvars instantiated type: %s\nconstraints: %s"
           (str_of_val ~config t')
           (Formula.str_of @@ Formula.and_of @@ Set.to_list constrs''));
      t', constrs''
    end else failwith "not supported"
  | RPoly (svs1, c), Sort.SPoly (svs2, sort) (*ToDo: remove this*)
    when Fn.non Set.is_empty @@ Set.inter svs1 svs2 ->
    instantiate_val ~print ~config dom (sub, svmap)
      (mk_type_poly ~config (Set.diff svs1 svs2) c,
       Sort.mk_poly (Set.diff svs2 svs1) sort)
  | RPoly (svs, c) as ty0, sort0 ->
    if ALMap.is_empty (opsig_of_comp c) &&
       (not config.enable_temp_eff || is_pure_temp (temp_of_comp c)) &&
       is_pure_cont (cont_of_comp c) then begin
      print @@ lazy (sprintf "instantiate %s with %s"
                       (str_of_val ~config ty0) (Term.str_of_sort sort0));
      let t, constrs =
        let t = val_of_comp c in
        let sub' =
          Map.Poly.filter_keys ~f:(Set.mem svs) @@
          tsub_of_val ~config sub (t, sort0)
        in
        (*print_endline @@ str_of_sort_subst Term.str_of_sort sub';*)
        let svmap' = update_svmap_with_sub ~config dom svmap sub' in
        instantiate_val ~print ~config dom (sub', svmap') (t, sort0)
      in
      print @@ lazy
        (sprintf "svars instantiated type: %s\nconstraints: %s"
           (str_of_val ~config t)
           (Formula.str_of @@ Formula.and_of @@ Set.to_list constrs));
      t, constrs
    end else failwith "not supported"
  | ty0, sort0 ->
    failwith @@ sprintf "cannot instantiate %s with %s"
      (str_of_val ty0 ~config) (Term.str_of_sort sort0)

(** Refinement type environments *)
module Env = struct
  type t = env
  let mk_empty (): t = Map.Poly.empty, Set.Poly.empty
  let to_sort_env (senv, _phis) = Map.Poly.map senv ~f:sort_of_val
  let of_list l = Map.of_list_exn l, Set.Poly.empty
  let add_phi (senv, phis) phi: t = senv, Set.add phis phi
  let add_phis (senv, phis1) phis2: t = senv, Set.union phis1 phis2
  let set_ty (senv, phis) tvar ty: t = Map.Poly.set senv ~key:tvar ~data:ty, phis
  let remove (senv, phis) tvar = Map.Poly.remove senv tvar, phis
  let look_up (senv, _) tvar = Map.Poly.find senv tvar
  let look_up_exn (senv, _) tvar = Map.Poly.find_exn senv tvar
  let disj_union (senv1, phis1) (senv2, phis2) : t =
    try Map.force_merge senv1 senv2, Set.union phis1 phis2
    with _ -> failwith @@
      "duplicate definition: " ^
      String.concat_set ~sep:"," @@ Set.Poly.map ~f:Ident.name_of_tvar @@
      Set.inter
        (Set.Poly.of_list @@ Map.Poly.keys senv1)
        (Set.Poly.of_list @@ Map.Poly.keys senv2)
  let disj_union_list = List.fold ~init:(mk_empty ()) ~f:disj_union
  let set_with (senv1, phis1) (senv2, phis2) =
    Map.force_merge (Map.Poly.filter_keys senv1 ~f:(Fn.non @@ Map.Poly.mem senv2)) senv2,
    Set.union phis1 phis2
  let rename ~config map (senv, phis) =
    Map.Poly.map senv ~f:(rename_val ~config map),
    Set.Poly.map ~f:(Formula.rename map) phis
  let rename_bound_vars ~config map (senv, phis) =
    Map.rename_keys ~f:(Map.Poly.find map) @@
    Map.Poly.map senv ~f:(rename_val ~config map),
    Set.Poly.map ~f:(Formula.rename map) phis
  let update_with ~config (senv1, phis1) (senv2, phis2) =
    let shared =
      Set.inter
        (Set.Poly.of_list @@ Map.Poly.keys senv1)
        (Set.Poly.of_list @@ Map.Poly.keys senv2)
    in
    (* variables in senv1 that are masked by senv2 are renamed *)
    let map =
      Map.of_set_exn @@ Set.Poly.map shared ~f:(fun x -> x, Ident.mk_fresh_tvar ())
    in
    let senv1 = Map.rename_keys senv1 ~f:(Map.Poly.find map) in
    let senv1, phis1 = rename ~config map (senv1, phis1) in
    let senv2, phis2 = rename ~config map (senv2, phis2) in
    (Map.force_merge senv1 senv2, Set.union phis1 phis2), map
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
    List.map ~f:Formula.str_of @@ Set.to_list phis

  let svs_of (senv, phis) =
    Set.union (Set.concat_map phis ~f:Formula.svs_of)
      (Set.Poly.union_list @@ Map.Poly.data @@
       Map.Poly.map senv ~f:(fun t -> Term.svs_of_sort @@ sort_of_val t))

  let pure_formula_of (_, phis) = phis |> Set.to_list |> Formula.and_of

  let pred_sort_env_of ?(bpvs = Set.Poly.empty) (renv, phis) =
    let pred_senv =
      Map.Poly.fold renv ~init:Set.Poly.empty ~f:(fun ~key:_ ~data acc ->
          Set.union acc @@ pred_sort_env_of_val ~bpvs data)
    in
    let pred_senv =
      Set.fold phis ~init:pred_senv
        ~f:(fun acc phi -> Set.union acc @@ Formula.pred_sort_env_of ~bpvs phi)
    in
    try Map.of_set_exn pred_senv with _ ->
      failwith @@ String.concat_set ~sep:"\n" @@
      Set.Poly.map pred_senv ~f:(fun (pvar, sorts) ->
          Ident.name_of_pvar pvar ^ ": (" ^
          (String.concat_map_list ~sep:"," sorts ~f:Term.str_of_sort) ^ ")")
  let pvs_of (renv, phis) =
    Set.Poly.union_list @@
    List.map (Map.Poly.data renv) ~f:pvs_of_val @
    Set.to_list @@ Set.Poly.map phis ~f:Formula.pvs_of
end

let of_fsym ~print ~config fsym sort =
  let args_sorts, ret_sort = Sort.args_ret_of sort in
  let rec inner ts sorts =
    match sorts with
    | [] ->
      mk_val ~config ret_sort @@
      let v = mk_fresh_tvar_with "v" in
      v, Formula.eq (Term.mk_var v ret_sort) @@ Term.mk_fsym_app fsym @@ List.rev ts
    | s :: tl ->
      let x = mk_fresh_tvar_with "x" in
      mk_rarrow x (simple_val_of_sort ~config s)
        (pure_comp_of_val ~config @@ inner (Term.mk_var x s :: ts) tl) @@
      mk_fresh_trivial_pred ()
  in
  let res = inner [] args_sorts in
  print @@ lazy (sprintf "[Rtype.of_fsym] %s : %s"
                   (Term.str_of_funsym fsym) (str_of_val ~config res));
  res
let of_psym ~print ~config psym sort =
  let args_sorts, ret_sort = Sort.args_ret_of sort in
  assert (Term.is_bool_sort ret_sort);
  let rec inner ts sorts =
    match sorts with
    | [] ->
      mk_val ~config ret_sort @@
      let v = Ident.mk_fresh_tvar () in
      v, Formula.eq (Term.mk_var v T_bool.SBool) @@
      T_bool.of_atom @@ Atom.mk_psym_app psym @@ List.rev ts
    | s :: tl ->
      let x = mk_fresh_tvar_with "x" in
      mk_rarrow x (simple_val_of_sort ~config s)
        (pure_comp_of_val ~config @@ inner (Term.mk_var x s :: ts) tl) @@
      mk_fresh_trivial_pred ()
  in
  let res = inner [] args_sorts in
  print @@ lazy (sprintf "[Rtype.of_psym] %s : %s"
                   (Predicate.str_of_psym psym) (str_of_val ~config res));
  res
let of_unop ~config = function
  | Formula.Not ->
    let x = mk_fresh_tvar_with "x" in
    let r = mk_fresh_tvar_with "r" in
    mk_rarrow x (mk_rbase T_bool.SBool @@ mk_fresh_trivial_pred ())
      (pure_comp_of_val ~config @@ mk_rbase T_bool.SBool @@
       (r, Formula.neq (Term.mk_var r T_bool.SBool) (Term.mk_var x T_bool.SBool))) @@
    mk_fresh_trivial_pred ()
let of_binop ~config = function
  | Formula.And ->
    let rec inner ts sorts =
      match sorts with
      | [] ->
        mk_rbase T_bool.SBool @@
        let v = Ident.mk_fresh_tvar () in
        v, Formula.eq (Term.mk_var v T_bool.SBool) @@
        T_bool.of_formula @@ Formula.and_of @@ List.map ts ~f:Formula.of_bool_term
      | s :: tl ->
        let x = mk_fresh_tvar_with "x" in
        mk_rarrow x (mk_val ~config s @@ mk_fresh_trivial_pred ())
          (pure_comp_of_val ~config @@ inner (Term.mk_var x s :: ts) tl) @@
        mk_fresh_trivial_pred ()
    in
    inner [] [T_bool.SBool; T_bool.SBool]
  | Formula.Or ->
    let rec inner ts sorts =
      match sorts with
      | [] ->
        mk_rbase T_bool.SBool @@
        let v = Ident.mk_fresh_tvar () in
        v, Formula.eq (Term.mk_var v T_bool.SBool) @@
        T_bool.of_formula @@ Formula.or_of @@ List.map ts ~f:Formula.of_bool_term
      | s :: tl ->
        let x = mk_fresh_tvar_with "x" in
        mk_rarrow x (mk_val ~config s @@ mk_fresh_trivial_pred ())
          (pure_comp_of_val ~config @@ inner (Term.mk_var x s :: ts) tl) @@
        mk_fresh_trivial_pred ()
    in
    inner [] [T_bool.SBool; T_bool.SBool]
  | Imply | Iff | Xor -> failwith "unsupported bop"

let is_fsym = function
  | "Stdlib.+" | "Stdlib.-" | "Stdlib.*" | "Stdlib./"
  | "Stdlib.+." | "Stdlib.-." | "Stdlib.*." | "Stdlib./."
  | "Stdlib.~-" | "Stdlib.ref" | "Stdlib.!" | "Stdlib.:=" -> true
  | _ -> false
let is_psym = function
  | "Stdlib.>" | "Stdlib.<" | "Stdlib.>=" | "Stdlib.<="
  | "Stdlib.=" | "Stdlib.==" | "Stdlib.<>" | "Stdlib.!=" -> true
  | _ -> false
let is_unop = function "Stdlib.not" -> true | _ -> false
let is_binop = function
  | "Stdlib.&&" | "Stdlib.&" | "Stdlib.||" | "Stdlib.or" -> true
  | _ -> false
let fsym_of_str sort = function
  | "Stdlib.+" -> T_int.Add
  | "Stdlib.-" -> T_int.Sub
  | "Stdlib.*" -> T_int.Mult
  | "Stdlib./" -> T_int.Div
  | "Stdlib.+." -> T_real.RAdd
  | "Stdlib.-." -> T_real.RSub
  | "Stdlib.*." -> T_real.RMult
  | "Stdlib./." -> T_real.RDiv
  | "Stdlib.~-" -> T_int.Neg
  | "Stdlib.ref" -> T_ref.Ref sort
  | "Stdlib.!" ->
    T_ref.Deref (match sort with T_ref.SRef sort -> sort | _ ->
        failwith @@ sprintf "Stdlib.! in fsym_of_str: %s" (Term.str_of_sort sort))
  | "Stdlib.:=" ->
    T_ref.Update (match sort with T_ref.SRef sort -> sort | _ ->
        failwith @@ sprintf "Stdlib.:= in fsym_of_str: %s" (Term.str_of_sort sort))
  | s -> failwith @@ "unknown fsym: " ^ s
let psym_of_str sort = function
  | "Stdlib.>" ->
    (match sort with T_int.SInt -> T_int.Gt | T_real.SReal -> T_real.RGt | _ -> T_num.NGt (mk_fresh_svar ()))
  | "Stdlib.<" ->
    (match sort with T_int.SInt -> T_int.Lt | T_real.SReal -> T_real.RLt | _ -> T_num.NLt (mk_fresh_svar ()))
  | "Stdlib.>=" ->
    (match sort with T_int.SInt -> T_int.Geq | T_real.SReal -> T_real.RGeq | _ -> T_num.NGeq (mk_fresh_svar ()))
  | "Stdlib.<=" ->
    (match sort with T_int.SInt -> T_int.Leq | T_real.SReal -> T_real.RLeq | _ -> T_num.NLeq (mk_fresh_svar ()))
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
  let sort = Term.sort_of term in
  if Term.is_var term then
    let (tvar, sort), _ = Term.let_var term in
    let name = Ident.name_of_tvar tvar in
    if is_fsym name then
      of_fsym ~print ~config (fsym_of_str (List.hd_exn @@ Sort.args_of sort) name) sort
    else if is_psym name then
      of_psym ~print ~config (psym_of_str (List.hd_exn @@ Sort.args_of sort) name) sort
    else if is_unop name then
      of_unop ~config (unop_of_str name)
    else if is_binop name then
      of_binop ~config (binop_of_str name)
    else
      mk_val ~config sort @@
      let v =  mk_fresh_tvar_with "v" in v, Formula.eq (Term.mk_var v sort) term
  else
    mk_val ~config sort @@
    let v =  mk_fresh_tvar_with "v" in v, Formula.eq (Term.mk_var v sort) term

let renv_ref = ref (Env.mk_empty ())
let cgen_config = ref {
    depend_on_func_args = false;
    depend_on_ref_args = false;
    depend_on_unit_args = false;
    gen_ref_pred_for_type_vars = false;
    share_ref_pred_with_same_type_vars = false;
    gen_ref_pred_for_fun_types = false;
    gen_ref_pred_for_ref_types = false;
    gen_ref_pred_for_tup_elems = false;
    gen_ref_pred_for_dt_params = true;
    gen_ref_type_temp_for_constructors = false;
    never_fail = false;
    can_fail_only_at_total_apps = false;
    can_cause_temp_eff_only_at_total_apps = false;
    enable_temp_eff = false;
    enable_pred_poly_for_constructors = false;
    enable_pred_poly_for_ref_types = false;
    instantiate_svars_to_int = false;
  }
