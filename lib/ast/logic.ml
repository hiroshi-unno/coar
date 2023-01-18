open Core
open Common.Ext
open Common.Util

module Sort = struct
  type t = .. and e = .. and o = ..
  type t += SVar of Ident.svar | SArrow of t * (o *t * e) | SForAll of Ident.svar * t
  type e += EVar of Ident.evar | Pure | Eff of o * t * e * o * t * e
  type o += OpSig of (string, t) ALMap.t * Ident.rvar option (* Some r: open / None: closed *)

  let empty_closed_opsig = OpSig (ALMap.empty, None)
  let is_empty_closed_opsig = function
    | OpSig (map, None) -> ALMap.is_empty map
    | _ -> false
  let is_empty_opsig = function
    | OpSig (map, _) -> ALMap.is_empty map
    | _ -> false

  let mk_arrow s1 s2 = SArrow (s1, (empty_closed_opsig, s2, Pure))
  let rec mk_fun = function
    | [s] -> s
    | s :: ss -> mk_arrow s (mk_fun ss)
    | _ -> assert false
  let mk_forall v sort = SForAll (v, sort)

  let is_arrow = function SArrow _ -> true | _ -> false
  let rec arity_of = function
    | SVar _ -> assert false
    | SArrow (_s1, (_, s2, _)) -> 1 + arity_of s2
    | SForAll (_, s) -> arity_of s
    | _ -> 0 (* assert false*)
  let rec ret_of = function
    | SArrow (_s1, (_, s2, _)) -> ret_of s2
    | sort -> sort
  let rec args_of = function
    | SArrow (s1, (_, s2, _)) -> s1 :: args_of s2
    | _ -> []
  let rec args_ret_of = function
    | SArrow (s1, (_, s2, _)) ->
      let args, ret = args_ret_of s2 in
      s1 :: args, ret
    | s -> [], s
end

type sort_bind = Ident.tvar * Sort.t
type sort_env_set = sort_bind Set.Poly.t
type sort_env_list = sort_bind list
type sort_env_map = (Ident.tvar, Sort.t) Map.Poly.t

let mk_fresh_sort_env_list sorts : sort_env_list =
  List.map sorts ~f:(fun s -> Ident.mk_fresh_tvar (), s)

let str_of_sort_env_list str_of_sort senv =
  String.concat_map_list ~sep:", " senv ~f:(fun (tvar, sort) ->
      Printf.sprintf "%s: %s" (Ident.name_of_tvar tvar) (str_of_sort sort))
let str_of_sort_env_map str_of_sort senv =
  String.concat_map_list ~sep:" " (Map.Poly.to_alist senv) ~f:(fun (tvar, sort) ->
      Printf.sprintf "(%s: %s)" (Ident.name_of_tvar tvar) (str_of_sort sort))
let str_of_term_subst str_of_term subst =
  String.concat_map_list ~sep:"\n" (Map.Poly.to_alist subst) ~f:(fun (tvar, term) ->
      Printf.sprintf "%s |-> %s" (Ident.name_of_tvar tvar) (str_of_term term))

let of_old_sort_env_list of_old_sort = List.map ~f:(fun (x, s) -> x, of_old_sort s)
let of_old_sort_env_map of_old_sort = Map.Poly.map ~f:of_old_sort
let to_old_sort_env_list to_old_sort = List.map ~f:(fun (x, s) -> x, to_old_sort s)
let to_old_sort_env_map to_old_sort = Map.Poly.map ~f:to_old_sort

let to_old_dummies to_old_sort =
  Map.Poly.map ~f:(fun s -> LogicOld.Term.mk_dummy (to_old_sort s))

(*
module SortMap = struct
  type t = sort_env

  let empty = Set.Poly.empty
  let merge senv1 senv2 =
    let xs = Set.Poly.union (Set.Poly.map ~f:fst senv1) (Set.Poly.map ~f:fst senv2) in
    Set.Poly.map xs ~f:(fun x ->
        match Set.Poly.find senv1 ~f:(fun (y, _) -> Stdlib.(x = y)),
              Set.Poly.find senv2 ~f:(fun (y, _) -> Stdlib.(x = y)) with
        | Some (_, s1), Some (_, s2) -> if Stdlib.(s1 = s2) then x, s1 else assert false
        | Some (_, s), None | None, Some (_, s) -> x, s
        | None, None -> assert false)

  let merge_list = function
    | [] -> Set.Poly.empty
    | senv :: senvs' -> List.fold ~init:senv senvs' ~f:merge

  let is_empty = Set.Poly.is_empty
  let mem senv x = Set.Poly.exists senv ~f:(fun (y, _) -> Stdlib.(x = y))
  let remove senv x = Set.Poly.filter senv ~f:(fun (y, _) -> Stdlib.(x <> y))
  let singleton x s = Set.Poly.singleton (x, s)

  let length = Set.Poly.length
  let find senv x = Set.Poly.find_map senv ~f:(fun (y, s) -> if Stdlib.(x = y) then Some s else None)
  let find_exn senv x = snd @@ Set.Poly.find_exn senv ~f:(fun (y, _) -> Stdlib.(x = y))
  let add_exn senv ~key ~data =
    match find senv key with
    | None -> Set.Poly.add senv (key, data)
    | Some _ -> failwith "add_exn"
  let update senv x ~f =
    match find senv x with
    | None -> Set.Poly.add senv (x, f None)
    | Some s -> Set.Poly.map senv ~f:(fun (y, s') -> if Stdlib.(x = y) then y, f (Some s) else y, s')

  let of_alist_exn = List.fold ~init:empty ~f:(fun senv (x, s) -> add_exn senv ~key:x ~data:s)
  let to_alist = Set.Poly.to_list
  let of_set senv = senv
  let to_set senv = senv
  let key_set = Set.Poly.map ~f:fst
  let keys senv = Set.Poly.to_list @@ key_set senv

  let map senv ~f = Set.Poly.map senv ~f:(fun (x, s) -> x, f s)
  let mapi senv ~f = Set.Poly.map senv ~f:(fun (x, s) -> x, f ~key:x ~data:s)
  let filter_mapi senv ~f = Set.Poly.filter_map senv ~f:(fun (x, s) -> match f ~key:x ~data:s with None -> None | Some s -> Some (x, s))
  let rename_keys rename_map map =
    Set.Poly.fold map ~init:Set.Poly.empty ~f:(fun acc (key, data) ->
        match Map.Poly.find rename_map key with
        | None -> add_exn acc ~key ~data
        | Some key' -> add_exn acc ~key:key' ~data)
  let filter_keys ~f senv = Set.Poly.filter senv ~f:(fun (x, _) -> f x)
end
*)

type sym = ..

type termlit = ..
type termlit += FunLit of (termlit -> termlit) | SFunLit of (Sort.t -> termlit)

type info = ..
type info += Dummy
(*type info += ID of int*)

type binder = Mu | Nu | Lambda | Forall | Exists

type term =
  | Var of Ident.tvar * info
  | Con of sym * info
  | App of term * term * info
  | Bin of binder * Ident.tvar * Sort.t * term * info
  | Let of Ident.tvar * Sort.t * term * term * info
  | TyApp of term * Sort.t * info
  | TyLam of Ident.svar * term * info

type term_bind = Ident.tvar * term
type term_subst_set = term_bind Set.Poly.t
type term_subst_list = term_bind list
type term_subst_map = (Ident.tvar, term) Map.Poly.t
type pred_subst_set = (sort_bind * term) Set.Poly.t
type pred_subst_list = (sort_bind * term) list
type pred_subst_map = (sort_bind, term) Map.Poly.t

type model_elem = sort_bind * term option
type model = model_elem list

module type TermType = sig
  (** Construction *)
  val mk_var: Ident.tvar -> term
  val mk_con: sym -> term
  val mk_app: term -> term -> term
  val mk_apps: term -> term list -> term
  val mk_sym_app: sym -> term list -> term
  val mk_var_app: Ident.tvar -> term list -> term
  val mk_bind: binder -> Ident.tvar -> Sort.t -> term -> term
  val mk_binds: binder -> sort_env_list -> term -> term
  val mk_let: Ident.tvar -> Sort.t -> term -> term -> term
  val mk_tyapp: term -> Sort.t -> term
  val mk_tylam: Ident.svar -> term -> term
  val mk_lambda: sort_env_list -> term -> term

  (** Observation *)
  val is_var: term -> bool
  val is_con: term -> bool
  val is_app: term -> bool
  val is_lam: term -> bool
  val is_bin: term -> bool
  val is_let: term -> bool
  val is_tyapp: term -> bool
  val is_tylam: term -> bool

  (** Destruction *)
  val let_var: term -> Ident.tvar * info
  val let_con: term -> sym * info
  val let_app: term -> term * term * info
  val let_apps: term -> term * term list
  val let_sym_app: term -> sym * term list
  val let_var_app: term -> Ident.tvar * term list
  val let_bin: term -> binder * Ident.tvar * Sort.t * term * info
  val let_let: term -> Ident.tvar * Sort.t * term * term * info
  val let_tyapp: term -> term * Sort.t * info
  val let_tylam: term -> Ident.svar * term * info
  val let_lam: term -> sort_env_list * term

  val svs_of: (sym -> Ident.svar Set.Poly.t) -> (Sort.t -> Ident.svar Set.Poly.t) ->
    term -> Ident.svar Set.Poly.t
  val fvs_of: term -> Ident.tvar Set.Poly.t
  val pvar_of_atom: term -> Ident.tvar
  val ast_size: term -> int

  (** Sorts *)
  val open_arity_of_sym: (sym -> Sort.t) -> sym -> int
  val open_sort_of: (sym -> Sort.t) -> (Ident.svar * Sort.t -> Sort.t -> Sort.t) -> sort_env_map -> term -> Sort.t

  val sym_sort_map: (sym, Sort.t) Map.Poly.t
  val arity_of_sym: sym -> int
  val sort_of_sym: sym -> Sort.t

  (** Substitution *)
  val rename: Ident.tvar_map -> term -> term
  val subst: term_subst_map -> term -> term
  val beta_reduction: term -> term list -> term
  val refresh: sort_env_map * term -> sort_env_map * term
  val unify: term -> term -> term_subst_map option

  (** Transformation *)
  val reduce_sort_map: sort_env_map * term -> sort_env_map * term

  (** Printing *)
  val open_str_of_sort: (Sort.t -> string) -> Sort.t -> string
  val open_str_of: (Sort.t -> string) -> (sym -> string) -> term -> string

  val str_of_sym: sym -> string
  val str_of_termlit: termlit -> string
  val str_of_sort: Sort.t -> string
  val str_of: term -> string

  (** Evaluation *)
  val open_assert_sort_check: (Sort.t -> termlit -> unit) -> Sort.t -> termlit -> unit
  val open_eval: (sym -> termlit) -> (termlit -> term) -> (sym, Sort.t) Map.Poly.t -> term -> termlit

  val is_termlit: termlit -> bool
  val of_termlit: termlit -> term
  val assert_sort_check: Sort.t -> termlit -> unit
  val eval_sym: sym -> termlit
  val eval: (sym, Sort.t) Map.Poly.t -> term -> termlit

  val let_sort_env_of : term -> (Ident.tvar, Sort.t, Comparator.Poly.comparator_witness) Map.Poly.map
  val let_env_of : ?map:term_subst_map -> term -> term_subst_map
end

module Term : TermType = struct
  (** Construction *)
  let info_id_count = ref 0
  (*let get_info_id () = incr info_id_count; !info_id_count*)
  let mk_var var =
    incr info_id_count;
    Var (var, Dummy(*ID (get_info_id ())*))
  let mk_con sym =
    incr info_id_count;
    Con (sym, Dummy(*ID (get_info_id ())*))
  let mk_app t1 t2 =
    incr info_id_count;
    App (t1, t2, Dummy(*ID (get_info_id ())*))
  let mk_apps t ts = List.fold ~f:mk_app ~init:t ts
  let mk_sym_app sym args = mk_apps (mk_con sym) args
  let mk_var_app var args = mk_apps (mk_var var) args

  let mk_bind bind var sort term =
    incr info_id_count;
    Bin (bind, var, sort, term, Dummy(*ID (get_info_id ())*))
  let mk_let var sort t1 t2 =
    incr info_id_count;
    Let (var, sort, t1, t2, Dummy(*ID (get_info_id ())*))
  let mk_tyapp term sort =
    incr info_id_count;
    TyApp (term, sort, Dummy(*ID (get_info_id ())*))
  let mk_tylam svar term =
    incr info_id_count;
    TyLam (svar, term, Dummy(*ID (get_info_id ())*))
  let mk_lambda args term =
    List.fold_right args ~init:term ~f:(fun (tvar, sort) -> mk_bind Lambda tvar sort)

  (** Observation *)
  let is_var = function Var (_, _) -> true | _ -> false
  let is_con = function Con (_, _) -> true | _ -> false
  let is_app = function App (_, _, _) -> true | _ -> false
  let is_lam = function Bin (Lambda, _, _, _, _) -> true | _ -> false
  let is_bin = function Bin (_, _, _, _, _) -> true | _ -> false
  let is_let = function Let (_, _, _, _, _) -> true | _ -> false
  let is_tyapp = function TyApp (_, _, _) -> true | _ -> false
  let is_tylam = function TyLam (_, _, _) -> true | _ -> false

  let svs_of svs_of_sym svs_of_sort term =
    let rec aux ~next = function
      | Var (_, _) -> next Set.Poly.empty
      | Con (sym, _) -> next @@ svs_of_sym sym
      | App (t1, t2, _) ->
        aux t1 ~next:(fun svs1 -> aux t2 ~next:(fun svs2 -> next @@ Set.Poly.union svs1 svs2))
      | Bin (_, _, sort, term, _) ->
        aux term ~next:(fun svs ->
            next @@ Set.Poly.union_list [svs; svs_of_sort sort])
      | Let (_, sort, t1, t2, _) ->
        aux t1 ~next:(fun svs1 -> aux t2 ~next:(fun svs2 ->
            next @@ Set.Poly.union_list [svs1; svs2; svs_of_sort sort]))
      | TyApp (term, _, _) | TyLam (_, term, _) -> aux term ~next
    in aux term ~next:Fn.id
  let fvs_of term =
    let rec aux ~next = function
      | Var (var, _) ->
        if LogicOld.is_dummy_term var None || Map.Poly.mem (Atomic.get LogicOld.ref_fenv) var
        then next Set.Poly.empty
        else next @@ Set.Poly.singleton var
      | Con (_, _) -> next Set.Poly.empty
      | App (t1, t2, _) ->
        aux t1 ~next:(fun fvs1 -> aux t2 ~next:(fun fvs2 -> next @@ Set.Poly.union fvs1 fvs2))
      | Bin (_, var, _, term, _) ->
        aux term ~next:(fun fvs -> next @@ Set.Poly.remove fvs var)
      | Let (var, _, t1, t2, _) ->
        aux t1 ~next:(fun fvs1 ->
            aux t2 ~next:(fun fvs2 ->
                next @@ Set.Poly.remove (Set.Poly.union fvs1 fvs2) var))
      | TyApp (term, _, _) | TyLam (_, term, _) -> aux term ~next
    in aux term ~next:Fn.id

  let rec pvar_of_atom = function
    | Var (tvar, _) -> tvar
    | App (t, _, _) -> pvar_of_atom t
    | _ -> assert false

  let rec ast_size = function
    | Var (_, _) | Con (_, _) -> 1
    | App (t1, t2, _) | Let (_, _, t1, t2, _) ->
      ast_size t1 + ast_size t2 + 1
    | Bin (_, _, _, term, _) | TyApp (term, _, _) | TyLam (_, term, _) ->
      ast_size term + 1

  (** Construction *)
  let mk_binds binder bounds body =
    let ftv = fvs_of body in
    let bounds = List.filter ~f:(fun (tvar, _) -> Set.Poly.mem ftv tvar) bounds in
    List.fold_right bounds ~init:body ~f:(fun (tvar, sort) -> mk_bind binder tvar sort)

  (** Destruction *)
  let let_var = function
    | Var (var, info) -> (var, info)
    | _ -> assert false
  let let_con = function
    | Con (sy, info) -> (sy, info)
    | _ -> assert false
  let let_app = function
    | App (t1, t2, info) -> (t1, t2, info)
    | _ -> assert false
  let rec let_apps = function
    | App (t1, t2, _) ->
      let t, ts = let_apps t1 in
      t, ts @ [t2]
    | t -> t, []
  let let_sym_app t =
    let t, ts = let_apps t in
    match t with
    | Con (sym, _) -> sym, ts
    | _ -> assert false
  let let_var_app t =
    let t, ts = let_apps t in
    match t with
    | Var (x, _) -> x, ts
    | _ -> assert false
  let let_bin = function
    | Bin (bind, var, sort, term, info) -> (bind, var, sort, term, info)
    | _ -> assert false
  let let_let = function
    | Let (var, sort, t1, t2, info) -> (var, sort, t1, t2, info)
    | _ -> assert false
  let let_tyapp = function
    | TyApp (term, sort, info) -> (term, sort, info)
    | _ -> assert false
  let let_tylam = function
    | TyLam (svar, term, info) -> (svar, term, info)
    | _ -> assert false
  let let_lam =
    let rec aux args = function
      | Bin (Lambda, tvar, sort, term, _) -> aux ((tvar, sort) :: args) term
      | term -> List.rev args, term
    in
    aux []

  (** Sorts *)

  let open_arity_of_sym sort_of_sym sym = Sort.arity_of @@ sort_of_sym sym
  let rec open_sort_of sort_of_sym subst_sort var_env = function
    | Var (v, _) -> begin
        try Map.Poly.find_exn var_env v with _ -> failwith @@ Ident.name_of_tvar v ^ " not found"
      end
    | Con (sym, _) -> sort_of_sym sym
    | App (t1, t2, _) -> begin
        match
        open_sort_of sort_of_sym subst_sort var_env t1,
        open_sort_of sort_of_sym subst_sort var_env t2 with
        | Sort.SArrow (s11, (o, s12, Sort.Pure)), s2 when Sort.is_empty_opsig o ->
          if Stdlib.(s11 = s2) then s12 else (*ToDo*)s12
        | _ -> failwith "The sort of App is unmached"
      end
    | Bin (bind, tvar, sort, term, _) -> begin
        match bind with
        | Lambda ->
          let new_var_env = Map.Poly.add_exn var_env ~key:tvar ~data:sort in
          open_sort_of sort_of_sym subst_sort new_var_env term
        | _ -> failwith "The sort of Bin is not implemented yet"
      end
    | Let (v, sort, t1, t2, _) ->
      if not (Stdlib.(sort = open_sort_of sort_of_sym subst_sort var_env t1)) then
        failwith "The sort of let-expression is wrong"
      else
        let new_var_env = Map.Poly.add_exn var_env ~key:v ~data:sort in
        open_sort_of sort_of_sym subst_sort new_var_env t2
    | TyApp (term, sort, _) -> begin
        match term with
        | Con (sym, _) -> begin
            match sort_of_sym sym with
            | Sort.SForAll (svar, s1) -> subst_sort (svar, sort) s1
            | _ -> failwith "TyApp can be used only for SForAll"
          end
        | TyApp _ -> failwith "it is not implemented yet"
        | TyLam _ -> failwith "it is not implemented yet"
        | _ -> failwith "The sort of term cannot apply another sort"
      end
    | TyLam _ -> failwith "it is not implemented yet"

  let sym_sort_map = Map.Poly.empty
  let sort_of_sym = Map.Poly.find_exn sym_sort_map
  let arity_of_sym = open_arity_of_sym sort_of_sym

  (** Substitution *)
  let rec rename map = function
    | Var (var, info) -> begin
        match Map.Poly.find map var with
        | None -> Var (var, info)
        | Some var' -> mk_var var'
      end
    | Con (_, _) as c -> c
    | App (t1, t2, info) -> App (rename map t1, rename map t2, info)
    | Bin (bind, var, sort, term, info) ->
      let map' = Map.Poly.remove map var in
      Bin (bind, var, sort, rename map' term, info)
    | Let (var, sort, t1, t2, info) ->
      let map' = Map.Poly.remove map var in
      Let (var, sort, rename map t1, rename map' t2, info)
    | TyApp (term, sort, info) -> TyApp (rename map term, sort, info)
    | TyLam (svar, term, info) -> TyLam (svar, rename map term, info)
  let rec subst env t =
    let rec aux ~next env = function
      | Var (var, info) -> begin
          match Map.Poly.find env var with
          | None -> next (Var (var, info))
          | Some t -> next t
        end
      | Bin (bind, var, sort, term, info) ->
        let var' = Ident.mk_fresh_tvar () in
        let env' = Map.Poly.add_exn (Map.Poly.remove env var) ~key:var ~data:(mk_var var') in
        aux env' term ~next:(fun t -> next @@ Bin (bind, var', sort, t, info))
      | Let (var, sort, t1, t2, info) ->
        aux env t1 ~next:(fun t1' -> aux env t2 ~next:(fun t2' -> next @@ Let (var, sort, t1', t2', info)))
      | App (t1, t2, _) -> aux env t1 ~next:(fun t1' -> aux env t2 ~next:(fun t2' -> next @@ beta_reduction t1' [t2']))
      | TyApp (term, sort, info) -> aux env term ~next:(fun t -> next @@ TyApp (t, sort, info))
      | TyLam (svar, term, info) -> aux env term ~next:(fun t -> next @@ TyLam (svar, t, info))
      | t -> next t
    in
    aux env t ~next:Fn.id
  and beta_reduction term args =
    let rec aux env term args =
      match term, args with
      | Bin (Lambda, var, _sort, term', _), arg :: args' ->
        aux (Map.Poly.add_exn env ~key:var ~data:arg) term' args'
      | _, [] -> subst env term
      | _, _ -> mk_apps term args
    in
    aux Map.Poly.empty term args
  let refresh (senv, t) =
    let map = Map.Poly.map senv ~f:(fun _ -> Ident.mk_fresh_tvar ()) in
    Map.rename_keys_map map senv, rename map t
  let rec unify t1 t2 =
    match t1, t2 with
    | Var (tvar, _), t | t, Var (tvar, _) -> (* ToDo: occurs check *)
      Map.Poly.singleton tvar t |> Option.some
    | App (Var (tvar1, _), t1, _), App (Var (tvar2, _), t2, _) ->
      if Stdlib.(tvar1 = tvar2) then unify t1 t2 else None
    | Con (s1, _), Con (s2, _) ->
      if Stdlib.(s1 = s2) then Some Map.Poly.empty else None
    | App (t11, t12, _), App (t21, t22, _) -> begin
        match unify t11 t21, unify t12 t22 with
        | Some th1, Some th2 ->
          Map.fold th1 ~init:th2 ~f:(fun ~key ~data map ->
              match Map.Poly.add ~key:key ~data:data map with
              | `Ok map' -> map' | _ -> map)
          |> Option.some
        | _, _ -> None
      end
    | _ -> None

  (** Transformation *)
  let reduce_sort_map (senv, t) =
    Map.Poly.filter_keys senv ~f:(Set.Poly.mem @@ fvs_of t), t

  (** Printing *)
  let open_str_of str_of_sort str_of_sym =
    let rec str_of = function
      | Var (Ident.Tvar id, _) ->
        Printf.sprintf "(%s)" id
      | Con (sym, _) ->
        Printf.sprintf "(%s)" (str_of_sym sym)
      | App (t1, t2, _) ->
        Printf.sprintf "(%s, %s)" (str_of t1) (str_of t2)
      | Bin (bind, Ident.Tvar id, sort, term, _) ->
        Printf.sprintf "%s %s:%s. (%s)"
          (match bind with Mu -> "Mu" | Nu -> "Nu" | Lambda -> "Lam" | Forall -> "forall" | Exists -> "exists")
          id (str_of_sort sort)(str_of term)
      | Let (Ident.Tvar id, sort, t1, t2, _) ->
        Printf.sprintf "Let %s:%s = %s (%s)"
          id (str_of_sort sort) (str_of t1) (str_of t2)
      | TyApp (term, sort, _) ->
        Printf.sprintf "(%s)[%s]" (str_of term) (str_of_sort sort)
      | TyLam (svar, term, _) ->
        Printf.sprintf "%s. (%s)"
          (match svar with | Ident.Svar s -> s) (str_of term)
    in str_of
  let rec open_str_of_sort str_of_sort = function
    | Sort.SArrow (s1, (o, s2, Sort.Pure)) ->
      let str_o = if Sort.is_empty_opsig o then "" else "_ |> " in
      Printf.sprintf "%s -> %s%s" (open_str_of_sort str_of_sort s1) str_o (open_str_of_sort str_of_sort s2)
    | Sort.SArrow (s1, (o, s2, Sort.Eff _)) ->
      let str_o = if Sort.is_empty_opsig o then "" else "_ |> " in
      Printf.sprintf "%s -> %s%s / _" (open_str_of_sort str_of_sort s1) str_o (open_str_of_sort str_of_sort s2)
    | Sort.SVar (Ident.Svar s) -> s
    | Sort.SForAll (Ident.Svar v, s) ->
      Printf.sprintf "(forall %s. %s)" v (open_str_of_sort str_of_sort s)
    | sort -> str_of_sort sort
  let str_of_sym _ = failwith "Term.str_of_sym"
  let str_of_termlit _ = failwith "Term.str_of_termlit"
  let str_of_sort _ = failwith "Term.str_of_sort"
  let str_of = open_str_of str_of_sort str_of_sym

  (** Evaluation *)
  let open_assert_sort_check assert_sort_check_of =
    let assert_sort_check sort = function
      | FunLit _ -> (match sort with Sort.SArrow (_, _) -> () | _ -> assert false)
      | SFunLit _ -> assert false
      | lit -> assert_sort_check_of sort lit
    in assert_sort_check
  let open_eval eval_sym of_termlit _type_env =
    let rec eval = function
      | Var _ -> failwith "Any term variables should be removed before evaluation "
      | Con (sym, _) -> eval_sym sym
      | App (Bin (Lambda, v, _sort, term, _), t2, _) ->
        eval @@ subst (Map.Poly.singleton v t2) term
      | App (t1, t2, _) ->
        (match eval t1 with
         | FunLit flit -> flit (eval t2)
         | _ -> failwith "the term cannot be applyed")
      | Let (x, _, t1, t2, _) -> let l1 = eval t1 in
        eval @@ subst (Map.Poly.singleton x @@ of_termlit l1) t2
      | Bin (_, _, _, _, _) -> failwith "eval of Lam is not implemented yet"
      | TyApp (term, sort, _) -> begin
          match eval term with
          | SFunLit sfun -> sfun sort
          | _ -> failwith "invalid type for TyApp"
        end
      | TyLam (_, _, _) -> failwith "invalid type for TyLam"
    in eval

  (* assume that term is let-normalized and alpha-renamed *)
  let rec let_sort_env_of = function
    | Let (v, s, _, b, _) ->
      Map.Poly.add_exn ~key:v ~data:s @@ let_sort_env_of b
    | _ -> Map.Poly.empty
  (* assume that term is let-normalized and alpha-renamed *)
  let rec let_env_of ?(map=Map.Poly.empty) = function
    | Let (var, _, def, body, _) ->
      let_env_of ~map:(Map.Poly.set map ~key:var ~data:(subst map def)) body
    | _ -> Map.Poly.empty

  let is_termlit _ = false
  let of_termlit _ = failwith "Term.of_termlit"
  let assert_sort_check _ _ = failwith "Term.assert_sort_check"
  let eval_sym _ = failwith "Term.eval_sym"
  let eval _ _ = failwith "Term.eval"
end

module type BoolTermType = sig
  include TermType

  type sym += True | False | Not | And | Or | Imply | Iff | Xor | IfThenElse | Eq | Neq
  type Sort.t += SBool
  type termlit += BoolLit of bool

  (** Construction *)
  val mk_bool: bool -> term
  val mk_and: unit -> term
  val mk_or: unit -> term
  val mk_not: unit -> term
  val mk_imply: unit -> term
  val mk_xor: unit -> term
  val mk_iff: unit -> term
  val mk_ite: Sort.t -> term
  val mk_bool_ite: unit -> term
  val mk_eq: Sort.t -> term
  val mk_neq: Sort.t -> term
  val mk_bool_eq: unit -> term
  val mk_bool_neq: unit -> term

  val and_of: term list -> term
  val or_of: term list -> term
  val neg_of: term -> term
  val imply_of: term -> term -> term
  val eq_of: Sort.t -> term -> term -> term
  val neq_of: Sort.t -> term -> term -> term
  val ite_of: Sort.t -> term -> term -> term -> term

  val mk_forall: sort_env_list -> term -> term
  val mk_exists: sort_env_list -> term -> term
  val forall: sort_env_list -> term -> term
  val exists: sort_env_list -> term -> term

  (** Destruction *)

  val let_not: term -> term

  (** Observation *)
  val is_bool: term -> bool
  val is_bool_sort : Sort.t -> bool
  val is_true: term -> bool
  val is_false: term -> bool
  val is_not: term -> bool
  val is_pvar_app: sort_env_map -> sort_env_map -> term -> bool

  val conjuncts_of: term -> term list
  val disjuncts_of: term -> term list

  (** Transformation *)
  val cnf_of: sort_env_map -> sort_env_map -> term -> (term Set.Poly.t * term Set.Poly.t * term) Set.Poly.t
  val nnf_of: term -> term
  val elim_imp: term -> term
end

module BoolTerm : BoolTermType = struct
  include Term

  type sym += True | False | Not | And | Or | Imply | Iff | Xor | IfThenElse | Eq | Neq
  type Sort.t += SBool
  type termlit += BoolLit of bool

  (** Construction *)
  let mk_bool b = if b then mk_con True else mk_con False
  let mk_and () = mk_con And
  let mk_or () = mk_con Or
  let mk_not () = mk_con Not
  let mk_imply () = mk_con Imply
  let mk_xor () = mk_con Xor
  let mk_iff () = mk_con Iff
  let mk_ite sort = mk_tyapp (mk_con IfThenElse) sort
  let mk_bool_ite () = mk_ite SBool
  let mk_eq sort = mk_tyapp (mk_con Eq) sort
  let mk_neq sort = mk_tyapp (mk_con Neq) sort
  let mk_bool_eq () = mk_eq SBool
  let mk_bool_neq () = mk_neq SBool

  let and_of = function
    | [] -> mk_bool true
    | t::ts -> List.fold ~init:t ~f:(fun acc t -> mk_apps (mk_and ()) [acc; t]) ts
  let or_of = function
    | [] -> mk_bool false
    | t::ts -> List.fold ~init:t ~f:(fun acc t -> mk_apps (mk_or ()) [acc; t]) ts
  let rec neg_of = function
    | Let (v, s, d, b, i) -> Let (v, s, d, neg_of b, i)
    | term -> mk_app (mk_not ()) term
  let imply_of t1 t2 = mk_apps (mk_imply ()) [t1; t2]
  let eq_of ty t1 t2 = mk_apps (mk_eq ty) [t1; t2]
  let neq_of ty t1 t2 = mk_apps (mk_neq ty) [t1; t2]
  let ite_of ty t1 t2 t3 = mk_apps (mk_ite ty) [t1; t2; t3]

  let mk_forall args term =
    List.fold_right args ~init:term ~f:(fun (tvar, sort) -> mk_bind Forall tvar sort)
  let mk_exists args term =
    List.fold_right args ~init:term ~f:(fun (tvar, sort) -> mk_bind Exists tvar sort)
  let forall bounds body = mk_binds Forall bounds body
  let exists bounds body = mk_binds Exists bounds body

  (** Destruction *)
  let let_not t =
    match let_app t with
    | Con (Not, _), t, _ -> t
    | _, _, _ -> assert false

  (** Observation *)
  let is_bool term =
    if is_con term
    then let sym, _ = let_con term in Stdlib.(sym = True) || Stdlib.(sym = False)
    else false
  let is_bool_sort = function SBool -> true | _ -> false
  let is_true term =
    if is_con term
    then let sym, _ = let_con term in Stdlib.(sym = True)
    else false
  let is_false term =
    if is_con term
    then let sym, _ = let_con term in Stdlib.(sym = False)
    else false
  let is_not term =
    if is_app term then
      let t, _, _ = let_app term in
      if is_con t then let sym, _ = let_con t in Stdlib.(sym = Not)
      else false
    else false
  let rec is_pvar_app exi_senv uni_senv = function
    | Var (tvar, _) ->
      (match Map.Poly.find exi_senv tvar, Map.Poly.find uni_senv tvar with
       | Some sort, None -> is_bool_sort @@ Sort.ret_of sort
       | None, Some _ -> false
       | Some _, Some _ -> failwith (Printf.sprintf "[is_pvar_app] %s is doubly bound" (Ident.name_of_tvar tvar))
       | None, None -> failwith (Printf.sprintf "[is_pvar_app] %s is not bound" (Ident.name_of_tvar tvar)))
    | App (t, _, _) -> is_pvar_app exi_senv uni_senv t
    | _ -> false
  let rec is_fvar_app fenv = function
    | Var (tvar, _) -> Map.Poly.mem fenv tvar
    | App (t, _, _) -> is_fvar_app fenv t
    | _ -> false

  let rec conjuncts_of = function
    | App (_, _, _) as t ->
      begin
        match let_apps t with
        | Con (And, _), args -> List.concat_map args ~f:conjuncts_of
        | _, _ -> [t]
      end
    | t -> [t]
  let rec disjuncts_of = function
    | App (_, _, _) as t ->
      begin
        match let_apps t with
        | Con (Or, _), args -> List.concat_map args ~f:disjuncts_of
        | _, _ -> [t]
      end
    | t -> [t]

  (** Transformation *)
  let insert_let var sort def info term =
    if Set.Poly.mem (fvs_of term) var then
      let var' = Ident.mk_fresh_tvar () in
      Let (var', sort, def, rename (Map.Poly.singleton var var') term, info)
    else term
  let insert_let_var_app var sort def info atom =
    let x, ts = let_var_app atom in
    mk_var_app x @@ List.map ts ~f:(insert_let var sort def info)
  let rec nnf_of = function
    | App (Con (Not, _), Con (True, _), _) -> (* not true -> false *)
      mk_bool false
    | App (Con (Not, _), Con (False, _), _) -> (* not false -> true *)
      mk_bool true
    | App (Con (Not, _), App (Con (Not, _), t, _), _) -> (* not (not t) -> t *)
      nnf_of t
    | App (Con (Not, _), App (App (Con (And, _), t1, _), t2, _), _) -> (* not (t1 and t2) -> (not t1) or (not t2) *)
      mk_apps (mk_or ()) [nnf_of @@ neg_of t1; nnf_of @@ neg_of t2]
    | App (Con (Not, _), App (App (Con (Or, _), t1, _), t2, _), _) -> (* not (t1 or t2) -> (not t1) and (not t2) *)
      mk_apps (mk_and ()) [nnf_of @@ neg_of t1; nnf_of @@ neg_of t2]
    | App (Con (Not, _), App (App (Con (Imply, _), t1, _), t2, _), _) -> (* not (t1 => t2) -> t1 and (not t2) *)
      mk_apps (mk_and ()) [nnf_of t1; nnf_of @@ neg_of t2]
    | App (Con (Not, _), App (App (Con (Iff, _), t1, _), t2, _), _) -> (* not (t1 <=> t2) -> t1 <> t2 *)
      mk_apps (mk_neq SBool) [nnf_of t1; nnf_of t2]
    | App (Con (Not, _), App (App (Con (Xor, _), t1, _), t2, _), _) -> (* not (t1 xor t2) -> t1 = t2 *)
      mk_apps (mk_eq SBool) [nnf_of t1; nnf_of t2]
    | App (Con (Not, _), Bin (Forall, x, s, t, _), _) ->
      mk_bind Exists x s (nnf_of @@ neg_of t)
    | App (Con (Not, _), Bin (Exists, x, s, t, _), _) ->
      mk_bind Forall x s (nnf_of @@ neg_of t)
    | App (Con (Not, _), Let (v, s, d, b, _), _) ->
      mk_let v s (nnf_of d) (nnf_of @@ neg_of b)
    | App (Con (Not, _), t, _) as term -> begin
        match let_apps t with
        | TyApp (Con (Eq, _), s, _), [t1; t2] ->
          nnf_of @@ mk_apps (mk_neq s) [t1; t2]
        | TyApp (Con (Neq, _), s, _), [t1; t2] ->
          nnf_of @@ mk_apps (mk_eq s) [t1; t2]
        | _ -> term
      end
    | App (App (Con (And, _), t1, _), t2, _)  ->
      mk_apps (mk_and ()) [nnf_of t1; nnf_of t2]
    | App (App (Con (Or, _), t1, _), t2, _)  ->
      mk_apps (mk_or ()) [nnf_of t1; nnf_of t2]
    | App (App (Con (Imply, _), t1, _), t2, _)  ->
      mk_apps (mk_or ()) [nnf_of @@ neg_of t1; nnf_of t2]
    | App (App (Con (Iff, _), t1, _), t2, _)  -> (* t1 <=> t2 -> t1 = t2 *)
      nnf_of @@ mk_apps (mk_eq SBool) [t1; t2]
    | App (App (Con (Xor, _), t1, _), t2, _)  -> (* t1 xor t2 -> t1 <> t2 *)
      nnf_of @@ mk_apps (mk_neq SBool) [t1; t2]
    | Bin (b, x, s, t, _) -> mk_bind b x s (nnf_of t)
    | Let (v, s, d, b, _) -> mk_let v s (nnf_of d) (nnf_of b)
    | term ->
      match let_apps term with
      | TyApp (Con (Eq, _), SBool, _), [t1; t2] ->
        mk_apps (mk_eq SBool) [nnf_of t1; nnf_of t2]
      (* t1 = t2 -> (t1 and t2) or (not t1 and not t2) *)
      (*mk_apps (mk_or ()) [mk_apps (mk_and ()) [nnf_of t1; nnf_of t2];
                           mk_apps (mk_and ()) [nnf_of @@ neg_of t1; nnf_of @@ neg_of t2]]*)
      (* t1 = t2 -> (not t1 or t2) and (t1 or not t2) *)
      (*mk_apps (mk_and ()) [mk_apps (mk_or ()) [nnf_of @@ neg_of t1; nnf_of t2];
                           mk_apps (mk_or ()) [nnf_of t1; nnf_of @@ neg_of t2]]*)
      | TyApp (Con (Neq, _), SBool, _), [t1; t2] ->
        mk_apps (mk_neq SBool) [nnf_of t1; nnf_of t2]
      (* t1 <> t2 -> (t1 and not t2) or (not t1 and t2) *)
      (*mk_apps (mk_or ()) [mk_apps (mk_and ()) [nnf_of t1; nnf_of @@ neg_of t2];
                           mk_apps (mk_and ()) [nnf_of @@ neg_of t1; nnf_of t2]]*)
      (* t1 <> t2 -> (t1 or t2) and (not t1 or not t2) *)
      (*mk_apps (mk_and ()) [mk_apps (mk_or ()) [nnf_of t1; nnf_of t2];
                           mk_apps (mk_or ()) [nnf_of @@ neg_of t1; nnf_of @@ neg_of t2]]*)
      | _ -> term
  let rec aux exi_senv senv = function
    | Con (True, _) | App (Con (Not, _), Con (False, _), _) ->
      Set.Poly.empty
    | Con (False, _) | App (Con (Not, _), Con (True, _), _) ->
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
    | t when Set.Poly.is_empty @@ Set.Poly.inter (fvs_of t) (Map.key_set exi_senv) ->
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton t)
    | App (Con (Not, _), t, _) ->
      if is_pvar_app exi_senv senv t then
        Set.Poly.singleton (Set.Poly.empty, Set.Poly.singleton t, Set.Poly.empty)
      else (* not reachable? *)
        Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (neg_of t))
    | App (App (Con (And, _), t1, _), t2, _) ->
      let cls1 = aux exi_senv senv t1 in
      let cls2 = aux exi_senv senv t2 in
      let phis, cls =
        Set.Poly.union cls1 cls2
        |> Set.Poly.partition_tf ~f:(fun (ps, ns, _phis) ->
            Set.Poly.is_empty ps && Set.Poly.is_empty ns)
        |> Pair.map (Set.Poly.map ~f:(fun (_, _, phis) ->
            or_of @@ Set.Poly.to_list phis)) Fn.id
      in
      if Set.Poly.is_empty phis then cls
      else Set.Poly.add cls (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton @@ and_of @@ Set.Poly.to_list phis)
    | App (App (Con (Or, _), t1, _), t2, _) ->
      let cls1 = aux exi_senv senv t1 in
      let cls2 = aux exi_senv senv t2 in
      Set.cartesian_map cls1 cls2 ~f:(fun (ps1, ns1, phis1) (ps2, ns2, phis2) ->
          Set.Poly.union ps1 ps2, Set.Poly.union ns1 ns2, Set.Poly.union phis1 phis2)
    | Let (var, sort, def, body, info) ->
      let senv' = Map.Poly.set senv ~key:var ~data:sort in
      Set.Poly.map (aux exi_senv senv' body) ~f:(fun (ps, ns, phis) ->
          Set.Poly.map ~f:(insert_let_var_app var sort def info) ps,
          Set.Poly.map ~f:(insert_let_var_app var sort def info) ns,
          Set.Poly.singleton @@ insert_let var sort def info @@ or_of @@ Set.Poly.to_list phis)
    | t ->
      if is_pvar_app exi_senv senv t then
        Set.Poly.singleton (Set.Poly.singleton t, Set.Poly.empty, Set.Poly.empty)
      else
        match let_apps t with
        | TyApp (Con (Eq, _), SBool, _), [t1; t2]
          when (Fn.non Set.Poly.is_empty @@ Set.Poly.inter
                  (Set.Poly.union (fvs_of t1) (fvs_of t2))
                  (Map.key_set exi_senv)) &&
               not (is_fvar_app (Atomic.get LogicOld.ref_fenv) t1) &&
               not (is_fvar_app (Atomic.get LogicOld.ref_fenv) t2) ->
          (* t1 = t2 -> (not t1 or t2) and (t1 or not t2) *)
          aux exi_senv senv @@
          mk_apps (mk_and ()) [mk_apps (mk_or ()) [nnf_of @@ neg_of t1; nnf_of t2];
                               mk_apps (mk_or ()) [nnf_of t1; nnf_of @@ neg_of t2]]
        | TyApp (Con (Neq, _), SBool, _), [t1; t2]
          when (Fn.non Set.Poly.is_empty @@ Set.Poly.inter
                  (Set.Poly.union (fvs_of t1) (fvs_of t2))
                  (Map.key_set exi_senv)) &&
               not (is_fvar_app (Atomic.get LogicOld.ref_fenv) t1) &&
               not (is_fvar_app (Atomic.get LogicOld.ref_fenv) t2) ->
          (* t1 <> t2 -> (t1 or t2) and (not t1 or not t2) *)
          aux exi_senv senv @@
          mk_apps (mk_and ()) [mk_apps (mk_or ()) [nnf_of t1; nnf_of t2];
                               mk_apps (mk_or ()) [nnf_of @@ neg_of t1; nnf_of @@ neg_of t2]]
        | _ -> (* not reachable *)
          Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton t)
  (* assume that [term] is in NNF *)
  let cnf_of exi_senv uni_senv term =
    Set.Poly.map (aux exi_senv uni_senv term) ~f:(fun (pos, neg, phis) -> pos, neg, or_of @@ Set.Poly.to_list phis)

  let rec elim_imp = function
    | App (App (Con (Imply, _), t1, _), t2, _) -> (* t1 => t2 -> (not t1) or t2 *)
      let t1' = elim_imp t1 |> neg_of in
      let t2' = elim_imp t2 in
      mk_apps (mk_or ()) [t1'; t2']
    | App (t1, t2, _) ->
      let t1' = elim_imp t1 in
      let t2' = elim_imp t2 in
      mk_app t1' t2'
    | Bin (b, x, s, t, _) ->
      mk_bind b x s (elim_imp t)
    | Let (x, s, t1, t2, _) ->
      mk_let x s (elim_imp t1) (elim_imp t2)
    | TyApp (t, s, _) ->
      mk_tyapp (elim_imp t) s
    | TyLam (x, t, _) ->
      mk_tylam x (elim_imp t)
    | term -> term

  (** Sorts *)
  let bb = Sort.mk_arrow SBool SBool
  let bbb = Sort.mk_arrow SBool bb
  let sym_sort_map =
    Map.Poly.of_alist_exn
      [ (True, SBool); (False, SBool); (Not, bb);
        (And, bbb); (Or, bbb); (Imply, bbb); (Iff, bbb); (Xor, bbb);
        (IfThenElse, let var = Ident.mk_fresh_svar () in
         Sort.SForAll (var, Sort.mk_arrow SBool @@ Sort.mk_arrow (Sort.SVar var) @@ Sort.mk_arrow (Sort.SVar var) @@ Sort.SVar var));
        (Eq, let var = Ident.mk_fresh_svar () in
         Sort.SForAll (var, Sort.mk_arrow (Sort.SVar var) @@ Sort.mk_arrow (Sort.SVar var) SBool));
        (Neq, let var = Ident.mk_fresh_svar () in
         Sort.SForAll (var, Sort.mk_arrow (Sort.SVar var) @@ Sort.mk_arrow (Sort.SVar var) SBool)) ]
  let sort_of_sym = Map.Poly.find_exn sym_sort_map
  let arity_of_sym = Term.open_arity_of_sym sort_of_sym

  (** Printing *)
  let str_of_sym = function
    | True -> "True"
    | False -> "False"
    | Not -> "Not"
    | And -> "And"
    | Or -> "Or"
    | Imply -> "Imply"
    | Iff -> "Iff"
    | Xor -> "Xor"
    | IfThenElse -> "IfThenElse"
    | Eq -> "Eq"
    | Neq -> "Neq"
    | _ -> failwith "BoolTerm.str_of_sym"
  let str_of_termlit = function
    | BoolLit true -> "true"
    | BoolLit false -> "false"
    | _ -> assert false
  let str_of_sort_theory = function
    | SBool -> "bool"
    | _ -> failwith "unknown sort in BoolTerm.str_of_sort_theory"
  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym

  (** Evaluation *)
  let is_termlit = function BoolLit _ -> true | _ -> false
  let of_termlit = function BoolLit b -> mk_bool b | _ -> assert false
  let assert_sort_check_of_theory sort lit =
    match sort, lit with
    | SBool, BoolLit _ -> ()
    | _ -> assert false
  let assert_sort_check = open_assert_sort_check assert_sort_check_of_theory
  let eval_sym = function
    | True -> BoolLit true
    | False -> BoolLit false
    | Not ->
      FunLit (function BoolLit x -> BoolLit (not x) | _ -> assert false)
    | And ->
      FunLit (function
          | BoolLit x ->
            FunLit (function BoolLit y -> BoolLit (x && y) | _ -> assert false)
          | _ -> assert false)
    | Or  ->
      FunLit (function
          | BoolLit x ->
            FunLit (function BoolLit y -> BoolLit (x || y) | _ -> assert false)
          | _ -> assert false)
    | Imply ->
      FunLit (function
          | BoolLit x ->
            FunLit (function BoolLit y -> BoolLit (not x || y) | _ -> assert false)
          | _ -> assert false)
    | Iff ->
      FunLit (function
          | BoolLit x ->
            FunLit (function BoolLit y -> BoolLit (Stdlib.(x = y)) | _ -> assert false)
          | _ -> assert false)
    | Xor ->
      FunLit (function
          | BoolLit x ->
            FunLit (function BoolLit y -> BoolLit (Stdlib.(x <> y)) | _ -> assert false)
          | _ -> assert false)
    | IfThenElse ->
      SFunLit (fun sort ->
          FunLit (function
              | BoolLit t1 ->
                FunLit (fun l2 ->
                    assert_sort_check sort l2;
                    FunLit (fun l3 -> assert_sort_check sort l3; if t1 then l2 else l3))
              | _ -> assert false))
    | Eq ->
      SFunLit (fun sort ->
          FunLit (fun l1 ->
              assert_sort_check sort l1;
              FunLit (fun l2 -> assert_sort_check sort l2; BoolLit (Stdlib.(l1 = l2)))))
    | Neq ->
      SFunLit (fun sort ->
          FunLit (fun l1 ->
              assert_sort_check sort l1;
              FunLit (fun l2 -> assert_sort_check sort l2; BoolLit (Stdlib.(l1 <> l2)))))
    | _ -> assert false
  let eval = open_eval eval_sym of_termlit
end

module type IntTermType = sig
  include TermType

  type sym += Int of Z.t | Add | Sub | Mult | Div | Mod | Neg | Abs | Rem
  type Sort.t += SInt
  type termlit += IntLit of Z.t

  (** Construction *)
  val zero: unit -> term
  val one: unit -> term
  val mk_int: Z.t -> term
  val mk_from_int: int -> term
  val mk_add: unit -> term
  val mk_sub: unit -> term
  val mk_mult: unit -> term
  val mk_div: unit -> term
  val mk_mod: unit -> term
  val mk_neg: unit -> term
  val mk_abs: unit -> term
  val mk_rem : unit -> term

  val sum: term list -> term
  val prod: term list -> term

  (** Evalaution *)
  val neg_sym: sym -> sym
end

module IntTerm : IntTermType = struct
  include Term

  type sym += Int of Z.t | Add | Sub | Mult | Div | Mod | Neg | Abs | Rem
  type Sort.t += SInt
  type termlit += IntLit of Z.t

  (** Construction *)
  let zero () = mk_con (Int (Z.of_int 0))
  let one () = mk_con (Int (Z.of_int 1))
  let mk_int n = mk_con (Int n)
  let mk_from_int n = mk_con (Int (Z.of_int n))
  let mk_add () = mk_con Add
  let mk_sub () = mk_con Sub
  let mk_mult () = mk_con Mult
  let mk_div () = mk_con Div
  let mk_mod () = mk_con Mod
  let mk_neg () = mk_con Neg
  let mk_abs () = mk_con Abs
  let mk_rem () = mk_con Rem

  let sum = function
    | [] -> zero ()
    | t :: ts -> List.fold ~init:t ts ~f:(fun t1 t2 -> mk_apps (mk_add ()) [t1; t2])
  let prod = function
    | [] -> one ()
    | t :: ts -> List.fold ~init:t ts ~f:(fun t1 t2 -> mk_apps (mk_mult ()) [t1; t2])

  (** Sorts *)
  let ii = Sort.mk_arrow SInt SInt
  let iii = Sort.mk_arrow SInt ii
  let sym_sort_map =
    Map.Poly.of_alist_exn
      [ (Add, iii); (Sub, iii); (Mult, iii); (Div, iii); (Mod, iii); (Neg, ii); (Abs, ii) ]
  let sort_of_sym = function
    | Int _ -> SInt
    | sym -> Map.Poly.find_exn sym_sort_map sym
  let arity_of_sym = Term.open_arity_of_sym sort_of_sym

  (** Printing *)
  let str_of_sym = function
    | Int n -> Printf.sprintf "Int %s" @@ Z.to_string n
    | Add -> "Add"
    | Sub -> "Sub"
    | Mult -> "Mult"
    | Div -> "Div"
    | Mod -> "Mod"
    | Neg-> "Neg"
    | Abs -> "Abs"
    | Rem -> "Rem"
    | _ -> failwith "IntTerm.str_of_sym"
  let str_of_termlit = function IntLit n -> Z.to_string n | _ -> assert false
  let str_of_sort_theory = function
    | SInt -> "int"
    | _ -> failwith "unknown sort in IntTerm.str_of_sort_theory"
  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym

  (** Evaluation *)
  let neg_sym = function Add -> Sub | Sub -> Add | _ -> failwith "undefined "

  let is_termlit = function IntLit _ -> true | _ -> false
  let of_termlit = function IntLit n -> mk_int n | _ -> assert false
  let assert_sort_check_of_theory sort lit =
    match sort, lit with
    | SInt, IntLit _ -> ()
    | _ -> assert false
  let assert_sort_check = open_assert_sort_check assert_sort_check_of_theory
  let eval_sym = function
    | Int n -> IntLit n
    | Add ->
      FunLit (function
          | IntLit x ->
            FunLit (function IntLit y -> IntLit (Z.(+) x y) | _ -> assert false)
          | _ -> assert false)
    | Sub ->
      FunLit (function
          | IntLit x ->
            FunLit (function IntLit y -> IntLit (Z.(-) x y) | _ -> assert false)
          | _ -> assert false)
    | Mult->
      FunLit (function
          | IntLit x ->
            FunLit (function IntLit y -> IntLit (Z.( * ) x y) | _ -> assert false)
          | _ -> assert false)
    | Div ->
      FunLit (function
          | IntLit x ->
            FunLit (function IntLit y -> IntLit (Z.(/) x y) | _ -> assert false)
          | _ -> assert false)
    | Mod ->
      FunLit (function
          | IntLit x ->
            FunLit (function IntLit y -> IntLit (Z.(mod) x y) | _ -> assert false)
          | _ -> assert false)
    | Neg -> FunLit (function IntLit x -> IntLit (Z.neg x) | _ -> assert false)
    | Abs -> FunLit (function IntLit x -> IntLit (Z.abs x) | _ -> assert false)
    | _ -> assert false
  let eval = open_eval eval_sym of_termlit
end

module type RealTermType = sig
  include TermType

  type sym += Real of Q.t | RAdd | RSub | RMult | RDiv | RNeg | RAbs
  type Sort.t += SReal
  type termlit += RealLit of Q.t

  (** Construction *)
  val rzero: unit -> term
  val rone: unit -> term
  val mk_real: Q.t -> term
  val mk_from_float: float -> term
  val mk_radd: unit -> term
  val mk_rsub: unit -> term
  val mk_rmult: unit -> term
  val mk_rdiv: unit -> term
  val mk_rneg: unit -> term
  val mk_rabs: unit -> term

  val sum: term list -> term
  val prod: term list -> term

  (** Evalaution *)
  val neg_sym: sym -> sym
end

module RealTerm : RealTermType = struct
  include Term

  type sym += Real of Q.t | RAdd | RSub | RMult | RDiv | RNeg | RAbs
  type Sort.t += SReal
  type termlit += RealLit of Q.t

  (** Construction *)
  let rzero () = mk_con (Real Q.zero)
  let rone () = mk_con (Real Q.one)
  let mk_real r = mk_con (Real r)
  let mk_from_float r = mk_con (Real (Q.of_float r))
  let mk_radd () = mk_con RAdd
  let mk_rsub () = mk_con RSub
  let mk_rmult () = mk_con RMult
  let mk_rdiv () = mk_con RDiv
  let mk_rneg () = mk_con RNeg
  let mk_rabs () = mk_con RAbs

  let sum = function
    | [] -> rzero ()
    | t :: ts -> List.fold ~init:t ts ~f:(fun t1 t2 -> mk_apps (mk_radd ()) [t1; t2])
  let prod = function
    | [] -> rone ()
    | t :: ts -> List.fold ~init:t ts ~f:(fun t1 t2 -> mk_apps (mk_rmult ()) [t1; t2])

  (** Sorts *)
  let rr = Sort.mk_arrow SReal SReal
  let rrr = Sort.mk_arrow SReal rr
  let sym_sort_map =
    Map.Poly.of_alist_exn
      [ (RAdd, rrr); (RSub, rrr); (RMult, rrr); (RDiv, rrr); (RNeg, rr); (RAbs, rr) ]
  let sort_of_sym = function
    | Real _ -> SReal
    | sym -> Map.Poly.find_exn sym_sort_map sym
  let arity_of_sym = Term.open_arity_of_sym sort_of_sym

  (** Printing *)
  let str_of_sym = function
    | Real r -> Printf.sprintf "Real %s" @@ Q.to_string r
    | RAdd -> "Add"
    | RSub -> "Sub"
    | RMult -> "Mult"
    | RDiv -> "Div"
    | RNeg-> "Neg"
    | RAbs -> "Abs"
    | _ -> failwith "RealTerm.str_of_sym"
  let str_of_termlit = function
    | RealLit r -> Q.to_string r
    | _ -> assert false
  let str_of_sort_theory = function
    | SReal -> "real"
    | _ -> failwith "unknown sort in RealTerm.str_of_sort_theory"
  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym

  (** Evaluation *)
  let neg_sym = function RAdd -> RSub | RSub -> RAdd | _ -> failwith "undefined "

  let is_termlit = function RealLit _ -> true | _ -> false
  let of_termlit = function RealLit r -> mk_real r | _ -> assert false
  let assert_sort_check_of_theory sort lit =
    match sort, lit with
    | SReal, RealLit _ -> ()
    | _ -> assert false
  let assert_sort_check = open_assert_sort_check assert_sort_check_of_theory
  let eval_sym = function
    | Real r -> RealLit r
    | RAdd ->
      FunLit (function
          | RealLit x -> FunLit (function RealLit y -> RealLit (Q.(+) x y) | _ -> assert false)
          | _ -> assert false)
    | RSub ->
      FunLit (function
          | RealLit x -> FunLit (function RealLit y -> RealLit (Q.(-) x y) | _ -> assert false)
          | _ -> assert false)
    | RMult->
      FunLit (function
          | RealLit x -> FunLit (function RealLit y -> RealLit (Q.( * ) x y) | _ -> assert false)
          | _ -> assert false)
    | RDiv ->
      FunLit (function
          | RealLit x -> FunLit (function RealLit y -> RealLit (Q.(/) x y) | _ -> assert false)
          | _ -> assert false)
    | RNeg -> FunLit (function RealLit x -> RealLit (Q.neg x) | _ -> assert false)
    | RAbs -> FunLit (function RealLit x -> RealLit (Q.abs x) | _ -> assert false)
    | _ -> assert false
  let eval = open_eval eval_sym of_termlit
end

module type RealIntTermType = sig
  include RealTermType
  include IntTermType

  type sym += ToReal | ToInt

  (** Construction *)
  val mk_to_real: unit -> term
  val mk_to_int: unit -> term
end

module RealIntTerm : RealIntTermType = struct
  include RealTerm
  include IntTerm

  type sym += ToReal | ToInt

  let mk_to_real () = mk_con ToReal
  let mk_to_int () = mk_con ToInt

  (** Sorts *)
  let ri = Sort.mk_arrow SReal SInt
  let ir = Sort.mk_arrow SInt SReal
  let sym_sort_map = Map.Poly.of_alist_exn [ (ToReal, ir); (ToInt, ri) ]
  let sort_of_sym sym =
    try Map.Poly.find_exn sym_sort_map sym with _ ->
    try RealTerm.sort_of_sym sym with _ ->
    try IntTerm.sort_of_sym sym with _ ->
      failwith "RealIntTerm.sort_of_sym"

  (** Printing *)
  let str_of_sym = function
    | ToReal -> "ToReal"
    | ToInt -> "ToInt"
    | sym ->
      try RealTerm.str_of_sym sym with _ ->
      try IntTerm.str_of_sym sym with _ ->
        failwith "RealIntTerm.str_of_sym"
  let str_of_termlit = function
    | IntLit n -> Z.to_string n
    | RealLit r -> Q.to_string r
    | _ -> assert false
  let str_of_sort_theory = function
    | SInt -> "int"
    | SReal -> "real"
    | _ -> failwith "unknown sort RealIntTerm.str_of_sort_theory"
  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym

  (** Evalaution *)
  let is_termlit lit = RealTerm.is_termlit lit || IntTerm.is_termlit lit
  let of_termlit lit =
    if RealTerm.is_termlit lit then RealTerm.of_termlit lit
    else if IntTerm.is_termlit lit then IntTerm.of_termlit lit
    else assert false
  let assert_sort_check_of_theory sort lit =
    match sort, lit with
    | SReal, RealLit _ -> ()
    | SInt, IntLit _ -> ()
    | _ -> assert false
  let assert_sort_check = open_assert_sort_check assert_sort_check_of_theory
  let eval_sym = function
    | ToReal -> FunLit (function IntLit x -> RealLit (Q.of_bigint x) | _ -> assert false)
    | ToInt -> FunLit (function RealLit x -> IntLit (Q.to_bigint x) | _ -> assert false)
    | sym ->
      if Map.Poly.mem RealTerm.sym_sort_map sym then RealTerm.eval_sym sym
      else if Map.Poly.mem IntTerm.sym_sort_map sym then IntTerm.eval_sym sym
      else assert false
  let eval = open_eval eval_sym of_termlit
end

module type TupleTermType = sig
  include TermType

  type Sort.t += STuple of Sort.t list
  type sym += TupleCons of Sort.t list | TupleSel of Sort.t list * int

  val mk_tuple_cons : Sort.t list -> term
  val mk_tuple_sel : Sort.t list -> int -> term
  val is_tuple_cons : term -> bool
  val is_tuple_sel : term -> bool
  val mk_stuple : Sort.t list -> Sort.t
  val sorts_of : Sort.t -> Sort.t list
  val tuple_of : Sort.t list -> term list -> term
  val tuple_sel_of : Sort.t list -> term -> int -> term
  val let_tuple : term -> term list
  val let_stuple : Sort.t -> Sort.t list
end

module TupleTerm : TupleTermType = struct
  include Term

  type Sort.t += STuple of Sort.t list
  type sym += TupleCons of Sort.t list | TupleSel of Sort.t list * int

  let mk_tuple_cons sorts = Term.mk_con (TupleCons sorts)
  let mk_tuple_sel sorts i = Term.mk_con (TupleSel (sorts, i))
  let is_tuple_cons = function App (Con (TupleCons _, _), _, _) -> true | _ -> false
  let is_tuple_sel = function App (Con (TupleSel _, _), _, _) -> true | _ -> false
  let mk_stuple sorts = STuple sorts
  let sorts_of = function STuple sorts -> sorts | _ -> assert false
  let tuple_of sorts ts = Term.mk_apps (mk_tuple_cons sorts) ts
  let tuple_sel_of sorts term i = Term.mk_apps (mk_tuple_sel sorts i) [term]
  let let_tuple t = Term.let_apps t |> snd
  let let_stuple = function STuple sorts -> sorts | _ -> assert false
  let sort_of_sym = function
    | TupleCons sorts -> Sort.mk_fun (sorts @ [STuple sorts])
    | TupleSel (sorts, i) -> Sort.mk_fun (sorts @ [List.nth_exn sorts i])
    | _ -> failwith "TupleTerm.sort_of_sym"
  let str_of_sym = function
    | TupleCons _ -> sprintf "tuple"
    | TupleSel (_, i) -> sprintf "tuple.%d" i
    | _ -> failwith "TupleTerm.str_of_sym"
end

module type DatatypeType = sig
  type sel =
    | Sel of string * Sort.t
    | InSel of string * string * Sort.t list
  type cons =  {
    name : string;
    sels : sel list
  }
  type func = FCons of cons | FSel of sel
  type flag = FDt | FCodt | Undef | Alias of Sort.t
  type dt = {
    name : string;
    args : Sort.t list;
    conses : cons list
  }
  type t =  {
    name : string;
    dts : dt list;
    flag : flag
  }

  val mk_dt : string -> Sort.t list -> dt
  val create : string -> dt list -> flag -> t
  val mk_uninterpreted_datatype : ?numeral:int -> string -> t
  (* val mk_cons : ?sels:sel list -> string -> cons
     val mk_sel : string -> Sort.t -> sel
     val mk_insel : string -> string -> sel *)
  (* val mk_poly_sel : string -> int -> sel *)

  val update_name : t -> string -> t

  val dts_of : t -> dt list
  val name_of : t -> string
  val flag_of : t -> flag
  val name_of_dt : dt -> string
  val args_of_dt : dt -> Sort.t list
  val conses_of_dt : dt -> cons list
  val sels_of_cons : cons -> sel list
  val name_of_cons : cons -> string
  val name_of_sel : sel -> string
  val full_name_of : (Sort.t -> string) -> t -> string
  val full_name_of_dt : (Sort.t -> string) -> dt -> string

  val look_up_dt : t -> string -> dt option
  val look_up_cons : t -> string -> cons option
  val look_up_sel_of_cons : cons -> string -> sel option
  val look_up_sel : t -> string -> sel option
  val look_up_func : t -> string -> func option
  val look_up_base_cons : t -> cons option

  val dt_of : t -> dt
  val conses_of : t -> cons list
  val args_of : t -> Sort.t list

  val is_dt : t -> bool
  val is_codt : t -> bool
  val is_undef : t -> bool
  val is_alias : t -> bool

  val is_cons : func -> bool
  val is_sel : func -> bool

  val update_dts : dt list -> dt -> dt list
  val update_dt : t -> dt -> t
  val update_args : t -> Sort.t list -> t
  val update_conses : t -> cons list -> t

  val add_cons : t -> cons -> t
  val add_sel : cons -> sel -> cons

  val str_of_sel : sel -> string
  val str_of_cons : cons -> string
  val str_of_flag : flag -> string
  val str_of : t -> string

  val sort_of: t -> Sort.t
  val sort_of_sel : t -> sel -> Sort.t
  val sorts_of_cons_args : t -> cons -> Sort.t list

  val subst_sorts : (Ident.svar * Sort.t -> Sort.t -> Sort.t) -> Ident.svar * Sort.t -> dt -> dt

  val is_finite : t -> bool
  val is_singleton : Sort.t -> bool
  val fsym_of_cons : t -> cons -> sym
  val fsym_of_sel : t -> sel -> sym
  val fsym_of_func : t -> func -> sym

  val of_old_flag : LogicOld.Datatype.flag -> flag
  (* val of_old_sort : LogicOld.Sort.t -> Sort.t *)
  val of_old_sel : (LogicOld.Sort.t -> Sort.t) -> LogicOld.Datatype.sel -> sel
  val of_old_cons : (LogicOld.Sort.t -> Sort.t) ->  LogicOld.Datatype.cons -> cons
  val of_old_dt : (LogicOld.Sort.t -> Sort.t) -> LogicOld.Datatype.dt -> dt
  val of_old : (LogicOld.Sort.t -> Sort.t) -> LogicOld.Datatype.t -> t

  val to_old_flag : flag -> LogicOld.Datatype.flag
  (* val to_old_sort : Sort.t -> LogicOld.Sort.t *)
  val to_old_sel : (Sort.t -> LogicOld.Sort.t) ->  sel -> LogicOld.Datatype.sel
  val to_old_cons : (Sort.t -> LogicOld.Sort.t) -> cons -> LogicOld.Datatype.cons
  val to_old_dt : (Sort.t -> LogicOld.Sort.t) -> dt -> LogicOld.Datatype.dt
  val to_old : (Sort.t -> LogicOld.Sort.t) -> t -> LogicOld.Datatype.t
end

module type DatatypeTermType = sig
  include TermType

  type dt
  type dtcons
  type dtsel
  type flag
  type sym +=
    | DTSel of string * dt * Sort.t
    | DTCons of string * Sort.t list * dt
  type Sort.t +=
    | SDT of dt
    | SUS of string * (Sort.t list)

  val mk_sel : dt -> string  -> term
  val mk_cons : dt -> string -> term
  val mk_dummy : (Sort.t -> term) -> Sort.t -> term
  val is_dt : Sort.t -> bool
  val is_finite_dt : ?his:Sort.t list -> Sort.t -> bool
  val is_codt : Sort.t -> bool
  val is_undef : Sort.t -> bool
  val is_cons : term -> bool
  val is_sel : term -> bool
  val sels_of_cons : sym -> dtsel list
end

module rec Datatype : DatatypeType  = struct
  type sel =
    | Sel of string * Sort.t
    | InSel of string * string * Sort.t list
  type cons =  {
    name : string;
    sels : sel list
  }
  type func = FCons of cons | FSel of sel
  type flag = FDt | FCodt | Undef | Alias of Sort.t
  type dt = {
    name : string;
    args : Sort.t list;
    conses : cons list
  }
  type t = {
    name : string;
    dts : dt list;
    flag : flag
  }

  let mk_dt name args = {name = name; args = args; conses = []}
  let create name dts flag = {name = name; dts = dts; flag = flag}
  let mk_uninterpreted_datatype ?(numeral=0) name =
    let rec aux numeral =
      if numeral = 0 then []
      else Sort.SVar (Ident.mk_fresh_svar ()) :: (aux (numeral - 1))
    in
    create name [mk_dt name @@ aux numeral] Undef

  let update_name t name = {t with name = name}

  let dts_of t = t.dts
  let name_of t = t.name
  let flag_of t = t.flag
  let name_of_dt (dt:dt) = dt.name
  let args_of_dt (dt:dt) = dt.args
  let conses_of_dt (dt:dt) = dt.conses
  let sels_of_cons (cons:cons) = cons.sels
  let name_of_cons (cons:cons) = cons.name

  let is_dt t = match flag_of t with FDt  -> true | _ -> false
  let is_codt t = match flag_of t with FCodt  -> true | _ -> false
  let is_undef t = match flag_of t with Undef   -> true | _ -> false
  let is_alias t = match flag_of t with Alias _ -> true | _ -> false
  let is_cons = function FCons _ -> true | _ -> false
  let is_sel = function FSel _ -> true | _ -> false

  let name_of_sel = function Sel (name, _) | InSel (name, _, _) -> name
  let look_up_dt t name =
    List.find ~f:(fun dt -> Stdlib.(name = name_of_dt dt)) @@ dts_of t

  let dt_of t =
    match look_up_dt t @@ name_of t with
    | Some dt -> dt
    | _ -> assert false

  let conses_of t = dt_of t |> conses_of_dt
  let args_of t = dt_of t |> args_of_dt

  let full_name_of str_of_sort t =
    let name = name_of t in
    let args = args_of t in
    sprintf "%s %s" (String.concat_map_list ~sep:", " args ~f:str_of_sort) name
  let full_name_of_dt str_of_sort dt =
    let name = name_of_dt dt in
    let args = args_of_dt dt in
    sprintf "%s %s" (String.concat_map_list ~sep:", " args ~f:str_of_sort) name
  let rec update_dts dts dt =
    match dts with
    | [] -> []
    | dt1 :: tl ->
      if Stdlib.(name_of_dt dt1 = name_of_dt dt) then dt :: tl
      else dt1 :: update_dts tl dt

  let update_dt t dt = { t with dts = update_dts (dts_of t) dt }
  let rec update_dt_args t dt args his =
    let conses = conses_of_dt dt in
    let args1 = args_of_dt dt in
    let conses' =
      List.fold2_exn args1 args ~init:conses ~f:(fun conses arg1 arg ->
          List.map conses ~f:(fun cons ->
              let sels' = List.map (sels_of_cons cons) ~f:(function
                  | Sel (name, (Sort.SVar _ as svar)) when Stdlib.(svar = arg1) ->
                    begin match arg with
                      | DatatypeTerm.SDT t1 ->
                        begin match look_up_dt t (name_of t1) with
                          | Some _ -> InSel (name, name_of t1, args_of t1)
                          | _ -> Sel (name, arg)
                        end
                      | _ -> Sel (name, arg)
                    end
                  | InSel (name, ret_name, args) ->
                    let args' = List.map args ~f:(fun svar -> if Stdlib.(svar = arg1) then arg else svar) in
                    InSel (name, ret_name, args')
                  | sel -> sel)
              in
              { cons with sels = sels' }))
    in
    let t' =
      List.fold_left conses' ~init:t ~f:(fun t cons ->
          List.fold_left (sels_of_cons cons) ~init:t ~f:(fun t -> function
              | Sel _ -> t
              | InSel (_, ret_sort, args) ->
                if not @@ List.exists his ~f:(Stdlib.(=) ret_sort) then
                  let t', dt' =
                    update_dt_args (update_name t ret_sort) (dt_of @@ update_name t ret_sort) args (ret_sort :: his)
                  in
                  update_name (update_dt t' dt') (name_of t)
                else t))
    in
    t', {dt with args = args ; conses = conses'}
  and update_args t args =
    let dt = dt_of t in
    let t', dt' = update_dt_args t dt args [name_of t] in
    let ret = update_dt t' dt' in
    ret
  let update_conses t conses = update_dt t {(dt_of t) with conses = conses}

  let add_cons t cons =
    let dt = dt_of t in
    let conses = conses_of_dt dt in
    update_dt t {dt with conses = cons :: conses}

  let add_sel cons sel =
    let sels = sels_of_cons cons in
    {cons with sels = sel::sels}

  let look_up_cons t name =
    conses_of t |>
    List.find ~f:(fun cons -> Stdlib.(name = name_of_cons cons))

  let look_up_sel_of_cons cons name =
    sels_of_cons cons |>
    List.find ~f:(fun sel -> Stdlib.(name = name_of_sel sel))

  let look_up_sel t name =
    conses_of t |>
    List.fold_left ~init:None ~f:(fun ret cons ->
        match ret with
        | None -> sels_of_cons cons |>
                  List.find ~f:(fun sel -> Stdlib.(name = name_of_sel sel))
        | _ -> ret)

  let look_up_func t name =
    match look_up_cons t name with
    | Some cons -> Some (FCons cons)
    | None ->
      match look_up_sel t name with
      | Some sel -> Some (FSel sel)
      | None -> None

  let str_of_sel = function
    | Sel (name, ret_sort) ->
      sprintf "%s:%s" name (Term.str_of_sort ret_sort)
    | InSel (name, ret_name, args) ->
      String.concat ~sep:"_" @@
      sprintf "%s:%s" name ret_name :: List.map args ~f:Term.str_of_sort

  let str_of_cons cons =
    let name = name_of_cons cons in
    let sels = sels_of_cons cons in
    String.concat ~sep:" " @@ name :: List.map sels ~f:str_of_sel

  let str_of_flag = function FCodt -> "codt" | FDt -> "dt" | Undef -> "undef" | Alias _ -> "alias"

  let str_of t =
    let dt = dt_of t in
    sprintf "(%s:%s%s) %s"
      (str_of_flag @@ flag_of t)
      (name_of t)
      (String.concat_map_list ~sep:" " (args_of_dt dt) ~f:Term.str_of_sort)
      (String.concat_map_list ~sep:"\n| " (conses_of_dt dt) ~f:str_of_cons)

  let sort_of t =
    match flag_of t with
    | Undef -> DatatypeTerm.SUS (name_of t, args_of t)
    | _ -> DatatypeTerm.SDT t
  let sort_of_sel t = function
    | Sel (_, sort) -> sort
    | InSel (_, ret_name, args) ->
      match look_up_dt t ret_name with
      | Some _ -> sort_of @@ update_args (update_name t ret_name) args
      | None -> failwith @@ sprintf "unknown sort:%s" ret_name

  let sorts_of_cons_args t cons=
    sels_of_cons cons |>
    List.map ~f:(fun sel -> sort_of_sel t sel)

  let subst_sorts subst_sort (svar, sort) dt =
    { dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            { cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                    | InSel (name, ret_name, args) ->
                      InSel (name, ret_name, List.map args ~f:(subst_sort (svar, sort)))
                    | Sel (name, ret_sort) ->
                      Sel (name, subst_sort (svar, sort) ret_sort)) });
      args = List.map (args_of_dt dt) ~f:(subst_sort (svar, sort)) }

  let is_finite t =
    not @@ List.exists (conses_of t) ~f:(fun cons ->
        List.for_all (sorts_of_cons_args t cons) ~f:(fun arg ->
            Stdlib.(arg = DatatypeTerm.SDT t) && DatatypeTerm.is_finite_dt arg))

  let rec is_singleton = function
    | DatatypeTerm.SDT t as sort -> begin
        match conses_of t with
        | [cons] ->
          List.for_all (sorts_of_cons_args t cons) ~f:(fun arg -> Stdlib.(arg = sort) || is_singleton arg)
        | _ -> false
      end
    | _ -> false

  (*let fresh_of t =
    let dts = dts_of t in
    let dts' =
      List.map dts ~f:(fun dt ->
          let args = args_of_dt dt in
          let args' = List.map args ~f:(function Sort.SVar _ -> Sort.SVar (Ident.mk_fresh_svar ()) | arg -> arg) in
          snd @@ update_dt_args t dt args' [])
    in
    { t with dts = dts' }*)

  let fsym_of_cons t cons =
    (*let t = fresh_of t in*)
    match look_up_cons t @@ name_of_cons cons with
    | Some cons -> DatatypeTerm.DTCons (name_of_cons cons, sorts_of_cons_args t cons, t)
    | None -> assert false

  let fsym_of_sel t sel =
    (*let t = fresh_of t in*)
    match look_up_sel t @@ name_of_sel sel with
    | None -> assert false
    | Some sel ->
      match sel with
      | Sel (name, ret_sort) -> DatatypeTerm.DTSel (name, t, ret_sort)
      | InSel (name, ret_name, args) ->
        match look_up_dt t ret_name with
        | Some _ -> DatatypeTerm.DTSel (name, t, sort_of @@ update_args (update_name t ret_name) args)
        | None -> failwith @@ sprintf "unknown dt sort:%s" ret_name

  let fsym_of_func t = function
    | FCons cons -> fsym_of_cons t cons
    | FSel sel -> fsym_of_sel t sel

  let rec of_old_flag = function
    | LogicOld.Datatype.FDt -> FDt
    | LogicOld.Datatype.FCodt -> FCodt
    | LogicOld.Datatype.Undef -> Undef
    | LogicOld.Datatype.Alias _ -> assert false
  and of_old_sel of_old_sort = function
    | LogicOld.Datatype.Sel (name, ret_sort) ->
      Sel (name, of_old_sort ret_sort)
    | LogicOld.Datatype.InSel (name, ret_name, args) ->
      InSel (name, ret_name, List.map args ~f:of_old_sort)
  and of_old_cons of_old_sort old_cons =
    let name = LogicOld.Datatype.name_of_cons old_cons in
    let sels = LogicOld.Datatype.sels_of_cons old_cons in
    { name = name; sels = List.map sels ~f:(of_old_sel of_old_sort) }
  and of_old_dt of_old_sort old_dt =
    let name = LogicOld.Datatype.name_of_dt old_dt in
    let conses = LogicOld.Datatype.conses_of_dt old_dt in
    let args = LogicOld.Datatype.args_of_dt old_dt in
    { name = name;
      conses = List.map conses ~f:(of_old_cons of_old_sort);
      args = List.map args ~f:of_old_sort }
  and of_old of_old_sort old_t =
    let dts = LogicOld.Datatype.dts_of old_t in
    let name = LogicOld.Datatype.name_of old_t in
    let flag = LogicOld.Datatype.flag_of old_t in
    { name = name;
      flag = of_old_flag flag;
      dts = List.map dts ~f:(of_old_dt of_old_sort) }

  let rec to_old_flag = function
    | FDt -> LogicOld.Datatype.FDt
    | FCodt -> LogicOld.Datatype.FCodt
    | Undef -> LogicOld.Datatype.Undef
    | Alias _ -> assert false
  and to_old_sel to_old_sort = function
    | Sel (name, ret_sort) ->
      LogicOld.Datatype.Sel (name, to_old_sort ret_sort)
    | InSel (name, ret_name, args) ->
      LogicOld.Datatype.InSel (name, ret_name, List.map args ~f:to_old_sort)
  and to_old_cons to_old_sort cons =
    let name = name_of_cons cons in
    let sels = sels_of_cons cons |> List.map ~f:(to_old_sel to_old_sort) in
    LogicOld.Datatype.mk_cons name ~sels
  and to_old_dt to_old_sort dt =
    let name = name_of_dt dt in
    let conses = conses_of_dt dt |> List.map ~f:(to_old_cons to_old_sort) in
    let args = args_of_dt dt |> List.map ~f:to_old_sort in
    { (LogicOld.Datatype.mk_dt name args) with conses = conses }
  and to_old to_old_sort t =
    let dts = dts_of t in
    let name = name_of t in
    let flag = flag_of t in
    LogicOld.Datatype.create name (List.map dts ~f:(to_old_dt to_old_sort)) (to_old_flag flag)

  let look_up_base_cons t =
    let has_direct_base t =
      let conses = conses_of t in
      List.exists conses ~f:(fun cons ->
          List.for_all (sels_of_cons cons) ~f:(function Sel _ -> true | InSel _ -> false))
    in
    let rec look_up_other_base t his=
      if List.exists his ~f:(fun t1 -> Stdlib.(name_of t = name_of t1)) then None
      else
        List.find (conses_of t) ~f:(fun cons ->
            let sels = sels_of_cons cons in
            List.for_all sels ~f:(function
                | Sel _ -> true
                | InSel (_, ret_name, _) ->
                  let ret_dt = update_name t ret_name in
                  if has_direct_base ret_dt then true
                  else Option.is_some @@ look_up_other_base ret_dt (t :: his)))
    in
    List.find (conses_of t) ~f:(fun cons ->
        List.for_all (sels_of_cons cons) ~f:(function
            | Sel _ -> true
            | InSel (_, ret_name, _) ->
              Option.is_some @@ look_up_other_base (update_name t ret_name) [t]))
end
and DatatypeTerm : DatatypeTermType
  with type dt := Datatype.t
   and type dtcons := Datatype.cons
   and type dtsel := Datatype.sel
   and type flag := Datatype.flag
= struct
  include Term

  type sym +=
    | DTSel of string * Datatype.t * Sort.t
    | DTCons of string * Sort.t list * Datatype.t
  type Sort.t +=
    | SDT of Datatype.t
    | SUS of string * (Sort.t list)

  let mk_cons dt name  =
    match Datatype.look_up_cons dt name with
    | Some cons -> Term.mk_con @@ Datatype.fsym_of_cons dt cons
    | _ -> failwith @@ "unknown cons :" ^ name

  let mk_sel dt name =
    match Datatype.look_up_sel dt name with
    | Some sel -> Term.mk_con @@ Datatype.fsym_of_sel dt sel
    | _ -> failwith @@ "unknown sel :" ^ name

  let sels_of_cons = function
    | DTCons (name, _, dt) ->
      (match Datatype.look_up_cons dt name with
       | Some cons -> Datatype.sels_of_cons cons
       | _ -> assert false)
    | _ -> assert false

  let is_dt = function SDT dt -> Datatype.is_dt dt | _ -> false
  let is_codt = function SDT dt -> Datatype.is_dt dt | _ -> false
  let is_undef = function SUS (_, _) -> true | _ -> false

  let rec is_finite_dt ?(his=[]) sort =
    if List.exists his ~f:(Stdlib.(=) sort) then false
    else
      match sort with
      | SDT dt ->
        List.for_all (Datatype.conses_of dt) ~f:(fun cons ->
            Datatype.sorts_of_cons_args dt cons
            |> List.for_all ~f:(fun arg -> is_finite_dt ~his:(sort::his) arg))
      | _ -> false

  let is_cons = function App (Con (DTCons _, _), _, _) -> true | _ -> false
  let is_sel = function App (Con (DTSel _, _), _, _) -> true | _ -> false

  let sort_of_sym = function
    | DTSel (_, dt, sort) -> Sort.mk_arrow (SDT dt) sort
    | DTCons (_, sorts, dt) -> Sort.mk_fun @@ sorts @ [SDT dt]
    | _ -> failwith "DatatypeTerm.sort_of_sym"
  let str_of_sym = function
    | DTSel (name, _, _) -> name
    | DTCons (name, _, _) -> name
    | _ -> failwith "DatatypeTerm.str_of_sym"

  let mk_dummy f = function
    | SDT dt when Datatype.is_dt dt->
      begin match Datatype.look_up_base_cons dt with
        | Some cons ->
          mk_apps (mk_cons dt @@ Datatype.name_of_cons cons) @@
          List.map ~f @@ Datatype.sorts_of_cons_args dt cons
        | None -> assert false
      end
    | SUS (name, _) -> mk_var @@ Ident.Tvar ("dummy_" ^ name)
    | sort -> f sort
end

module type ArrayTermType = sig
  include TermType

  type sym +=
    | AStore of Sort.t * Sort.t
    | ASelect of Sort.t * Sort.t
    | AConst of Sort.t * Sort.t
  type Sort.t += SArray of Sort.t * Sort.t

  val mk_array_sort : Sort.t -> Sort.t -> Sort.t
  val mk_select : Sort.t -> Sort.t -> term
  val mk_store : Sort.t -> Sort.t -> term
  val mk_const_array : Sort.t -> Sort.t -> term
  val index_sort_of : Sort.t -> Sort.t
  val elem_sort_of : Sort.t -> Sort.t
end

module ArrayTerm : ArrayTermType = struct
  include Term

  type sym +=
    | AStore of Sort.t * Sort.t
    | ASelect of Sort.t * Sort.t
    | AConst of Sort.t * Sort.t
  type Sort.t += SArray of Sort.t * Sort.t

  let mk_array_sort s1 s2 = SArray (s1, s2)
  let mk_select s1 s2 = Term.mk_con (ASelect (s1, s2))
  let mk_store s1 s2 = Term.mk_con (AStore (s1, s2))

  let mk_const_array s1 s2 = Term.mk_con (AConst (s1, s2))

  let index_sort_of = function SArray (si, _) -> si | _ -> failwith "not array sort"

  let elem_sort_of = function SArray (_, se) -> se | _ -> failwith "not array sort"

  let sort_of_sym = function
    | AStore (s1, s2) -> Sort.mk_fun [SArray (s1, s2); s1; s2; SArray (s1, s2)]
    | ASelect (s1, s2) -> Sort.mk_fun [SArray (s1, s2); s1; s2]
    | AConst (s1, s2) -> Sort.mk_fun [s2; SArray (s1, s2)]
    | _ -> failwith "ArrayTerm.sort_of_sym"
  let str_of_sym = function
    | AStore _ -> "store"
    | ASelect _ -> "select"
    | AConst _ -> "array_const"
    | _ -> failwith "ArrayTerm.str_of_sym"
end

module type StringTermType = sig
  include TermType

  type Sort.t += SString
  type sym += StringConst of string

  val mk_string_const : string -> term
  val let_string_const : term -> string * info
end

module StringTerm : StringTermType = struct
  include Term

  type Sort.t += SString
  type sym += StringConst of string

  let mk_string_const str = Term.mk_sym_app (StringConst str) []
  let let_string_const = function Con (StringConst str, info) -> str, info | _ -> assert false

  let sort_of_sym = function
    | StringConst _ -> SString
    | _ -> failwith "StringTerm.sort_of_sym"
  let str_of_sym = function
    | StringConst str -> sprintf "\"%s\"" str
    | _ -> failwith "StringTerm.str_of_sym"
end

module type SequenceTermType = sig
  include TermType

  type Sort.t += SFinSequence | SInfSequence
  type sym +=
    | Epsilon | Symbol of string | Concat of bool | LeftQuotient of bool | RightQuotient of bool
end

module SequenceTerm : SequenceTermType = struct
  include Term

  type Sort.t += SFinSequence | SInfSequence
  type sym +=
    | Epsilon | Symbol of string | Concat of bool(* the first argument must be finite *) | LeftQuotient of bool(* the first argument must be finite *) | RightQuotient of bool(* the first argument must be finite *)

  let sort_of_sym = function
    | Epsilon -> SFinSequence
    | Symbol _ev -> SFinSequence
    | Concat fin -> if fin then SFinSequence else SInfSequence
    | LeftQuotient fin -> if fin then SFinSequence else SInfSequence
    | RightQuotient fin -> if fin then SFinSequence else SInfSequence
    | _ -> failwith "SequenceTerm.sort_of_sym"
  let str_of_sym = function
    | Epsilon -> "eps"
    | Symbol ev -> ev
    | Concat fin -> "concat" ^ if fin then "_fin" else "_inf"
    | LeftQuotient _ -> "left_quot"
    | RightQuotient _ -> "right_quot"
    | _ -> failwith "SequenceTerm.str_of_sym"
end

module type ExtTermType = sig
  include BoolTermType
  include RealIntTermType
  include TupleTermType
  include DatatypeTermType
  include ArrayTermType
  include StringTermType
  include SequenceTermType

  type sym +=
    | Leq | Geq | Lt | Gt | PDiv
    | RLeq | RGeq | RLt | RGt | IsInt
    | IsTuple of Sort.t list | NotIsTuple of Sort.t list
    | IsCons of string * Datatype.t | NotIsCons of string * Datatype.t
    | IsPrefix of bool | NotIsPrefix of bool | InRegExp of bool * string Grammar.RegWordExp.t | NotInRegExp of bool * string Grammar.RegWordExp.t

  (** Construction *)
  val mk_dummy: Sort.t -> term
  val mk_leq: unit -> term
  val mk_geq: unit -> term
  val mk_lt: unit -> term
  val mk_gt: unit -> term
  val mk_pdiv: unit -> term
  val mk_isint: unit -> term
  val mk_int_ite: unit -> term
  val mk_real_ite: unit -> term
  val mk_int_eq: unit -> term
  val mk_real_eq: unit -> term
  val mk_int_neq: unit -> term
  val mk_real_neq: unit -> term
  val mk_is_cons : string -> Datatype.t -> term

  val leq_of: term -> term -> term
  val geq_of: term -> term -> term
  val lt_of: term -> term -> term
  val gt_of: term -> term -> term

  (** Observation*)
  val svs_of_sym : sym -> Ident.svar Set.Poly.t 
  val svs_of_sort : Sort.t -> Ident.svar Set.Poly.t
  val sort_of: sort_env_map -> term -> Sort.t

  (** Conversion *)
  val of_old_sort: LogicOld.Sort.t -> Sort.t
  val of_old_sort_bind: Ident.tvar * LogicOld.Sort.t -> sort_bind
  val of_old_sort_env: LogicOld.sort_env_list -> sort_env_list
  val to_old_sort: Sort.t -> LogicOld.Sort.t
  val to_old_sort_bind: sort_bind -> Ident.tvar * LogicOld.Sort.t

  val of_old_term: LogicOld.Term.t -> term
  val of_old_atom: LogicOld.Atom.t -> term
  val of_old_formula: LogicOld.Formula.t -> term

  val to_old_term: sort_env_map -> sort_env_map -> term -> term list -> LogicOld.Term.t
  val to_old_atom: sort_env_map -> sort_env_map -> term -> term list -> LogicOld.Atom.t
  val to_old_formula: sort_env_map -> sort_env_map -> term -> term list -> LogicOld.Formula.t
  val to_old_subst: sort_env_map -> sort_env_map -> term_subst_map -> LogicOld.TermSubst.t

  val remove_dontcare_elem: model_elem -> term_bind
  val remove_dontcare: model -> term_bind list

  val str_of_formula : sort_env_map -> sort_env_map -> term -> string
  val str_of_term : sort_env_map -> sort_env_map -> term -> string

  val simplify_formula : sort_env_map -> sort_env_map -> term -> term
  val simplify_term : sort_env_map -> sort_env_map -> term -> term
end

module ExtTerm : ExtTermType
  with type dt := Datatype.t
   and type dtcons := Datatype.cons
   and type dtsel := Datatype.sel
   and type flag := Datatype.flag
= struct
  include BoolTerm
  include RealIntTerm
  include TupleTerm
  include DatatypeTerm
  include ArrayTerm
  include StringTerm
  include SequenceTerm

  type sym +=
    | Leq | Geq | Lt | Gt | PDiv
    | RLeq | RGeq | RLt | RGt | IsInt
    | IsTuple of Sort.t list | NotIsTuple of Sort.t list
    | IsCons of string * Datatype.t | NotIsCons of string * Datatype.t
    | IsPrefix of bool | NotIsPrefix of bool | InRegExp of bool * string Grammar.RegWordExp.t | NotInRegExp of bool * string Grammar.RegWordExp.t

  (** Construction *)
  let rec mk_dummy sort = match sort with
    | SBool -> BoolTerm.mk_bool false
    | SInt -> IntTerm.zero ()
    | SReal -> RealTerm.rzero ()
    | STuple sorts -> mk_apps (mk_tuple_cons sorts) @@ List.map sorts ~f:mk_dummy
    | SDT _ | SUS _ -> DatatypeTerm.mk_dummy mk_dummy sort
    | SArray (s1, s2) -> mk_app (mk_const_array s1 s2) (mk_dummy s2)
    | SString -> mk_con @@ StringConst ""
    | SFinSequence -> mk_con Epsilon
    | SInfSequence -> failwith "SInfSequence @ SArrow"
    | Sort.SArrow _ -> failwith "SArrow @ mk_dummy"
    | _ -> failwith @@ "unknown sort"
  let mk_leq () = mk_con Leq
  let mk_geq () = mk_con Geq
  let mk_lt () = mk_con Lt
  let mk_gt () = mk_con Gt
  let mk_pdiv () = mk_con PDiv
  let mk_rleq () = mk_con RLeq
  let mk_rgeq () = mk_con RGeq
  let mk_rlt () = mk_con RLt
  let mk_rgt () = mk_con RGt
  let mk_isint () = mk_con IsInt
  let mk_int_ite () = mk_ite SInt
  let mk_real_ite () = mk_ite SReal
  let mk_int_eq () = mk_eq SInt
  let mk_real_eq () = mk_eq SReal
  let mk_int_neq () = mk_neq SInt
  let mk_real_neq () = mk_neq SReal
  let mk_is_tuple sorts = mk_con (IsTuple sorts)
  let mk_is_not_tuple sorts = mk_con (NotIsTuple sorts)
  let mk_is_cons name dt = mk_con (IsCons (name, dt))
  let mk_is_not_cons name dt = mk_con (NotIsCons (name, dt))

  let leq_of t1 t2 = mk_apps (mk_leq ()) [t1; t2]
  let geq_of t1 t2 = mk_apps (mk_geq ()) [t1; t2]
  let lt_of t1 t2 = mk_apps (mk_lt ()) [t1; t2]
  let gt_of t1 t2 = mk_apps (mk_gt ()) [t1; t2]

  (** Sorts *)
  let iib = Sort.mk_arrow SInt @@ Sort.mk_arrow SInt SBool
  let rrb = Sort.mk_arrow SReal @@ Sort.mk_arrow SReal SBool
  let rb = Sort.mk_arrow SReal SBool
  let sym_sort_map =
    Map.force_merge (Map.force_merge RealIntTerm.sym_sort_map BoolTerm.sym_sort_map) @@
    Map.Poly.of_alist_exn @@
    [ (Leq, iib); (Geq, iib); (Lt, iib); (Gt, iib); (PDiv, iib);
      (RLeq, rrb); (RGeq, rrb); (RLt, rrb); (RGt, rrb); (IsInt, rb) ]
  let sort_of_sym = function
    | IsTuple sorts | NotIsTuple sorts ->
      Sort.mk_arrow (TupleTerm.STuple sorts) BoolTerm.SBool
    | IsCons (_, dt) | NotIsCons (_, dt) ->
      Sort.mk_arrow (DatatypeTerm.SDT dt) BoolTerm.SBool
    | IsPrefix fin | NotIsPrefix fin ->
      let sort = if fin then SequenceTerm.SFinSequence else SequenceTerm.SInfSequence in
      Sort.mk_arrow SequenceTerm.SFinSequence @@ Sort.mk_arrow sort BoolTerm.SBool
    | InRegExp (fin, _regexp) | NotInRegExp (fin, _regexp) ->
      let sort = if fin then SequenceTerm.SFinSequence else SequenceTerm.SInfSequence in
      Sort.mk_arrow sort BoolTerm.SBool
    | sym ->
      try Map.Poly.find_exn sym_sort_map sym with _ ->
      try BoolTerm.sort_of_sym sym with _ ->
      try RealIntTerm.sort_of_sym sym with _ ->
      try TupleTerm.sort_of_sym sym with _ ->
      try DatatypeTerm.sort_of_sym sym with _ ->
      try ArrayTerm.sort_of_sym sym with _ ->
      try StringTerm.sort_of_sym sym with _ ->
      try SequenceTerm.sort_of_sym sym with _ ->
        failwith "ExtTerm.sort_of_sym"
  let rec svs_of_sort = function
    | Sort.SVar svar -> Set.Poly.singleton svar
    | Sort.SArrow (s1, (o, s2, c)) ->
      Set.Poly.union_list [svs_of_sort s1; svs_of_opsig o; svs_of_sort s2; svs_of_cont c]
    | Sort.SForAll (svar, s1) ->
      Set.Poly.remove (svs_of_sort s1) svar
    | SBool | SInt | SReal | SString | SFinSequence | SInfSequence -> Set.Poly.empty
    | STuple sorts ->
      Set.Poly.union_list @@ List.map sorts ~f:svs_of_sort
    | SDT dt ->
      Set.Poly.union_list @@ List.map (Datatype.args_of dt) ~f:svs_of_sort
    | SUS (_, sorts) ->
      Set.Poly.union_list @@ List.map sorts ~f:svs_of_sort
    | SArray (s1, s2) ->
      Set.Poly.union_list @@ List.map [s1; s2] ~f:svs_of_sort
    | _ -> failwith "[ExtTerm.svs_of_sort] unknown sort"
  and svs_of_cont = function
    | Sort.EVar _  | Sort.Pure -> Set.Poly.empty
    | Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      Set.Poly.union_list [svs_of_opsig o1; svs_of_sort s1; svs_of_cont e1;
                           svs_of_opsig o2; svs_of_sort s2; svs_of_cont e2]
    | _ -> failwith "[svs_of_cont]"
  and svs_of_opsig = function
    | Sort.OpSig (opmap, _) ->
      Set.Poly.union_list @@ List.map ~f:snd @@ ALMap.map opmap ~f:svs_of_sort
    | _ -> failwith "[svs_of_opsig]"

  let rec subst_sorts_cont (svar, sort) = function
    | Sort.EVar x -> Sort.EVar x
    | Sort.Pure -> Sort.Pure
    | Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      Sort.Eff (subst_sorts_opsig (svar, sort) o1,
                subst_sorts_sort (svar, sort) s1,
                subst_sorts_cont (svar, sort) e1,
                subst_sorts_opsig (svar, sort) o2,
                subst_sorts_sort (svar, sort) s2,
                subst_sorts_cont (svar, sort) e2)
    | _ -> failwith "[subst_sorts_cont]"
  and subst_sorts_sort (svar, sort) = function
    | Sort.SVar v when Stdlib.(v = svar) -> sort
    | Sort.SArrow (s1, (o, s2, e)) ->
      Sort.SArrow (subst_sorts_sort (svar, sort) s1,
                   (subst_sorts_opsig (svar, sort) o,
                    subst_sorts_sort (svar, sort) s2,
                    subst_sorts_cont (svar, sort) e))
    | Sort.SForAll (svar', s1) ->
      if Stdlib.(svar' = svar) then Sort.SForAll (svar', s1)
      else Sort.SForAll (svar', subst_sorts_sort (svar, sort) s1)
    | (SBool | SInt | SReal | SString | SFinSequence | SInfSequence) as sort -> sort
    | STuple sorts -> STuple (List.map ~f:(subst_sorts_sort (svar, sort)) sorts)
    | SDT dt ->
      SDT (Datatype.update_dt dt (Datatype.subst_sorts subst_sorts_sort (svar, sort) (Datatype.dt_of dt)))
    | SUS (name, sorts) -> SUS (name, List.map ~f:(subst_sorts_sort (svar, sort)) sorts)
    | SArray (s1, s2) -> SArray (subst_sorts_sort (svar, sort) s1, subst_sorts_sort (svar, sort) s2)
    | _ -> sort(*failwith "[subst_sorts_sort]"*)
  and subst_sorts_opsig (svar, sort) = function
    | Sort.OpSig (opmap, r) ->
      Sort.OpSig (ALMap.map opmap ~f:(subst_sorts_sort (svar, sort)), r)
    | _ -> failwith "[subst_sorts_opsig]"

  let svs_of_sym sym = svs_of_sort @@ sort_of_sym sym
  let arity_of_sym = Term.open_arity_of_sym sort_of_sym
  let sort_of = Term.open_sort_of sort_of_sym subst_sorts_sort

  (** Printing *)
  let str_of_sym = function
    | Leq -> "Leq" | Geq -> "Geq" | Lt -> "Lt" | Gt -> "Gt" | PDiv -> "PDiv"
    | RLeq -> "RLeq" | RGeq -> "RGeq" | RLt -> "RLt" | RGt -> "RGt" | IsInt -> "IsInt"
    | IsTuple sorts ->
      sprintf "is_tuple(%s)" (String.concat_map_list ~sep:" * " sorts ~f:str_of_sort)
    | NotIsTuple sorts ->
      sprintf "is_not_tuple(%s)" (String.concat_map_list ~sep:" * " sorts ~f:str_of_sort)
    | IsCons (name, _) -> sprintf "is_%s" name
    | NotIsCons (name, _) -> sprintf "is_not_%s" name
    | IsPrefix _fin -> "is_prefix" | NotIsPrefix _fin -> "not is_prefix"
    | InRegExp (_fin, regexp) ->
      sprintf "in [%s]" @@ Grammar.RegWordExp.str_of Fn.id regexp
    | NotInRegExp (_fin, regexp) ->
      sprintf "not in [%s]" @@ Grammar.RegWordExp.str_of Fn.id regexp
    | sym ->
      try BoolTerm.str_of_sym sym with _ ->
      try RealIntTerm.str_of_sym sym with _ ->
      try TupleTerm.str_of_sym sym with _ ->
      try DatatypeTerm.str_of_sym sym with _ ->
      try ArrayTerm.str_of_sym sym with _ ->
      try StringTerm.str_of_sym sym with _ ->
      try SequenceTerm.str_of_sym sym with _ ->
        failwith "[ExtTerm.str_of_sym]"
  let str_of_termlit = function
    | BoolLit true -> "true"
    | BoolLit false -> "false"
    | IntLit n -> Z.to_string n
    | RealLit r -> Q.to_string r
    | _ -> assert false
  let rec str_of_sort_theory = function
    | Sort.SVar (Ident.Svar svar) -> sprintf "'%s" svar
    | Sort.SArrow (s1, (o, s2, c)) ->
      (if Sort.is_empty_opsig o then "" else "_ |> ") ^
      (if Sort.is_arrow s1 then
         sprintf "(%s)" @@ open_str_of_sort str_of_sort_theory s1
       else
         open_str_of_sort str_of_sort_theory s1) ^
      " -> " ^ open_str_of_sort str_of_sort_theory s2 ^
      if Stdlib.(c = Sort.Pure) then "" else " / _"
    | SBool -> "bool"
    | SInt -> "int"
    | SReal -> "real"
    | STuple sorts ->
      sprintf "(%s)" @@
      String.concat_map_list ~sep:" * " sorts ~f:(open_str_of_sort str_of_sort_theory)
    | SDT dt ->
      Datatype.full_name_of (open_str_of_sort str_of_sort_theory) dt
    | SUS (name, _) -> name
    | SArray (s1, s2) ->
      (match s1 with
       | SArray _ -> sprintf "(%s)" @@ open_str_of_sort str_of_sort_theory s1
       | _ -> open_str_of_sort str_of_sort_theory s1) ^
      " -a> " ^ open_str_of_sort str_of_sort_theory s2
    | SString -> "string"
    | SFinSequence -> "fin_sequence"
    | SInfSequence -> "inf_sequence"
    | _ -> failwith "[ExtTerm.str_of_sort_theory] unknown sort"
  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym

  (** Evaluation *)
  let is_termlit = function
    | BoolTerm.BoolLit _ | IntTerm.IntLit _ | RealTerm.RealLit _ -> true | _ -> false
  let of_termlit lit =
    if BoolTerm.is_termlit lit then BoolTerm.of_termlit lit
    else if RealTerm.is_termlit lit then RealTerm.of_termlit lit
    else if IntTerm.is_termlit lit then IntTerm.of_termlit lit
    else assert false
  let assert_sort_check_of_theory sort lit =
    match sort, lit with
    | SBool, BoolLit _ -> ()
    | SReal, RealLit _ -> ()
    | SInt, IntLit _ -> ()
    | _ -> assert false
  let assert_sort_check = open_assert_sort_check assert_sort_check_of_theory
  let eval_sym = function
    | Leq ->
      FunLit (function
          | IntLit x -> FunLit (function IntLit y -> BoolLit (Z.Compare.(<=) x y) | _ -> assert false)
          | _ -> assert false)
    | Geq ->
      FunLit (function
          | IntLit x -> FunLit (function IntLit y -> BoolLit (Z.Compare.(>=) x y) | _ -> assert false)
          | _ -> assert false)
    | Lt ->
      FunLit (function
          | IntLit x -> FunLit (function IntLit y -> BoolLit (Z.Compare.(<) x y) | _ -> assert false)
          | _ -> assert false)
    | Gt ->
      FunLit (function
          | IntLit x -> FunLit (function IntLit y -> BoolLit (Z.Compare.(>) x y) | _ -> assert false)
          | _ -> assert false)
    | PDiv ->
      FunLit (function
          | IntLit x -> FunLit (function IntLit y -> BoolLit (Z.Compare.(=) (Z.(mod) x y) Z.zero)
                                       | _ -> assert false)
          | _ -> assert false)
    | RLeq ->
      FunLit (function
          | RealLit x -> FunLit (function RealLit y -> BoolLit (Q.(<=) x y) | _ -> assert false)
          | _ -> assert false)
    | RGeq ->
      FunLit (function
          | RealLit x -> FunLit (function RealLit y -> BoolLit (Q.(>=) x y) | _ -> assert false)
          | _ -> assert false)
    | RLt ->
      FunLit (function
          | RealLit x -> FunLit (function RealLit y -> BoolLit (Q.(<) x y) | _ -> assert false)
          | _ -> assert false)
    | RGt ->
      FunLit (function
          | RealLit x -> FunLit (function RealLit y -> BoolLit (Q.(>) x y) | _ -> assert false)
          | _ -> assert false)
    | IsInt ->
      FunLit (function
          | RealLit x -> BoolLit (Z.Compare.(=) (Z.(mod) (Q.num x) (Q.den x)) Z.zero) | _ -> assert false)
    | sym ->
      if Map.Poly.mem BoolTerm.sym_sort_map sym then BoolTerm.eval_sym sym
      else if Map.Poly.mem RealIntTerm.sym_sort_map sym then RealIntTerm.eval_sym sym
      else assert false
  let eval = open_eval eval_sym of_termlit

  (** Conversion *)

  let rec of_old_cont = function
    | LogicOld.Sort.EVar x -> Sort.EVar x
    | LogicOld.Sort.Pure -> Sort.Pure
    | LogicOld.Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      Sort.Eff (of_old_opsig o1, of_old_sort s1, of_old_cont e1,
                of_old_opsig o2, of_old_sort s2, of_old_cont e2)
    | _ -> failwith "[of_old_cont]"
  and of_old_sort = function
    | LogicOld.Sort.SVar svar -> Sort.SVar svar
    | LogicOld.Sort.SArrow (s1, (o, s2, e)) ->
      Sort.SArrow (of_old_sort s1, (of_old_opsig o, of_old_sort s2, of_old_cont e))
    | LogicOld.T_bool.SBool -> SBool
    | LogicOld.T_int.SInt -> SInt
    | LogicOld.T_real.SReal -> SReal
    | LogicOld.T_tuple.STuple sorts -> STuple (List.map sorts ~f:of_old_sort)
    | LogicOld.T_dt.SDT dt -> SDT (Datatype.of_old of_old_sort dt)
    | LogicOld.T_dt.SUS (name, args) -> SUS (name, List.map args ~f:of_old_sort)
    | LogicOld.T_array.SArray (s1, s2) -> SArray (of_old_sort s1, of_old_sort s2)
    | LogicOld.T_string.SString -> SString
    | LogicOld.T_sequence.SFinSequence -> SFinSequence
    | LogicOld.T_sequence.SInfSequence -> SInfSequence
    | sort -> failwith @@ "unsupported old sort: " ^ LogicOld.Term.str_of_sort sort
  and of_old_opsig = function
    | LogicOld.Sort.OpSig (opmap, rv) -> Sort.OpSig (ALMap.map opmap ~f:of_old_sort, rv)
    | _ -> failwith "[of_old_opsig]"
  let of_old_sort_bind (x, s) = x, of_old_sort s
  let of_old_sort_env = List.map ~f:of_old_sort_bind
  let of_unop = function LogicOld.Formula.Not -> mk_not ()
  let of_binop = function
    | LogicOld.Formula.And -> mk_and ()
    | LogicOld.Formula.Or -> mk_or ()
    | LogicOld.Formula.Imply -> mk_imply ()
    | LogicOld.Formula.Iff-> mk_iff ()
    | LogicOld.Formula.Xor-> mk_xor ()
  let rec of_old_fun_sym sym sargs =
    match sym, sargs with
    | LogicOld.FVar (x, _sorts), _ -> mk_var x
    | LogicOld.T_bool.Formula phi, [] -> of_old_formula phi
    | LogicOld.T_bool.IfThenElse, [_; sort; _] -> mk_ite sort
    | LogicOld.T_int.Int n, [] -> mk_int n
    | LogicOld.T_int.Add, [_; _] -> mk_add ()
    | LogicOld.T_int.Sub, [_; _] -> mk_sub ()
    | LogicOld.T_int.Mult, [_; _] -> mk_mult ()
    | LogicOld.T_int.Div, [_; _] -> mk_div ()
    | LogicOld.T_int.Mod, [_; _] -> mk_mod ()
    | LogicOld.T_int.Neg, [_] -> mk_neg ()
    | LogicOld.T_int.Abs, [_] -> mk_abs ()
    | LogicOld.T_int.Rem, [_;_] -> mk_rem ()
    | LogicOld.T_real.Real r, [] -> mk_real r
    | LogicOld.T_real.RAdd, [_; _] -> mk_radd ()
    | LogicOld.T_real.RSub, [_; _] -> mk_rsub ()
    | LogicOld.T_real.RMult, [_; _] -> mk_rmult ()
    | LogicOld.T_real.RDiv, [_; _] -> mk_rdiv ()
    | LogicOld.T_real.RNeg, [_] -> mk_rneg ()
    | LogicOld.T_real.RAbs, [_] -> mk_rabs ()
    | LogicOld.T_real_int.ToReal, [_] -> mk_to_real ()
    | LogicOld.T_real_int.ToInt, [_] -> mk_to_int ()
    (*| LogicOld.T_num.Value (_v, _svar), [] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.NAdd svar, [_; _] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.NSub svar, [_; _] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.NMult svar, [_; _] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.NDiv svar, [_; _] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.NPower svar, [_; _] -> failwith "of_old_fun_sym"
      | LogicOld.T_num.NNeg svar, [_] -> failwith "of_old_fun_sym"*)
    | LogicOld.T_tuple.TupleCons sorts, _ -> mk_tuple_cons (List.map ~f:of_old_sort sorts)
    | LogicOld.T_tuple.TupleSel (sorts, i), _ -> mk_tuple_sel (List.map ~f:of_old_sort sorts) i
    | LogicOld.T_dt.DTCons (name, _, dt), _ -> mk_cons (Datatype.of_old of_old_sort dt) name
    | LogicOld.T_dt.DTSel (name, dt, _), _ -> mk_sel (Datatype.of_old of_old_sort dt) name
    | LogicOld.T_array.AStore (s1, s2), _-> mk_store (of_old_sort s1) (of_old_sort s2)
    | LogicOld.T_array.ASelect (s1, s2), _ -> mk_select (of_old_sort s1) (of_old_sort s2)
    | LogicOld.T_array.AConst (s1, s2), _ -> mk_const_array (of_old_sort s1) (of_old_sort s2)
    | LogicOld.T_string.StringConst str, _ -> mk_con @@ StringConst str
    | LogicOld.T_sequence.Epsilon, _ -> mk_con Epsilon
    | LogicOld.T_sequence.Symbol ev, _ -> mk_con @@ Symbol ev
    | LogicOld.T_sequence.Concat fin, _ -> mk_con @@ Concat fin
    | LogicOld.T_sequence.LeftQuotient fin, _ -> mk_con @@ LeftQuotient fin
    | LogicOld.T_sequence.RightQuotient fin, _ -> mk_con @@ RightQuotient fin
    | _ -> failwith @@ sprintf "%s not supported" (LogicOld.Term.str_of_funsym sym)
  and of_old_pred_sym sym sargs =
    match sym, sargs with
    | LogicOld.T_bool.Eq, [sort; _] -> mk_eq sort
    | LogicOld.T_bool.Neq, [sort; _] -> mk_neq sort
    | LogicOld.T_int.Leq, [_; _]  -> mk_leq ()
    | LogicOld.T_int.Geq, [_; _] -> mk_geq ()
    | LogicOld.T_int.Lt, [_; _]  -> mk_lt ()
    | LogicOld.T_int.Gt, [_; _] -> mk_gt ()
    | LogicOld.T_int.PDiv, [_; _] -> mk_pdiv ()
    | LogicOld.T_real.RLeq, [_; _] -> mk_rleq ()
    | LogicOld.T_real.RGeq, [_; _] -> mk_rgeq ()
    | LogicOld.T_real.RLt, [_; _] -> mk_rlt ()
    | LogicOld.T_real.RGt, [_; _] -> mk_rgt ()
    | LogicOld.T_real_int.IsInt, [_] -> mk_isint ()
    | LogicOld.T_num.NLeq svar, [_; _] -> mk_tyapp (mk_con Leq) (Sort.SVar svar)
    | LogicOld.T_num.NGeq svar, [_; _] -> mk_tyapp (mk_con Geq) (Sort.SVar svar)
    | LogicOld.T_num.NLt svar, [_; _] -> mk_tyapp (mk_con Lt) (Sort.SVar svar)
    | LogicOld.T_num.NGt svar, [_; _] -> mk_tyapp (mk_con Gt) (Sort.SVar svar)
    | LogicOld.T_tuple.IsTuple sorts, _ -> mk_is_tuple (List.map ~f:of_old_sort sorts)
    | LogicOld.T_tuple.NotIsTuple sorts, _ -> mk_is_not_tuple (List.map ~f:of_old_sort sorts)
    | LogicOld.T_dt.IsCons (name, dt), _ -> mk_is_cons name (Datatype.of_old of_old_sort dt)
    | LogicOld.T_dt.NotIsCons (name, dt), _ -> mk_is_not_cons name (Datatype.of_old of_old_sort dt)
    | LogicOld.T_sequence.IsPrefix fin, [_; _] -> Term.mk_con @@ IsPrefix fin
    | LogicOld.T_sequence.NotIsPrefix fin, [_; _] -> Term.mk_con @@ NotIsPrefix fin
    | LogicOld.T_sequence.InRegExp (fin, regexp), [_] -> Term.mk_con @@ InRegExp (fin, regexp)
    | LogicOld.T_sequence.NotInRegExp (fin, regexp), [_] -> Term.mk_con @@ NotInRegExp (fin, regexp)
    | _ -> failwith @@ sprintf "%s not supported" @@ LogicOld.Predicate.str_of_predsym sym
  and of_old_term = function
    | LogicOld.Term.Var (tvar, _sort, _) -> mk_var tvar
    | LogicOld.Term.FunApp (sym, args, _) ->
      let sargs = List.map args ~f:(fun t -> of_old_sort @@ LogicOld.Term.sort_of t) in
      mk_apps (of_old_fun_sym sym sargs) (List.map ~f:of_old_term args)
    | LogicOld.Term.LetTerm (var, sort, def, body, _) ->
      mk_let var (of_old_sort sort) (of_old_term def) (of_old_term body)
  and of_old_atom = function
    | LogicOld.Atom.True _ -> mk_bool true
    | LogicOld.Atom.False _ -> mk_bool false
    | LogicOld.Atom.App (LogicOld.Predicate.Var (Ident.Pvar pvar, _), args, _) ->
      mk_apps (mk_var (Ident.Tvar pvar)) (List.map ~f:of_old_term args)
    | LogicOld.Atom.App (LogicOld.Predicate.Psym psym, args, _) ->
      let sargs = List.map args ~f:(fun t -> of_old_sort @@ LogicOld.Term.sort_of t) in
      mk_apps (of_old_pred_sym psym sargs) (List.map ~f:of_old_term args)
    | LogicOld.Atom.App (LogicOld.Predicate.Fixpoint (_, _, _, _), _, _) ->
      failwith "conversion of fixpoint is not implemented yet"
  and of_old_formula = function
    | LogicOld.Formula.Atom (atom, _) -> of_old_atom atom
    | LogicOld.Formula.UnaryOp (unop, phi, _) ->
      mk_app (of_unop unop) (of_old_formula phi)
    | LogicOld.Formula.BinaryOp (binop, p1, p2, _) ->
      mk_app (mk_app (of_binop binop) (of_old_formula p1)) (of_old_formula p2)
    | LogicOld.Formula.Bind (bind, args, phi, _) ->
      let phi = of_old_formula phi in
      let bind =
        match bind with
        | LogicOld.Formula.Forall -> Forall
        | LogicOld.Formula.Exists -> Exists
        | LogicOld.Formula.Random _ -> failwith "unimplemented"
      in
      List.fold_right ~init:phi args
        ~f:(fun (tvar, sort) -> mk_bind bind tvar (of_old_sort sort))
    | LogicOld.Formula.LetRec _ -> failwith "conversion of letrec is not implemented yet"
    | LogicOld.Formula.LetFormula (var, sort, def, body, _) ->
      mk_let var (of_old_sort sort) (of_old_term def) (of_old_formula body)

  let rec to_old_cont = function
    | Sort.EVar x -> LogicOld.Sort.EVar x
    | Sort.Pure -> LogicOld.Sort.Pure
    | Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      LogicOld.Sort.Eff (to_old_opsig o1, to_old_sort s1, to_old_cont e1, to_old_opsig o2, to_old_sort s2, to_old_cont e2)
    | _ -> failwith "to_old_cont"
  and to_old_sort = function
    | Sort.SVar svar -> LogicOld.Sort.SVar svar
    | Sort.SArrow (s1, (o, s2, e)) ->
      LogicOld.Sort.SArrow (to_old_sort s1, (to_old_opsig o, to_old_sort s2, to_old_cont e))
    | SBool -> LogicOld.T_bool.SBool
    | SInt -> LogicOld.T_int.SInt
    | SReal -> LogicOld.T_real.SReal
    | STuple sorts -> LogicOld.T_tuple.STuple (List.map sorts ~f:to_old_sort)
    | SDT dt -> LogicOld.T_dt.SDT (Datatype.to_old to_old_sort dt)
    | SUS (name, args) -> LogicOld.T_dt.SUS (name, List.map args ~f:to_old_sort)
    | SArray (s1, s2) -> LogicOld.T_array.SArray (to_old_sort s1, to_old_sort s2)
    | SString -> LogicOld.T_string.SString
    | SFinSequence -> LogicOld.T_sequence.SFinSequence
    | SInfSequence -> LogicOld.T_sequence.SInfSequence
    | _ -> failwith "unknown sort"
  and to_old_opsig = function
    | Sort.OpSig (opmap, rv) -> LogicOld.Sort.OpSig (ALMap.map opmap ~f:to_old_sort, rv)
    | _ -> failwith "of_old_opsig"
  let to_old_sort_bind (x, s) = x, to_old_sort s
  let to_old_unop = function
    | Not -> LogicOld.Formula.Not |> Option.some
    | _ -> None
  let to_old_binop = function
    | And -> LogicOld.Formula.And |> Option.some
    | Or -> LogicOld.Formula.Or |> Option.some
    | Imply -> LogicOld.Formula.Imply |> Option.some
    | Iff -> LogicOld.Formula.Iff |> Option.some
    | Xor -> LogicOld.Formula.Xor |> Option.some
    | _ -> None
  let to_old_fun_sym = function
    | IfThenElse -> LogicOld.T_bool.IfThenElse |> Option.some
    | Int n -> LogicOld.T_int.Int n |> Option.some
    | Add -> LogicOld.T_int.Add |> Option.some
    | Sub -> LogicOld.T_int.Sub |> Option.some
    | Mult -> LogicOld.T_int.Mult |> Option.some
    | Div -> LogicOld.T_int.Div |> Option.some
    | Mod -> LogicOld.T_int.Mod |> Option.some
    | Neg -> LogicOld.T_int.Neg |> Option.some
    | Abs -> LogicOld.T_int.Abs |> Option.some
    | Rem -> LogicOld.T_int.Rem |> Option.some
    | Real r -> LogicOld.T_real.Real r |> Option.some
    | RAdd -> LogicOld.T_real.RAdd |> Option.some
    | RSub -> LogicOld.T_real.RSub |> Option.some
    | RMult -> LogicOld.T_real.RMult |> Option.some
    | RDiv -> LogicOld.T_real.RDiv |> Option.some
    | RNeg -> LogicOld.T_real.RNeg |> Option.some
    | RAbs -> LogicOld.T_real.RAbs |> Option.some
    | ToReal -> LogicOld.T_real_int.ToReal |> Option.some
    | ToInt -> LogicOld.T_real_int.ToInt |> Option.some
    | TupleCons sorts ->
      LogicOld.T_tuple.TupleCons (List.map sorts ~f:to_old_sort) |> Option.some
    | TupleSel (sorts, i) ->
      LogicOld.T_tuple.TupleSel (List.map sorts ~f:to_old_sort, i) |> Option.some
    | DTCons (name, sorts, dt) ->
      LogicOld.T_dt.DTCons
        (name, List.map sorts ~f:to_old_sort, Datatype.to_old to_old_sort dt) |> Option.some
    | DTSel (name, dt, sort) ->
      LogicOld.T_dt.DTSel (name, Datatype.to_old to_old_sort dt, to_old_sort sort) |> Option.some
    | AStore (s1, s2) ->
      LogicOld.T_array.AStore (to_old_sort s1, to_old_sort s2) |> Option.some
    | ASelect (s1, s2) ->
      LogicOld.T_array.ASelect (to_old_sort s1, to_old_sort s2) |> Option.some
    | AConst (s1, s2) ->
      LogicOld.T_array.AConst (to_old_sort s1, to_old_sort s2) |> Option.some
    | StringConst str ->
      LogicOld.T_string.StringConst str |> Option.some
    | Epsilon ->
      LogicOld.T_sequence.Epsilon |> Option.some
    | Symbol ev ->
      LogicOld.T_sequence.Symbol ev |> Option.some
    | Concat fin ->
      LogicOld.T_sequence.Concat fin |> Option.some
    | LeftQuotient fin ->
      LogicOld.T_sequence.LeftQuotient fin |> Option.some
    | RightQuotient fin ->
      LogicOld.T_sequence.RightQuotient fin |> Option.some
    | _ -> None
  let to_old_pred_sym = function
    | Eq -> LogicOld.T_bool.Eq |> Option.some
    | Neq -> LogicOld.T_bool.Neq |> Option.some
    | Leq -> LogicOld.T_int.Leq |> Option.some
    | Geq -> LogicOld.T_int.Geq |> Option.some
    | Lt -> LogicOld.T_int.Lt |> Option.some
    | Gt -> LogicOld.T_int.Gt |> Option.some
    | PDiv -> LogicOld.T_int.PDiv |> Option.some
    | RLeq -> LogicOld.T_real.RLeq |> Option.some
    | RGeq -> LogicOld.T_real.RGeq |> Option.some
    | RLt -> LogicOld.T_real.RLt |> Option.some
    | RGt -> LogicOld.T_real.RGt |> Option.some
    | IsInt -> LogicOld.T_real_int.IsInt |> Option.some
    | IsTuple sorts ->
      LogicOld.T_tuple.IsTuple (List.map ~f:to_old_sort sorts) |> Option.some
    | NotIsTuple sorts ->
      LogicOld.T_tuple.NotIsTuple (List.map ~f:to_old_sort sorts) |> Option.some
    | IsCons (name, dt) ->
      LogicOld.T_dt.IsCons (name, Datatype.to_old to_old_sort dt) |> Option.some
    | NotIsCons (name, dt) ->
      LogicOld.T_dt.NotIsCons (name, Datatype.to_old to_old_sort dt) |> Option.some
    | IsPrefix fin -> LogicOld.T_sequence.IsPrefix fin |> Option.some
    | NotIsPrefix fin -> LogicOld.T_sequence.NotIsPrefix fin |> Option.some
    | InRegExp (fin, regexp) -> LogicOld.T_sequence.InRegExp (fin, regexp) |> Option.some
    | NotInRegExp (fin, regexp) -> LogicOld.T_sequence.NotInRegExp (fin, regexp) |> Option.some
    | _ -> None
  let rec to_old_term exi_senv uni_senv term args =
    match term, args with
    | Var (tvar, _), args ->
      let args' = List.map args ~f:(Fn.flip (to_old_term exi_senv uni_senv) []) in
      let sort =
        match Map.Poly.find exi_senv tvar with
        | Some sort -> to_old_sort sort
        | None ->
          match Map.Poly.find uni_senv tvar with
          | Some sort -> to_old_sort sort
          | None ->
            match
              List.Assoc.find (Atomic.get LogicOld.dummy_term_senv) ~equal:Stdlib.(=) tvar
            with
            | Some sort -> sort
            | None ->
              match Map.Poly.find (Atomic.get LogicOld.ref_fenv) tvar with
              | Some (params, sret, _, _, _) ->
                LogicOld.Sort.mk_fun (List.map params ~f:snd @ [sret])
              | None ->
                failwith @@ Printf.sprintf "[to_old_term] %s is not bound" @@ Ident.name_of_tvar tvar
      in
      let sargs, sret = LogicOld.Sort.args_ret_of sort in
      if List.is_empty args then
        LogicOld.Term.mk_var tvar sort
      else if LogicOld.Term.is_bool_sort sret then
        LogicOld.T_bool.of_atom @@
        LogicOld.Atom.mk_pvar_app (Ident.tvar_to_pvar tvar) sargs args'
      else
        LogicOld.Term.mk_fvar_app tvar (sargs @ [sret]) args'
    | Con (sym, _), args ->
      begin
        match to_old_fun_sym sym with
        | Some old_sym ->
          LogicOld.Term.mk_fsym_app old_sym @@
          List.map args ~f:(Fn.flip (to_old_term exi_senv uni_senv) [])
        | None -> LogicOld.T_bool.of_formula (to_old_formula exi_senv uni_senv term args)
      end
    | App (t1, t2, _), args ->
      to_old_term exi_senv uni_senv t1 (t2 :: args)
    | Bin (Lambda, _, _, _, _), [] ->
      failwith "[to_old_term] partial application not supported"
    | Bin (Lambda, tvar, _, t, _), arg :: args' ->
      to_old_term exi_senv uni_senv (subst (Map.Poly.singleton tvar arg) t) args'
    | Let (var, sort, def, body, _), args ->
      LogicOld.Term.mk_let_term var (to_old_sort sort)
        (to_old_term exi_senv uni_senv def [])
        (to_old_term exi_senv (Map.Poly.set uni_senv ~key:var ~data:sort) body args)
    | TyApp (Con ((Eq | Neq) as op, _), _, _), [t1; t2] ->
      let t1' = to_old_term exi_senv uni_senv t1 [] in
      let t2' = to_old_term exi_senv uni_senv t2 [] in
      LogicOld.T_bool.of_atom @@
      if Stdlib.(op = Eq)
      then LogicOld.T_bool.mk_eq t1' t2'
      else LogicOld.T_bool.mk_neq t1' t2'
    | TyApp (Con (IfThenElse, _), (SBool | Sort.SVar _), _), t1 :: t2 :: t3 :: args
      when BoolTerm.is_bool_sort (sort_of (Map.force_merge exi_senv uni_senv) t2) ->
      let t1' = LogicOld.T_bool.of_formula (to_old_formula exi_senv uni_senv t1 []) in
      let t2' = LogicOld.T_bool.of_formula (to_old_formula exi_senv uni_senv t2 args) in
      let t3' = LogicOld.T_bool.of_formula (to_old_formula exi_senv uni_senv t3 args) in
      LogicOld.T_bool.mk_if_then_else t1' t2' t3'
    | TyApp (Con (IfThenElse, _), _, _), t1 :: t2 :: t3 :: args ->
      let t1' = LogicOld.T_bool.of_formula (to_old_formula exi_senv uni_senv t1 []) in
      let t2' = to_old_term exi_senv uni_senv t2 args in
      let t3' = to_old_term exi_senv uni_senv t3 args in
      LogicOld.T_bool.mk_if_then_else t1' t2' t3'
    | TyApp (Con (Leq, _), Sort.SVar svar, _), [t1; t2] ->
      let t1' = to_old_term exi_senv uni_senv t1 [] in
      let t2' = to_old_term exi_senv uni_senv t2 [] in
      LogicOld.T_bool.of_atom @@ LogicOld.Atom.mk_psym_app (LogicOld.T_num.NLeq svar) [t1';t2']
    | TyApp (Con (Geq, _), Sort.SVar svar, _), [t1; t2] ->
      let t1' = to_old_term exi_senv uni_senv t1 [] in
      let t2' = to_old_term exi_senv uni_senv t2 [] in
      LogicOld.T_bool.of_atom @@ LogicOld.Atom.mk_psym_app (LogicOld.T_num.NGeq svar) [t1';t2']
    | TyApp (Con (Lt, _), Sort.SVar svar, _), [t1; t2] ->
      let t1' = to_old_term exi_senv uni_senv t1 [] in
      let t2' = to_old_term exi_senv uni_senv t2 [] in
      LogicOld.T_bool.of_atom @@ LogicOld.Atom.mk_psym_app (LogicOld.T_num.NLt svar) [t1';t2']
    | TyApp (Con (Gt, _), Sort.SVar svar, _), [t1; t2] ->
      let t1' = to_old_term exi_senv uni_senv t1 [] in
      let t2' = to_old_term exi_senv uni_senv t2 [] in
      LogicOld.T_bool.of_atom @@ LogicOld.Atom.mk_psym_app (LogicOld.T_num.NGt svar) [t1';t2']
    (*| TyApp (t, _sort, _), args (* ToDo: use [sort] *) ->
      to_old_term exi_senv uni_senv t args*)
    | TyLam _, _ ->
      failwith "[to_old_term] tylam not implemented"
    | _ ->
      failwith @@
      sprintf "[to_old_term] unknown term: %s(%s)"
        (str_of term) (String.concat_map_list ~sep:"," args ~f:str_of)
  and to_old_atom exi_senv uni_senv term args =
    match term, args with
    | Var (Ident.Tvar name as tvar, _), args -> begin
        let args' = List.map args ~f:(fun t -> to_old_term exi_senv uni_senv t []) in
        match Map.Poly.find exi_senv tvar with
        | Some sort ->
          let sargs, sret = Sort.args_ret_of sort in
          assert (BoolTerm.is_bool_sort sret);
          let pred = LogicOld.Predicate.mk_var (Ident.Pvar name) (List.map ~f:to_old_sort sargs) in
          LogicOld.Atom.mk_app pred args'
        | None ->
          match Map.Poly.find uni_senv tvar with
          | Some sort ->
            assert (BoolTerm.is_bool_sort sort);
            if Fn.non List.is_empty args then
              failwith @@ sprintf "%s(%s)"
                (Ident.name_of_tvar tvar) (String.concat_map_list ~sep:"," args ~f:str_of);
            LogicOld.Atom.of_bool_term @@ LogicOld.Term.mk_var tvar (to_old_sort sort)
          | None ->
            match Map.Poly.find (Atomic.get LogicOld.ref_fenv) tvar with
            | Some (params, sret, _, _, _) ->
              assert (LogicOld.Term.is_bool_sort sret);
              let sargs = List.map params ~f:snd in
              LogicOld.Atom.of_bool_term @@
              LogicOld.Term.mk_fvar_app tvar (sargs @ [sret]) args'
            | None ->
              print_endline @@ sprintf "exi_senv: %s" @@
              str_of_sort_env_map str_of_sort exi_senv;
              print_endline @@ sprintf "uni_senv: %s" @@
              str_of_sort_env_map str_of_sort uni_senv;
              failwith (Printf.sprintf "[to_old_atom] %s is not bound" name)
      end
    | Con (True, _), [] -> LogicOld.Atom.mk_true ()
    | Con (False, _), [] -> LogicOld.Atom.mk_false ()
    | Con (ASelect _, _), args ->
      LogicOld.Atom.of_bool_term @@ to_old_term exi_senv uni_senv term args
    | Con (DTSel (name, dt, _), _), [arg]->
      LogicOld.Atom.of_bool_term @@
      LogicOld.T_dt.mk_sel (Datatype.to_old to_old_sort dt) name @@
      to_old_term exi_senv uni_senv arg []
    | Con (sym, _) as term, args ->
      let pred =
        match to_old_pred_sym sym with
        | Some pred_sym -> LogicOld.Predicate.mk_psym pred_sym
        | None -> failwith (sprintf "[to_old_atom] unknown pred. symbol: %s" @@ str_of term)
      in
      LogicOld.Atom.mk_app pred @@
      List.map ~f:(fun t -> to_old_term exi_senv uni_senv t []) args
    | App (t1, t2, _), args ->
      to_old_atom exi_senv uni_senv t1 (t2 :: args)
    | Bin (Lambda, _, _, _, _), [] ->
      failwith "[to_old_atom] partial application not supported"
    | Bin (Lambda, tvar, _, t, _), arg :: args' ->
      to_old_atom exi_senv uni_senv (subst (Map.Poly.singleton tvar arg) t) args'
    | Let (var, sort, def, body, _), args ->
      let sort' = to_old_sort sort in
      let def' = to_old_term exi_senv uni_senv def [] in
      let body' = to_old_atom exi_senv (Map.Poly.set uni_senv ~key:var ~data:sort) body args in
      LogicOld.Atom.insert_let_pvar_app var sort' def' (LogicOld.Dummy(* ToDo *)) body'
    | TyApp (Con ((Eq | Neq) as op, _), _, _), [t1; t2] ->
      let t1' = to_old_term exi_senv uni_senv t1 [] in
      let t2' = to_old_term exi_senv uni_senv t2 [] in
      if Stdlib.(op = Eq) then LogicOld.T_bool.mk_eq t1' t2' else LogicOld.T_bool.mk_neq t1' t2'
    | TyApp (Con (IfThenElse, _), (SBool | Sort.SVar _), _), t1 :: t2 :: t3 :: args
      when BoolTerm.is_bool_sort (sort_of (Map.force_merge exi_senv uni_senv) t2) ->
      let t1' = LogicOld.T_bool.of_formula (to_old_formula exi_senv uni_senv t1 []) in
      let t2' = LogicOld.T_bool.of_formula (to_old_formula exi_senv uni_senv t2 args) in
      let t3'  = LogicOld.T_bool.of_formula (to_old_formula exi_senv uni_senv t3 args) in
      LogicOld.Atom.of_bool_term @@ LogicOld.T_bool.mk_if_then_else t1' t2' t3'
    (*LogicOld.Formula.mk_or
      (LogicOld.Formula.mk_and t1' t2')
      (LogicOld.Formula.mk_and (LogicOld.Formula.mk_neg t1') t3')*)
    | TyApp (t, _sort, _), args (* ToDo: use [sort] *) ->
      to_old_atom exi_senv uni_senv t args
    | _ ->
      failwith @@
      sprintf "[to_old_atom] unknown term: %s(%s)"
        (str_of term) (String.concat_map_list ~sep:"," args ~f:str_of)
  and to_old_formula exi_senv uni_senv term args =
    let rec aux uni_senv term args ~next =
      match term with
      | Var _ ->
        next @@ LogicOld.Formula.mk_atom @@ to_old_atom exi_senv uni_senv term args
      | Con (sym, _) -> begin
          match to_old_unop sym with
          | Some unop_sym -> begin
              match args with
              | [t] ->
                aux uni_senv t [] ~next:(fun t' -> next @@ LogicOld.Formula.mk_unop unop_sym t')
              | _ -> assert false
            end
          | None -> begin
              match to_old_binop sym with
              | Some binop_sym -> begin
                  match args with
                  | [t1; t2] ->
                    aux uni_senv t1 [] ~next:(fun t1' ->
                        aux uni_senv t2 [] ~next:(fun t2' ->
                            next @@ LogicOld.Formula.mk_binop binop_sym t1' t2'))
                  | _ -> failwith (String.concat_map_list ~sep:"\n" ~f:str_of args)
                end
              | None -> next @@ LogicOld.Formula.mk_atom @@ to_old_atom exi_senv uni_senv term args
            end
        end
      | App (t1, t2, _) -> aux uni_senv t1 (t2 :: args) ~next
      | Bin (Forall, tvar, s, t, _) -> begin
          match args with
          | [] ->
            aux (Map.Poly.set uni_senv ~key:tvar ~data:s) t [] ~next:(fun t' ->
                next @@ LogicOld.Formula.mk_forall [tvar, to_old_sort s] t')
          | _ -> assert false
        end
      | Bin (Exists, tvar, s, t, _) -> begin
          match args with
          | [] ->
            aux (Map.Poly.set uni_senv ~key:tvar ~data:s) t [] ~next:(fun t' ->
                next @@ LogicOld.Formula.mk_exists [tvar, to_old_sort s] t')
          | _ -> assert false
        end
      | Bin (Lambda, tvar, _, t, _) -> begin
          match args with
          | [] -> assert false
          | arg :: args' ->
            aux uni_senv (subst (Map.Poly.singleton tvar arg) t) args' ~next
        end
      | TyApp (Con ((Eq | Neq | IfThenElse), _), (SBool | Sort.SVar _), _) ->
        next @@ LogicOld.Formula.mk_atom @@ to_old_atom exi_senv uni_senv term args
      | TyApp (term, _sort, _) (* ToDo: use [sort] *) -> aux uni_senv term args ~next
      | Let (var, sort, def, body, _) ->
        aux (Map.Poly.set uni_senv ~key:var ~data:sort) body args ~next:(fun body' ->
            next @@ LogicOld.Formula.mk_let_formula var (to_old_sort sort) (to_old_term exi_senv uni_senv def []) body')
      | _ ->
        failwith @@
        sprintf "[to_old_formula] unknown term: %s(%s)"
          (str_of term) (String.concat_map_list ~sep:"," args ~f:str_of)      
    in aux uni_senv term args ~next:Fn.id
  let to_old_subst exi_senv uni_senv =
    Map.Poly.map ~f:(Fn.flip (to_old_term exi_senv uni_senv) [])

  let remove_dontcare_elem ((x, s), v) =
    match v with
    | None -> x, mk_dummy s
    | Some term -> x, term
  let remove_dontcare = List.map ~f:remove_dontcare_elem

  let str_of_formula exi_senv uni_senv term =
    LogicOld.Formula.str_of @@ Evaluator.simplify @@ to_old_formula exi_senv uni_senv term []
  let str_of_term exi_senv uni_senv term =
    LogicOld.Term.str_of @@ Evaluator.simplify_term @@ to_old_term exi_senv uni_senv term []

  let simplify_formula exi_senv uni_senv t =
    try
      let param_senv, phi = let_lam t in
      let uni_senv = Map.force_merge uni_senv (Map.Poly.of_alist_exn param_senv) in
      to_old_formula exi_senv uni_senv phi []
      |> Evaluator.simplify
      |> of_old_formula
      |> mk_lambda param_senv
    with _ ->
      to_old_formula exi_senv uni_senv t []
      |> Evaluator.simplify
      |> of_old_formula
  let simplify_term exi_senv uni_senv t =
    try
      let param_senv, phi = let_lam t in
      let uni_senv = Map.force_merge uni_senv (Map.Poly.of_alist_exn param_senv) in
      to_old_term exi_senv uni_senv phi []
      |> Evaluator.simplify_term
      |> of_old_term
      |> mk_lambda param_senv
    with _ ->
      to_old_term exi_senv uni_senv t []
      |> Evaluator.simplify_term
      |> of_old_term
end
