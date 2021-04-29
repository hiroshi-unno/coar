open Core
open Common.Util

module Sort = struct
  type t = ..
  type t += SVar of Ident.svar | SArrow of t * t | SForAll of Ident.svar * t

  let mk_arrow s1 s2 = SArrow(s1, s2)
  let rec mk_fun = function
    | [s] -> s
    | s :: ss -> mk_arrow s (mk_fun ss)
    | _ -> assert false
  let mk_forall v sort = SForAll(v, sort)

  let is_arrow = function
    | SArrow _ -> true
    | _ -> false
  let rec arity_of = function
    | SVar _ -> assert false
    | SArrow (_s1, s2) -> 1 + arity_of s2
    | SForAll (_, s) -> arity_of s
    | _ -> 0 (* assert false*)
  let rec ret_of = function
    | SArrow (_s1, s2) -> ret_of s2
    | sort -> sort
  let rec args_of = function
    | SArrow (s1, s2) ->
      let args = args_of s2 in
      s1 :: args
    | _ -> []
  let rec args_ret_of = function
    | SArrow (s1, s2) ->
      let args, ret = args_ret_of s2 in
      s1 :: args, ret
    | s -> [], s
end

module SortMap = struct
  include Map.Poly
  include Map
  type t = (Ident.tvar, Sort.t) Map.Poly.t

  let empty = Map.Poly.empty
  let to_map senv = senv
  let to_set = Set.of_map
  let to_old_sort_env to_old_sort senv = 
    LogicOld.SortEnv.of_map @@ Map.Poly.map senv ~f:to_old_sort
  let to_old_sort_map to_old_sort = Map.Poly.map ~f:to_old_sort
  let to_old_dummies to_old_sort senv =
    to_map @@ map senv ~f:(fun s -> LogicOld.Term.mk_dummy (to_old_sort s))
  let of_old_sort_env of_old_sort senv =
    Map.Poly.of_alist_exn @@ LogicOld.SortEnv.map ~f:(fun (x, s) -> x, of_old_sort s) senv
  let of_old_sort_map of_old_sort = Map.Poly.map ~f:of_old_sort

  let merge = force_merge
  let merge_list = function
    | [] -> Map.Poly.empty
    | senv :: senvs' -> List.fold ~init:senv senvs' ~f:merge

  let str_of str_of_sort senv =
    String.concat ~sep:" " @@
    List.map (to_alist senv) ~f:(fun (tvar, sort) ->
        Printf.sprintf "(%s: %s)" (Ident.name_of_tvar tvar) (str_of_sort sort))


  (*type t = (Ident.tvar * Sort.t) Set.Poly.t

    let empty = Set.Poly.empty
    let merge senv1 senv2 =
    let xs = Set.Poly.union (Set.Poly.map ~f:fst senv1) (Set.Poly.map ~f:fst senv2) in
    Set.Poly.map xs ~f:(fun x ->
        match Set.Poly.find senv1 ~f:(fun (y, _) -> Stdlib.(=) x y),
              Set.Poly.find senv2 ~f:(fun (y, _) -> Stdlib.(=) x y) with
        | Some (_, s1), Some (_, s2) -> if Stdlib.(=) s1 s2 then x, s1 else assert false
        | Some(_, s), None | None, Some(_, s) -> x, s
        | None, None -> assert false)

    let merge_list = function
    | [] -> Set.Poly.empty
    | senv :: senvs' -> List.fold ~init:senv senvs' ~f:merge

    let is_empty = Set.Poly.is_empty
    let mem senv x = Set.Poly.exists senv ~f:(fun (y, _) -> Stdlib.(=) x y)
    let remove senv x = Set.Poly.filter senv ~f:(fun (y, _) -> Stdlib.(<>) x y)
    let singleton x s = Set.Poly.singleton (x, s)

    let length = Set.Poly.length
    let find senv x = Set.Poly.find_map senv ~f:(fun (y, s) -> if Stdlib.(=) x y then Some s else None)
    let find_exn senv x = snd @@ Set.Poly.find_exn senv ~f:(fun (y, _) -> Stdlib.(=) x y)
    let add_exn senv ~key ~data =
    match find senv key with
    | None -> Set.Poly.add senv (key, data)
    | Some _ -> failwith "add_exn"
    let update senv x ~f =
    match find senv x with
    | None -> Set.Poly.add senv (x, f None)
    | Some s -> Set.Poly.map senv ~f:(fun (y, s') -> if Stdlib.(=) x y then y, f (Some s) else y, s')

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
    let filter_keys ~f senv = Set.Poly.filter senv ~f:(fun (x, _) -> f x)*)
end

module SortEnv = struct
  type t = (Ident.tvar * Sort.t) list

  let str_of str_of_sort senv =
    String.concat ~sep:", " @@
    List.map senv ~f:(fun (tvar, sort) ->
        Printf.sprintf "%s: %s" (Ident.name_of_tvar tvar) (str_of_sort sort))

  let of_old_sort_env of_old_sort senv = LogicOld.SortEnv.map ~f:(fun (x, s) -> x, of_old_sort s) senv
  let to_old_sort_env to_old_sort senv = LogicOld.SortEnv.of_list @@ List.map ~f:(fun (x, s) -> x, to_old_sort s) senv
end

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


module type TermType = sig
  (** Construction *)
  val mk_var: Ident.tvar -> term
  val mk_con: sym -> term
  val mk_app: term -> term -> term
  val mk_apps: term -> term list -> term
  val mk_sym_app: sym -> term list -> term
  val mk_var_app: Ident.tvar -> term list -> term
  val mk_bind: binder -> Ident.tvar -> Sort.t -> term -> term
  val mk_binds: binder -> SortEnv.t -> term -> term
  val mk_let: Ident.tvar -> Sort.t -> term -> term -> term
  val mk_tyapp: term -> Sort.t -> term
  val mk_tylam: Ident.svar -> term -> term
  val mk_lambda: SortEnv.t -> term -> term

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
  val let_lam: term -> SortEnv.t * term

  val fvs_of: term -> Ident.tvar Set.Poly.t
  val pvar_of_atom: term -> Ident.tvar
  val ast_size: term -> int

  (** Sorts *)
  val open_arity_of_sym: (sym -> Sort.t) -> sym -> int
  val open_sort_of: (sym -> Sort.t) -> SortMap.t -> term -> Sort.t

  val sym_sort_map: (sym, Sort.t) Map.Poly.t
  val arity_of_sym: sym -> int
  val sort_of_sym: sym -> Sort.t
  val sort_of: SortMap.t -> term -> Sort.t

  (** Substitution *)
  val rename: (Ident.tvar, Ident.tvar) Map.Poly.t -> term -> term
  val subst: (Ident.tvar, term) Map.Poly.t -> term -> term
  val beta_reduction: term -> term list -> term
  val refresh: SortMap.t * term -> SortMap.t * term
  (*val unify: term -> term -> (Ident.tvar, term) Map.Poly.t option*)

  (** Transformation *)
  val reduce_sort_map: SortMap.t * term -> SortMap.t * term

  (** Printing *)
  val open_str_of_sort: (Sort.t -> string) -> Sort.t -> string
  val open_str_of: (Sort.t -> string) -> (sym -> string) -> term -> string
  val open_str_of_subst: (term -> string) -> (Ident.tvar, term) Map.Poly.t -> string

  val str_of_sym: sym -> string
  val str_of_termlit: termlit -> string
  val str_of_sort: Sort.t -> string
  val str_of: term -> string
  val str_of_subst: (Ident.tvar, term) Map.Poly.t -> string

  (** Evaluation *)
  val open_assert_sort_check: (Sort.t -> termlit -> unit) -> Sort.t -> termlit -> unit
  val open_eval: (sym -> termlit) -> (termlit -> term) -> (sym, Sort.t) Map.Poly.t -> term -> termlit

  val is_termlit: termlit -> bool
  val of_termlit: termlit -> term
  val assert_sort_check: Sort.t -> termlit -> unit
  val eval_sym: sym -> termlit
  val eval: (sym, Sort.t) Map.Poly.t -> term -> termlit
end

module Term : TermType = struct
  (** Construction *)
  let info_id_count = ref 0
  (*let get_info_id () = incr info_id_count; !info_id_count*)
  let mk_var var =
    incr info_id_count;
    Var(var, Dummy(*ID (get_info_id ())*))
  let mk_con sym =
    incr info_id_count;
    Con(sym, Dummy(*ID (get_info_id ())*))
  let mk_app t1 t2 =
    incr info_id_count;
    App(t1, t2, Dummy(*ID (get_info_id ())*))
  let mk_apps t ts = List.fold ~f:mk_app ~init:t ts
  let mk_sym_app sym args = mk_apps (mk_con sym) args
  let mk_var_app var args = mk_apps (mk_var var) args

  let mk_bind bind var sort term =
    incr info_id_count;
    Bin(bind, var, sort, term, Dummy(*ID (get_info_id ())*))
  let mk_let var sort t1 t2 =
    incr info_id_count;
    Let(var, sort, t1, t2, Dummy(*ID (get_info_id ())*))
  let mk_tyapp term sort =
    incr info_id_count;
    TyApp(term, sort, Dummy(*ID (get_info_id ())*))
  let mk_tylam svar term =
    incr info_id_count;
    TyLam(svar, term, Dummy(*ID (get_info_id ())*))
  let mk_lambda args term =
    List.fold_right args ~init:term ~f:(fun (tvar, sort) acc ->
        mk_bind Lambda tvar sort acc)

  (** Observation *)
  let is_var = function Var(_, _) -> true | _ -> false
  let is_con = function Con(_, _) -> true | _ -> false
  let is_app = function App(_, _, _) -> true | _ -> false
  let is_lam = function Bin(Lambda, _, _, _, _) -> true | _ -> false
  let is_bin = function Bin(_, _, _, _, _) -> true | _ -> false
  let is_let = function Let(_, _, _, _, _) -> true | _ -> false
  let is_tyapp = function TyApp(_, _, _) -> true | _ -> false
  let is_tylam = function TyLam(_, _, _) -> true | _ -> false

  let fvs_of term =
    let rec aux ~next = function
      | Var(var, _) -> 
        if LogicOld.is_dummy_term var None then next Set.Poly.empty
        else next @@ Set.Poly.singleton var
      | Con(_, _) -> next @@ Set.Poly.empty
      | App(t1, t2, _) -> aux t1 ~next:(fun fvs1 -> aux t2 ~next:(fun fvs2 -> next @@ Set.Poly.union fvs1 fvs2))
      | Bin(_, var, _, term, _) -> aux term ~next:(fun fvs -> next @@ Set.Poly.remove fvs var)
      | Let(var, _, t1, t2, _) ->
        aux t1 ~next:(fun fvs1 -> aux t2 ~next:(fun fvs2 -> next @@ Set.Poly.union fvs1 @@ Set.Poly.remove fvs2 var))
      | TyApp(term, _, _)
      | TyLam(_, term, _) -> aux term ~next
    in aux term ~next:(fun fvs -> fvs)

  let rec pvar_of_atom = function
    | Var(tvar, _) -> tvar
    | App(t, _, _) -> pvar_of_atom t
    | _ -> assert false

  let rec ast_size = function
    | Var(_, _) | Con(_, _) -> 1
    | App(t1, t2, _) | Let(_, _, t1, t2, _) ->
      ast_size t1 + ast_size t2 + 1
    | Bin(_, _, _, term, _) | TyApp(term, _, _) | TyLam(_, term, _) ->
      ast_size term + 1

  (** Construction *)
  let mk_binds binder bounds body =
    let ftv = fvs_of body in
    let bounds = List.filter ~f:(fun (tvar, _) -> Core.Set.Poly.mem ftv tvar) bounds in
    List.fold_right bounds ~init:body ~f:(fun (tvar, sort) -> mk_bind binder tvar sort)

  (** Destruction *)
  let let_var = function
    | Var(var, info) -> (var, info)
    | _ -> assert false
  let let_con = function
    | Con(sy, info) -> (sy, info)
    | _ -> assert false
  let let_app = function
    | App(t1, t2, info) -> (t1, t2, info)
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
    | Bin(bind, var, sort, term, info) -> (bind, var, sort, term, info)
    | _ -> assert false
  let let_let = function
    | Let(var, sort, t1, t2, info) -> (var, sort, t1, t2, info)
    | _ -> assert false
  let let_tyapp = function
    | TyApp(term, sort, info) -> (term, sort, info)
    | _ -> assert false
  let let_tylam = function
    | TyLam(svar, term, info) -> (svar, term, info)
    | _ -> assert false
  let let_lam =
    let rec aux args = function
      | Bin(Lambda, tvar, sort, term, _) -> aux ((tvar, sort) :: args) term
      | term -> List.rev args, term
    in
    aux []

  (** Sorts *)
  let rec subst_sort_aux s1 svar s2 = match s1 with
    | Sort.SVar v when Stdlib.(=) v svar -> s2
    | Sort.SArrow (s11, s12) -> Sort.SArrow(subst_sort_aux s11 svar s2, subst_sort_aux s12 svar s2)
    | Sort.SForAll (svar', s1) -> if Stdlib.(=) svar' svar then failwith "The different SVar use the same variable" else
        Sort.SForAll (svar', subst_sort_aux s1 svar s2)
    | _ -> s1
  let subst_sort s1 s2 = match s1 with
    | Sort.SForAll (svar, s1) -> subst_sort_aux s1 svar s2
    | _ -> failwith "TyApp can be used only for SForAll"

  let open_arity_of_sym sort_of_sym sym = Sort.arity_of @@ sort_of_sym sym
  let rec open_sort_of sort_of_sym var_env = function
    | Var(v, _) -> SortMap.find_exn var_env v
    | Con(sym, _) -> sort_of_sym sym
    | App(t1, t2, _) -> begin
        match open_sort_of sort_of_sym var_env t1, open_sort_of sort_of_sym var_env t2 with
        | Sort.SArrow(s11, s12), s2 when Stdlib.(=) s11 s2 -> s12
        | _ -> failwith "The sort of App is unmached"
      end
    | Bin(bind, tvar, sort, term, _) -> begin
        match bind with
        | Lambda ->
          let new_var_env = SortMap.add_exn var_env ~key:tvar ~data:sort in
          open_sort_of sort_of_sym new_var_env term
        | _ -> failwith "The sort of Bin is not implemented yet"
      end
    | Let(v, sort, t1, t2, _) ->
      if not (Stdlib.(=) sort (open_sort_of sort_of_sym var_env t1)) then failwith "The sort of let-expression is wrong" else
        let new_var_env = SortMap.add_exn var_env ~key:v ~data:sort in
        open_sort_of sort_of_sym new_var_env t2
    | TyApp(term, sort, _) -> begin
        match term with
        | Con(sym, _) -> subst_sort (sort_of_sym sym) sort
        | TyApp _ -> failwith "it is not implemented yet"
        | TyLam _ -> failwith "it is not implemented yet"
        | _ -> failwith "The sort of term cannot apply another sort"
      end
    | TyLam _ -> failwith "it is not implemented yet"

  let sym_sort_map = Map.Poly.empty
  let sort_of_sym = Map.Poly.find_exn sym_sort_map
  let arity_of_sym = open_arity_of_sym sort_of_sym
  let sort_of = open_sort_of sort_of_sym

  (** Substitution *)
  let rec rename map = function
    | Var(var, info) -> begin
        match Map.Poly.find map var with
        | None -> Var(var, info)
        | Some var' -> mk_var var'
      end
    | Con(_, _) as c -> c
    | App(t1, t2, info) -> App(rename map t1, rename map t2, info)
    | Bin(bind, var, sort, term, info) ->
      let map' = Map.Poly.remove map var in
      Bin(bind, var, sort, rename map' term, info)
    | Let(var, sort, t1, t2, info) ->
      let map' = Map.Poly.remove map var in
      Let (var, sort, rename map t1, rename map' t2, info)
    | TyApp(term, sort, info) -> TyApp(rename map term, sort, info)
    | TyLam(svar, term, info) -> TyLam(svar, rename map term, info)
  let rec subst env t =
    let rec aux ~next env = function
      | Var(var, info) -> begin
          match Map.Poly.find env var with
          | None -> next (Var(var, info))
          | Some t -> next t
        end
      | Bin(bind, var, sort, term, info) ->
        let var' = Ident.mk_fresh_tvar () in
        let env' = Map.Poly.add_exn (Map.Poly.remove env var) ~key:var ~data:(mk_var var') in
        aux env' term ~next:(fun t -> next @@ Bin(bind, var', sort, t, info))
      | Let(var, sort, t1, t2, info) ->
        let var' = Ident.mk_fresh_tvar () in
        let env' = Map.Poly.add_exn (Map.Poly.remove env var) ~key:var ~data:(mk_var var') in
        aux env t1 ~next:(fun t1' -> aux env' t2 ~next:(fun t2' -> next @@ Let(var', sort, t1', t2', info)))
      | App(t1, t2, _) -> aux env t1 ~next:(fun t1' -> aux env t2 ~next:(fun t2' -> next @@ beta_reduction t1' [t2']))
      | TyApp(term, sort, info) -> aux env term ~next:(fun t -> next @@ TyApp(t, sort, info))
      | TyLam(svar, term, info) -> aux env term ~next:(fun t -> next @@ TyLam(svar, t, info))
      | t -> next t
    in
    aux env t ~next:(fun t -> t)
  and beta_reduction term args =
    let rec aux env term args =
      match term, args with
      | Bin (Lambda, var, _sort, term', _), arg :: args' ->
        aux (Map.Poly.add_exn env ~key:var ~data:arg) term' args'
      | _, [] -> subst env term
      | _, _ -> mk_apps term args
    in
    aux Map.Poly.empty term args
  (*match term, args with
    | Bin (Lambda, var, _sort, term', _), arg :: args' ->
    beta_reduction (subst (Map.Poly.singleton var arg) term') args'
    | _, [] -> term
    | _, _ -> mk_apps term args*)
  let refresh (senv, t) =
    let map = SortMap.to_map @@ SortMap.map senv ~f:(fun _ -> Ident.mk_fresh_tvar()) in
    SortMap.rename_keys_map map senv, rename map t
  (*let rec unify t1 t2 =
    match (t1, t2) with
    | Var (tvar, _), t | t, Var (tvar, _) -> (* ToDo: occurs check *)
      Map.Poly.singleton tvar t |> Option.some
    | App (Var (tvar1, _), t1, _), App (Var (tvar2, _), t2, _) ->
      if Stdlib.(=) tvar1 tvar2 then unify t1 t2 else None
    | Con (s1, _), Con (s2, _) ->
      if Stdlib.(=) s1 s2 then Some Map.Poly.empty else None
    | App (t11, t12, _), App (t21, t22, _) -> (
        match unify t11 t21, unify t12 t22 with
        | Some th1, Some th2 ->
          Map.fold th1 ~f:(fun ~key ~data map ->
              match Map.Poly.add ~key:key ~data:data map with
              | `Ok map' -> map' | _ -> map) ~init:th2
          |> Option.some
        | _, _ -> None
      )
    | _ -> None*)

  (** Transformation *)
  let reduce_sort_map (senv, t) =
    let fvs = fvs_of t in
    SortMap.filter_keys senv ~f:(Set.Poly.mem fvs), t

  (** Printing *)
  let open_str_of str_of_sort str_of_sym =
    let rec str_of = function
      | Var(Ident.Tvar id, _) ->
        Printf.sprintf "(%s)" id
      | Con(sym, _) ->
        Printf.sprintf "(%s)" (str_of_sym sym)
      | App (t1, t2, _) ->
        Printf.sprintf "(%s, %s)" (str_of t1) (str_of t2)
      | Bin(bind, Ident.Tvar id, sort, term, _) ->
        Printf.sprintf "%s %s:%s. (%s)"
          (match bind with | Mu -> "Mu" | Nu -> "Nu" | Lambda -> "Lam" | Forall -> "forall" | Exists -> "exists")
          id (str_of_sort sort)(str_of term)
      | Let(Ident.Tvar id, sort, t1, t2, _) ->
        Printf.sprintf "Let %s:%s = %s (%s)"
          id (str_of_sort sort) (str_of t1) (str_of t2)
      | TyApp(term, sort, _) ->
        Printf.sprintf "(%s)[%s]" (str_of term) (str_of_sort sort)
      | TyLam(svar, term, _) ->
        Printf.sprintf "%s. (%s)"
          (match svar with | Ident.Svar s -> s) (str_of term)
    in str_of
  let rec open_str_of_sort str_of_sort = function
    | Sort.SArrow(s1, s2) -> Printf.sprintf "%s -> %s" (open_str_of_sort str_of_sort s1) (open_str_of_sort str_of_sort s2)
    | Sort.SVar (Ident.Svar s) -> s
    | Sort.SForAll(Ident.Svar v, s) -> Printf.sprintf "(forall %s. %s)" v (open_str_of_sort str_of_sort s)
    | sort -> str_of_sort sort
  let open_str_of_subst str_of subst =
    String.concat ~sep:"\n"
    @@ List.map (Map.Poly.to_alist subst) ~f:(fun (Ident.Tvar name, term) ->
        Printf.sprintf "%s |-> %s" name (str_of term))
  let str_of_sym _ = failwith "Term.str_of_sym"
  let str_of_termlit _ = failwith "Term.str_of_termlit"
  let str_of_sort _ = failwith "Term.str_of_sort"
  let str_of = open_str_of str_of_sort str_of_sym
  let str_of_subst = open_str_of_subst str_of

  (** Evaluation *)
  let open_assert_sort_check assert_sort_check_of =
    let assert_sort_check sort = function
      | FunLit _ -> begin
          match sort with
          | Sort.SArrow (_, _) -> ()
          | _ -> assert false
        end
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
      | Let(x, _, t1, t2, _) -> let l1 = eval t1 in
        eval @@ subst (Map.Poly.singleton x @@ of_termlit l1) t2
      | Bin (_, _, _, _, _) -> failwith "eval of Lam is not implemented yet"
      | TyApp(term, sort, _) -> begin
          match eval term with
          | SFunLit sfun -> sfun sort
          | _ -> failwith "invalid type for TyApp"
        end
      | TyLam (_, _, _) -> failwith "invalid type for TyLam"
    in eval

  let is_termlit _ = false
  let of_termlit _ = failwith "Term.of_termlit"
  let assert_sort_check _ _ = failwith "Term.assert_sort_check"
  let eval_sym _ = failwith "Term.eval_sym"
  let eval _ _ = failwith "Term.eval"
end

module type BoolTermType = sig
  include TermType

  type sym += True | False | And | Or | Not | Imply | Iff | Xor | IfThenElse | Eq | Neq
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

  val mk_forall: SortEnv.t -> term -> term
  val mk_exists: SortEnv.t -> term -> term
  val forall: SortEnv.t -> term -> term
  val exists: SortEnv.t -> term -> term

  (** Destruction *)

  val let_not: term -> term

  (** Observation *)
  val is_bool: term -> bool
  val is_true: term -> bool
  val is_false: term -> bool
  val is_not: term -> bool
  val is_atom: SortMap.t -> SortMap.t -> term -> bool

  val conjuncts_of: term -> term list
  val disjuncts_of: term -> term list

  (** Transformation *)
  val cnf_of: SortMap.t -> SortMap.t -> term -> (term Set.Poly.t * term Set.Poly.t * term) Set.Poly.t
  val nnf_of: term -> term
  val elim_imp: term -> term
end

module BoolTerm : BoolTermType = struct
  include Term

  type sym += True | False | And | Or | Not | Imply | Iff | Xor | IfThenElse | Eq | Neq
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
  let neg_of = mk_app (mk_not ())
  let imply_of t1 t2 = mk_apps (mk_imply ()) [t1; t2]
  let eq_of ty t1 t2 = mk_apps (mk_eq ty) [t1; t2]
  let neq_of ty t1 t2 = mk_apps (mk_neq ty) [t1; t2]

  let mk_forall args term =
    List.fold_right args ~init:term ~f:(fun (tvar, sort) -> mk_bind Forall tvar sort)
  let mk_exists args term =
    List.fold_right args ~init:term ~f:(fun (tvar, sort) -> mk_bind Exists tvar sort)
  let forall bounds body = mk_binds Forall bounds body
  let exists bounds body = mk_binds Exists bounds body

  (** Destruction *)
  let let_not t =
    match let_app t with
    | Con(Not, _), t, _ -> t
    | _, _, _ -> assert false

  (** Observation *)
  let is_bool term =
    if is_con term
    then let sym, _ = let_con term in Stdlib.(=) sym True || Stdlib.(=) sym False
    else false
  let is_true term =
    if is_con term
    then let sym, _ = let_con term in Stdlib.(=) sym True
    else false
  let is_false term =
    if is_con term
    then let sym, _ = let_con term in Stdlib.(=) sym False
    else false
  let is_not term =
    if is_app term then
      let t, _, _ = let_app term in
      if is_con t
      then let sym, _ = let_con t in Stdlib.(=) sym Not
      else false
    else false
  let rec is_atom exi_senv uni_senv = function
    | Var (tvar, _) ->
      (match SortMap.find exi_senv tvar, SortMap.find uni_senv tvar with
       | Some sort, None -> Stdlib.(=) (Sort.ret_of sort) SBool
       | None, Some _ -> false
       | Some _, Some _ -> failwith (Printf.sprintf "%s is doubly bound (is_atom)" (Ident.name_of_tvar tvar))
       | None, None -> failwith (Printf.sprintf "%s is not bound (is_atom)" (Ident.name_of_tvar tvar)))
    | App (t, _, _) -> is_atom exi_senv uni_senv t
    | _ -> false

  let rec conjuncts_of = function
    | App (_, _, _) as t ->
      begin
        match let_apps t with
        | Con(And, _), args -> List.concat_map args ~f:conjuncts_of
        | _, _ -> [t]
      end
    | t -> [t]
  let rec disjuncts_of = function
    | App (_, _, _) as t ->
      begin
        match let_apps t with
        | Con(Or, _), args -> List.concat_map args ~f:disjuncts_of
        | _, _ -> [t]
      end
    | t -> [t]

  (** Transformation *)

  (* assume that term is in nnf *)
  let cnf_of exi_senv uni_senv term =
    let rec aux = function
      | Con (True, _) | App (Con (Not, _), Con (False, _), _) ->
        Set.Poly.empty
      | Con (False, _) | App (Con (Not, _), Con (True, _), _) ->
        Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
      | App (Con (Not, _), t, _) ->
        if is_atom exi_senv uni_senv t then
          Set.Poly.singleton (Set.Poly.empty, Set.Poly.singleton t, Set.Poly.empty)
        else
          Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (neg_of t))
      | App (App (Con (And, _), t1, _), t2, _) ->
        let cls1 = aux t1 in
        let cls2 = aux t2 in
        let phis, cls =
          Set.Poly.partition_tf (Set.Poly.union cls1 cls2) ~f:(fun (ps, ns, _phis) ->
              Set.Poly.is_empty ps && Set.Poly.is_empty ns)
          |> Pair.map (Set.Poly.map ~f:(fun (_, _, phis) -> or_of (Set.Poly.to_list phis))) ident
        in
        if Set.Poly.is_empty phis then cls
        else Set.Poly.add cls (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (and_of (Set.Poly.to_list phis)))
      | App (App (Con (Or, _), t1, _), t2, _) ->
        let cls1 = aux t1 in
        let cls2 = aux t2 in
        Set.cartesian_map cls1 cls2 ~f:(fun (ps1, ns1, phis1) (ps2, ns2, phis2) ->
            Set.Poly.union ps1 ps2, Set.Poly.union ns1 ns2, Set.Poly.union phis1 phis2)
      | t ->
        if is_atom exi_senv uni_senv t then
          Set.Poly.singleton (Set.Poly.singleton t, Set.Poly.empty, Set.Poly.empty)
        else
          Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton t)
    in
    aux term |> Set.Poly.map ~f:(fun (pos, neg, terms) -> pos, neg, or_of (Set.Poly.to_list terms))

  let rec nnf_of = function
    | App (Con (Not, _), Con (True, _), _) -> mk_bool false (* not true -> false *)
    | App (Con (Not, _), Con (False, _), _) -> mk_bool true (* not false -> true *)
    | App (Con (Not, _), App (Con (Not, _), term, _), _) -> nnf_of term (* not not t -> t *)
    | App (Con (Not, _), App (App (Con (And, _), t1, _), t2, _), _) -> (* not (t1 and t2) -> (not t1) or (not t2) *)
      mk_apps (mk_or ()) [nnf_of @@ neg_of t1; nnf_of @@ neg_of t2]
    | App (Con (Not, _), App (App (Con (Or, _), t1, _), t2, _), _) -> (* not (t1 or t2) -> (not t1) and (not t2) *)
      mk_apps (mk_and ()) [nnf_of @@ neg_of t1; nnf_of @@ neg_of t2]
    | App (Con (Not, _), App (App (Con (Imply, _), t1, _), t2, _), _) -> (* not (t1 => t2) -> t1 and (not t2) *)
      mk_apps (mk_and ()) [nnf_of t1; nnf_of @@ neg_of t2]
    | App (Con (Not, _), App (App (Con (Iff, _), t1, _), t2, _), _) -> (* not (t1 <=> t2) -> t1 and (not t2) or (not t1) and t2 *)
      mk_apps (mk_or ()) [mk_apps (mk_and ()) [nnf_of t1; nnf_of @@ neg_of t2];
                          mk_apps (mk_and ()) [nnf_of @@ neg_of t1; nnf_of t2]]
    | App (Con (Not, _), Bin (Forall, x, s, t, _), _) ->
      mk_bind Exists x s (nnf_of @@ neg_of t)
    | App (Con (Not, _), Bin (Exists, x, s, t, _), _) ->
      mk_bind Forall x s (nnf_of @@ neg_of t)
    | App (App (Con (And, _), t1, _), t2, _)  ->
      mk_apps (mk_con And) [nnf_of t1; nnf_of t2]
    | App (App (Con (Or, _), t1, _), t2, _)  ->
      mk_apps (mk_con Or) [nnf_of t1; nnf_of t2]
    | App (App (Con (Imply, _), t1, _), t2, _)  ->
      mk_apps (mk_con Or) [nnf_of @@ neg_of t1; nnf_of t2]
    | App (App (Con (Iff, _), t1, _), t2, _)  ->
      mk_apps (mk_and ()) [mk_apps (mk_or ()) [nnf_of @@ neg_of t1; nnf_of t2];
                           mk_apps (mk_or ()) [nnf_of t1; nnf_of @@ neg_of t2]]
    | Bin (b, x, s, t, _) -> mk_bind b x s (nnf_of t)
    | term -> term

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
    | Let(x, s, t1, t2, _) ->
      mk_let x s (elim_imp t1) (elim_imp t2)
    | TyApp(t, s, _) ->
      mk_tyapp (elim_imp t) s
    | TyLam(x, t, _) ->
      mk_tylam x (elim_imp t)
    | term -> term

  (** Sorts *)
  let sym_sort_map =
    Map.Poly.of_alist_exn
      [ (Not, Sort.SArrow(SBool, SBool));
        (And, Sort.SArrow(SBool, Sort.SArrow(SBool, SBool)));
        (Or, Sort.SArrow(SBool, Sort.SArrow(SBool, SBool)));
        (Imply, Sort.SArrow(SBool, Sort.SArrow(SBool, SBool)));
        (Xor, Sort.SArrow(SBool, Sort.SArrow(SBool, SBool)));
        (Iff, Sort.SArrow(SBool, Sort.SArrow(SBool, SBool)));
        (IfThenElse, let var = Ident.mk_fresh_svar () in
         Sort.SForAll(var, Sort.SArrow(SBool, Sort.SArrow(Sort.SVar var,
                                                          Sort.SArrow(Sort.SVar var, Sort.SVar var)))));
        (Eq, let var = Ident.mk_fresh_svar () in
         Sort.SForAll(var, Sort.SArrow(Sort.SVar var, Sort.SArrow(Sort.SVar var, SBool))));
        (Neq, let var = Ident.mk_fresh_svar () in
         Sort.SForAll(var, Sort.SArrow(Sort.SVar var, Sort.SArrow(Sort.SVar var, SBool)))) ]
  let sort_of_sym = Map.Poly.find_exn sym_sort_map
  let arity_of_sym = open_arity_of_sym sort_of_sym
  let sort_of = open_sort_of sort_of_sym

  (** Printing *)
  let str_of_sym = function
    | True -> "True"
    | False -> "False"
    | And -> "And"
    | Or -> "Or"
    | Not -> "Not"
    | Imply -> "Imply"
    | Xor -> "Xor"
    | Iff -> "Iff"
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
    | _ -> failwith "unknown sort"
  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym
  let str_of_subst = open_str_of_subst str_of

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
    | And -> FunLit (function | BoolLit x -> FunLit (function | BoolLit y -> BoolLit (x && y) | _ -> assert false)
                              | _ -> assert false)
    | Or  -> FunLit (function | BoolLit x -> FunLit (function | BoolLit y -> BoolLit (x || y) | _ -> assert false)
                              | _ -> assert false)
    | Not -> FunLit (function | BoolLit x -> BoolLit (not x) | _ -> assert false)
    | Imply -> FunLit (function | BoolLit x -> FunLit (function | BoolLit y -> BoolLit (not x || y) | _ -> assert false)
                                | _ -> assert false)
    | Xor -> FunLit (function | BoolLit x -> FunLit (function | BoolLit y -> BoolLit (Stdlib.(=) (not @@ x) y) | _ -> assert false)
                              | _ -> assert false)
    | Iff -> FunLit (function | BoolLit x -> FunLit (function | BoolLit y -> BoolLit (Stdlib.(=) x y) | _ -> assert false)
                              | _ -> assert false)
    | IfThenElse -> SFunLit (fun sort -> FunLit (function | BoolLit t1 ->
        FunLit (fun l2 -> assert_sort_check sort l2;
                 FunLit (fun l3 -> assert_sort_check sort l3; if t1 then l2 else l3))
                                                          | _ -> assert false))
    | Eq -> SFunLit (fun sort -> FunLit (fun l1 -> assert_sort_check sort l1;
                                          FunLit (fun l2 -> assert_sort_check sort l2; BoolLit (Stdlib.(=) l1 l2))))
    | Neq-> SFunLit (fun sort -> FunLit (fun l1 -> assert_sort_check sort l1;
                                          FunLit (fun l2 -> assert_sort_check sort l2; BoolLit (not @@ Stdlib.(=) l1 l2))))
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
  let mk_add () = mk_con (Add)
  let mk_sub () = mk_con (Sub)
  let mk_mult () = mk_con (Mult)
  let mk_div () = mk_con (Div)
  let mk_mod () = mk_con (Mod)
  let mk_neg () = mk_con (Neg)
  let mk_abs () = mk_con Abs
  let mk_rem () = mk_con (Rem)

  let sum = function
    | [] -> zero ()
    | t :: ts -> List.fold ~init:t ts ~f:(fun t1 t2 -> mk_apps (mk_add ()) [t1; t2])
  let prod = function
    | [] -> one ()
    | t :: ts -> List.fold ~init:t ts ~f:(fun t1 t2 -> mk_apps (mk_mult ()) [t1; t2])

  (** Sorts *)
  let sym_sort_map =
    Map.Poly.of_alist_exn
      [ (Add, Sort.SArrow(SInt, Sort.SArrow(SInt, SInt)));
        (Sub, Sort.SArrow(SInt, Sort.SArrow(SInt, SInt)));
        (Mult, Sort.SArrow(SInt, Sort.SArrow(SInt, SInt)));
        (Div, Sort.SArrow(SInt, Sort.SArrow(SInt, SInt)));
        (Mod, Sort.SArrow(SInt, Sort.SArrow(SInt, SInt)));
        (Neg, Sort.SArrow(SInt, SInt));
        (Abs, Sort.SArrow(SInt, SInt)) ]
  let sort_of_sym = function
    | Int _ -> SInt
    | sym -> Map.Poly.find_exn sym_sort_map sym
  let arity_of_sym = Term.open_arity_of_sym sort_of_sym
  let sort_of = Term.open_sort_of sort_of_sym

  (** Printing *)
  let str_of_sym = function
    | Int n -> Printf.sprintf "Int %s" (Z.to_string n)
    | Add -> "Add"
    | Sub -> "Sub"
    | Mult -> "Mult"
    | Div -> "Div"
    | Mod -> "Mod"
    | Neg-> "Neg"
    | Abs -> "Abs"
    | Rem -> "Rem"
    | _ -> failwith "IntTerm.str_of_sym"
  let str_of_termlit = function
    | IntLit n -> Z.to_string n
    | _ -> assert false
  let str_of_sort_theory = function
    | SInt -> "int"
    | _ -> failwith "unknown sort"
  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym
  let str_of_subst = open_str_of_subst str_of

  (** Evaluation *)
  let neg_sym = function
    | Add -> Sub | Sub -> Add
    | _ -> failwith "undefined "

  let is_termlit = function IntLit _ -> true | _ -> false
  let of_termlit = function IntLit n -> mk_int n | _ -> assert false
  let assert_sort_check_of_theory sort lit =
    match sort, lit with
    | SInt, IntLit _ -> ()
    | _ -> assert false
  let assert_sort_check = open_assert_sort_check assert_sort_check_of_theory
  let eval_sym = function
    | Int n -> IntLit n
    | Add -> FunLit (function | IntLit x -> FunLit (function | IntLit y -> IntLit (Z.(+) x y) | _ -> assert false)
                              | _ -> assert false)
    | Sub -> FunLit (function | IntLit x -> FunLit (function | IntLit y -> IntLit (Z.(-) x y) | _ -> assert false)
                              | _ -> assert false)
    | Mult-> FunLit (function | IntLit x -> FunLit (function | IntLit y -> IntLit (Z.( * ) x y) | _ -> assert false)
                              | _ -> assert false)
    | Div -> FunLit (function | IntLit x -> FunLit (function | IntLit y -> IntLit (Z.(/) x y) | _ -> assert false)
                              | _ -> assert false)
    | Mod -> FunLit (function | IntLit x -> FunLit (function | IntLit y -> IntLit (Z.(mod) x y) | _ -> assert false)
                              | _ -> assert false)
    | Neg -> FunLit (function | IntLit x -> IntLit (Z.neg x) | _ -> assert false)
    | Abs -> FunLit (function | IntLit x -> IntLit (Z.abs x) | _ -> assert false)
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
  let rzero () = mk_con (Real (Q.zero))
  let rone () = mk_con (Real (Q.one))
  let mk_real r = mk_con (Real r)
  let mk_from_float r = mk_con (Real (Q.of_float r))
  let mk_radd () = mk_con (RAdd)
  let mk_rsub () = mk_con (RSub)
  let mk_rmult () = mk_con (RMult)
  let mk_rdiv () = mk_con (RDiv)
  let mk_rneg () = mk_con (RNeg)
  let mk_rabs () = mk_con (RAbs)

  let sum = function
    | [] -> rzero ()
    | t :: ts -> List.fold ~init:t ts ~f:(fun t1 t2 -> mk_apps (mk_radd ()) [t1; t2])
  let prod = function
    | [] -> rone ()
    | t :: ts -> List.fold ~init:t ts ~f:(fun t1 t2 -> mk_apps (mk_rmult ()) [t1; t2])

  (** Sorts *)
  let sym_sort_map =
    Map.Poly.of_alist_exn
      [ (RAdd, Sort.SArrow(SReal, Sort.SArrow(SReal, SReal)));
        (RSub, Sort.SArrow(SReal, Sort.SArrow(SReal, SReal)));
        (RMult, Sort.SArrow(SReal, Sort.SArrow(SReal, SReal)));
        (RDiv, Sort.SArrow(SReal, Sort.SArrow(SReal, SReal)));
        (RNeg, Sort.SArrow(SReal, SReal));
        (RAbs, Sort.SArrow(SReal, SReal)) ]
  let sort_of_sym = function
    | Real _ -> SReal
    | sym -> Map.Poly.find_exn sym_sort_map sym
  let arity_of_sym = open_arity_of_sym sort_of_sym
  let sort_of = open_sort_of sort_of_sym

  (** Printing *)
  let str_of_sym = function
    | Real r -> Printf.sprintf "Real %s" (Q.to_string r)
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
    | _ -> failwith "unknown sort"
  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym
  let str_of_subst = open_str_of_subst str_of

  (** Evaluation *)
  let neg_sym = function
    | RAdd -> RSub | RSub -> RAdd
    | _ -> failwith "undefined "

  let is_termlit = function RealLit _ -> true | _ -> false
  let of_termlit = function RealLit r -> mk_real r | _ -> assert false
  let assert_sort_check_of_theory sort lit =
    match sort, lit with
    | SReal, RealLit _ -> ()
    | _ -> assert false
  let assert_sort_check = open_assert_sort_check assert_sort_check_of_theory
  let eval_sym = function
    | Real r -> RealLit r
    | RAdd -> FunLit (function | RealLit x -> FunLit (function | RealLit y -> RealLit (Q.(+) x y) | _ -> assert false)
                               | _ -> assert false)
    | RSub -> FunLit (function | RealLit x -> FunLit (function | RealLit y -> RealLit (Q.(-) x y) | _ -> assert false)
                               | _ -> assert false)
    | RMult-> FunLit (function | RealLit x -> FunLit (function | RealLit y -> RealLit (Q.( * ) x y) | _ -> assert false)
                               | _ -> assert false)
    | RDiv -> FunLit (function | RealLit x -> FunLit (function | RealLit y -> RealLit (Q.(/) x y) | _ -> assert false)
                               | _ -> assert false)
    | RNeg -> FunLit (function | RealLit x -> RealLit (Q.neg x) | _ -> assert false)
    | RAbs -> FunLit (function | RealLit x -> RealLit (Q.abs x) | _ -> assert false)
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

  let mk_to_real () = mk_con (ToReal)
  let mk_to_int () = mk_con (ToInt)

  (** Sorts *)
  let sym_sort_map = 
    Map.Poly.add_exn ~key:ToInt ~data:(Sort.SArrow(SReal, SInt)) @@
    Map.Poly.add_exn ~key:ToReal ~data:(Sort.SArrow(SInt, SReal)) @@
    (Map.force_merge RealTerm.sym_sort_map IntTerm.sym_sort_map)
  let sort_of_sym = Map.Poly.find_exn sym_sort_map
  let arity_of_sym = open_arity_of_sym sort_of_sym
  let sort_of = open_sort_of sort_of_sym

  (** Printing *)
  let str_of_sym = function
    | Int n -> "Int " ^ (Z.to_string n)
    | Real r -> "Real " ^ (Q.to_string r)
    | ToReal -> "ToReal"
    | ToInt -> "ToInt"
    | sym ->
      if Map.Poly.mem RealTerm.sym_sort_map sym then RealTerm.str_of_sym sym
      else if Map.Poly.mem IntTerm.sym_sort_map sym then IntTerm.str_of_sym sym
      else failwith "RealIntTerm.str_of_sym"
  let str_of_termlit = function
    | IntLit n -> Z.to_string n
    | RealLit r -> Q.to_string r
    | _ -> assert false
  let str_of_sort_theory = function
    | SInt -> "int"
    | SReal -> "real"
    | _ -> failwith "unknown sort"
  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym
  let str_of_subst = open_str_of_subst str_of

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
    | ToReal -> FunLit (function | IntLit x -> RealLit (Q.of_bigint x) | _ -> assert false)
    | ToInt -> FunLit (function | RealLit x -> IntLit (Q.to_bigint x) | _ -> assert false)
    | sym ->
      if Map.Poly.mem RealTerm.sym_sort_map sym then RealTerm.eval_sym sym
      else if Map.Poly.mem IntTerm.sym_sort_map sym then IntTerm.eval_sym sym
      else assert false
  let eval = open_eval eval_sym of_termlit
end

module type DatatypeType = sig
  type sel = 
    | Sel  of string * Sort.t
    | InSel of string * string * Sort.t list
  type cons =  {
    name :string ;
    sels : sel list
  }
  type func = | FCons of cons | FSel of sel
  type flag = | FDt | FCodt | Undef
  type dt = {
    name : string ;
    args : Sort.t list ;
    conses : cons list
  }
  type t =  {
    name : string ;
    dts  :  dt list;
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
  val full_name_of : t -> string
  val full_name_of_dt : dt -> string

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

  val is_finite : t -> bool
  val is_singleton : Sort.t -> bool
  val fsym_of_cons : t -> cons -> sym
  val fsym_of_sel : t -> sel -> sym
  val fsym_of_func : t -> func -> sym

  val of_old_flag : LogicOld.Datatype.flag -> flag
  val of_old_sort : LogicOld.Sort.t -> Sort.t
  val of_old_sel : LogicOld.Datatype.sel -> sel
  val of_old_cons : LogicOld.Datatype.cons -> cons
  val of_old_dt : LogicOld.Datatype.dt -> dt
  val of_old : LogicOld.Datatype.t -> t

  val to_old_flag : flag -> LogicOld.Datatype.flag
  val to_old_sort : Sort.t -> LogicOld.Sort.t
  val to_old_sel : sel -> LogicOld.Datatype.sel
  val to_old_cons : cons -> LogicOld.Datatype.cons
  val to_old_dt : dt -> LogicOld.Datatype.dt
  val to_old : t -> LogicOld.Datatype.t
end

module type DatatypeTermType = sig
  type dt
  type dtcons
  type dtsel
  type flag 
  type sym += 
    |DTSel of string * dt * Sort.t 
    |DTCons of string * Sort.t list * dt
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
  val str_of_sym : sym -> string
end

module rec Datatype : DatatypeType  = struct
  type sel = 
    | Sel  of string * Sort.t
    | InSel of string * string * Sort.t list
  type cons =  {
    name :string ;
    sels : sel list
  }
  type func = | FCons of cons | FSel of sel
  type flag = | FDt | FCodt | Undef
  type dt = {
    name : string ;
    args : Sort.t list ;
    conses : cons list
  }
  type t =  {
    name : string ;
    dts  :  dt list;
    flag : flag
  }

  let mk_dt name args = {name = name; args = args; conses = []}
  let create name dts flag = {name = name; dts = dts; flag = flag}
  let mk_uninterpreted_datatype ?(numeral=0) name = 
    let rec aux numeral =
      if numeral = 0 then []
      else Sort.SVar(Ident.mk_fresh_svar ()) :: (aux (numeral - 1))
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

  let is_dt t = match flag_of t with|FDt  -> true | _ -> false
  let is_codt t = match flag_of t with|FCodt  -> true | _ -> false
  let is_undef t = match flag_of t with|Undef   -> true | _ -> false
  let is_cons = function | FCons _ -> true | _ -> false
  let is_sel = function | FSel _ -> true | _ -> false

  let name_of_sel = function 
    | Sel(name, _) 
    | InSel(name, _, _) -> name
  let look_up_dt t name = 
    List.find ~f:(fun dt -> Stdlib.(=) name @@ name_of_dt dt) @@ dts_of t

  let dt_of t =
    match look_up_dt t @@ name_of t with
    | Some dt -> dt
    | _ -> assert false

  let conses_of t = dt_of t |> conses_of_dt
  let args_of t = dt_of t |> args_of_dt

  let full_name_of t =
    let name = name_of t in
    let args = args_of t in
    List.fold_left args ~init:(name) ~f:(
      fun ret arg -> ret ^ " " ^ Term.str_of_sort arg
    )
  let full_name_of_dt dt =
    let name = name_of_dt dt in
    let args = args_of_dt dt in
    List.fold_left args ~init:(name) ~f:(
      fun ret arg -> ret ^ " " ^ Term.str_of_sort arg
    )

  let rec update_dts dts dt =
    match dts with
    | [] -> []
    | dt1::tl -> 
      if Stdlib.(=) (name_of_dt dt1) @@ name_of_dt dt then
        dt::tl
      else
        dt1::(update_dts tl dt)

  let update_dt t dt = {t with dts = update_dts (dts_of t) dt}
  let rec update_dt_args t dt args his =
    let conses = conses_of_dt dt in
    let args1 = args_of_dt dt in
    let conses' =  List.fold2_exn args1 args ~init:(conses)~f:(
        fun (conses) arg1 arg ->
          List.map conses ~f:(
            fun cons -> 
              let sels = sels_of_cons cons in
              let sels' = List.map sels ~f:(
                  fun sel -> match sel with
                    | Sel(name, (Sort.SVar _ as svar)) when Stdlib.(=) svar arg1 ->
                      begin match arg with
                        |DatatypeTerm.SDT(t1) -> 
                          begin match look_up_dt t (name_of t1) with
                            | Some _ -> InSel(name, (name_of t1), (args_of t1))
                            | _ -> Sel(name, arg)
                          end
                        |_ -> Sel(name, arg)
                      end
                    | InSel(name, ret_name, args) ->
                      let args' = List.map args ~f:(fun svar -> if(Stdlib.(=) svar arg1) then arg else svar) in
                      InSel(name, ret_name, args')
                    | _ -> sel
                ) in {cons with sels = sels'}
          )
      ) in
    let t' = List.fold_left conses' ~init:t ~f:(
        fun t cons -> List.fold_left (sels_of_cons cons) ~init:t ~f:(
            fun t sel -> match sel with
              | Sel _ -> t
              | InSel (_, ret_sort, args) -> 
                if (not @@ List.exists his ~f:(Stdlib.(=) ret_sort)) then (
                  let t', dt' = update_dt_args (update_name t ret_sort) (dt_of @@ update_name t ret_sort) args (ret_sort::his) in
                  update_name (update_dt t' dt') (name_of t)
                )
                else t
          )
      ) in
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
    List.find ~f:(fun cons -> Stdlib.(=) name (name_of_cons cons))

  let look_up_sel_of_cons cons name =
    sels_of_cons cons |>
    List.find ~f:(fun sel -> Stdlib.(=) name (name_of_sel sel)) 

  let look_up_sel t name =
    conses_of t |>
    List.fold_left ~init:None ~f:(fun ret cons -> 
        match ret with
        | None -> sels_of_cons cons |>
                  List.find  ~f:(fun sel -> Stdlib.(=) name (name_of_sel sel))
        | _ -> ret)

  let look_up_func t name =
    match look_up_cons t name with
    | Some cons -> Some (FCons cons)
    | None -> 
      match look_up_sel t name with
      | Some sel -> Some (FSel sel)
      | None -> None

  let str_of_sel = function
    | Sel(name, ret_sort) ->
      sprintf "%s:%s" name (Term.str_of_sort ret_sort)
    | InSel(name, ret_name, args) ->      
      List.fold_left args ~init:(sprintf "%s:%s" name ret_name) ~f:(
        fun ret arg -> ret ^ "_" ^ Term.str_of_sort arg
      )

  let str_of_cons cons = 
    let name = name_of_cons cons in
    let sels = sels_of_cons cons in
    List.fold_left sels ~init:(name) ~f:(
      fun ret sel -> ret ^ " " ^ (str_of_sel sel)
    )

  let str_of_flag = function | FCodt -> "codt" | FDt -> "dt" | Undef -> "undef"

  let str_of t =
    let dt = dt_of t in
    sprintf "(%s:%s%s) %s" 
      (str_of_flag @@ flag_of t) 
      (name_of t) 
      (List.fold_left (args_of_dt dt) ~init:"" ~f:(
          fun ret arg -> ret ^ " " ^ Term.str_of_sort arg))
      (List.fold_left (conses_of_dt dt) ~init:"" ~f:(
          fun ret cons -> ret ^ "\n| " ^ str_of_cons cons))

  let sort_of t =   
    match flag_of t with
    | Undef -> DatatypeTerm.SUS(name_of t, args_of t)
    | _ -> DatatypeTerm.SDT(t)
  let sort_of_sel t = function 
    | Sel(_, sort) -> sort 
    | InSel(_, ret_name, args) -> 
      match look_up_dt t ret_name with
      | Some _ -> sort_of @@ update_args (update_name t ret_name) args
      | None -> failwith @@ sprintf "unkonwn sort:%s" ret_name

  let sorts_of_cons_args t cons= 
    sels_of_cons cons |>
    List.map ~f:(fun sel -> sort_of_sel t sel)

  let is_finite t = 
    let conses = conses_of t in
    not @@ List.exists conses ~f:(
      fun cons -> 
        let args = sorts_of_cons_args t cons in
        List.for_all args ~f:(
          fun arg -> Stdlib.(=) arg (DatatypeTerm.SDT(t)) && DatatypeTerm.is_finite_dt arg))

  let rec is_singleton sort =
    match sort with
    | DatatypeTerm.SDT(t) ->
      let conses = conses_of t in
      begin match conses with
        | [cons] -> 
          let args =  sorts_of_cons_args t cons in
          List.for_all args ~f:(
            fun arg -> Stdlib.(=) arg sort || is_singleton arg
          )
        | _ -> false 
      end
    | _ -> false

  let fresh_of t =
    let dts = dts_of t in
    let dts' = List.map dts ~f:(
        fun dt ->
          let args = args_of_dt dt in
          let args' = List.map args ~f:(function |Sort.SVar _ -> Sort.SVar(Ident.mk_fresh_svar ()) | arg -> arg) in
          snd @@ update_dt_args t dt args' []
      ) in
    {t with dts = dts'}

  let fsym_of_cons t cons =
    let t = fresh_of t in
    match look_up_cons t @@ name_of_cons cons with
    | Some cons -> DatatypeTerm.DTCons(name_of_cons cons, sorts_of_cons_args t cons, t)
    | None -> assert false

  let fsym_of_sel t sel =
    let t = fresh_of t in
    match look_up_sel t @@ name_of_sel sel with
    | None -> assert false
    | Some sel ->
      match sel with
      | Sel (name, ret_sort) -> DatatypeTerm.DTSel(name, t, ret_sort)
      | InSel (name, ret_name, args) -> 
        match look_up_dt t ret_name with
        | Some _ -> DatatypeTerm.DTSel(name, t, sort_of @@ update_args (update_name t ret_name) args)
        | None -> failwith @@ sprintf "unkonwn dt sort:%s" ret_name

  let fsym_of_func t func =
    match func with
    | FCons cons -> fsym_of_cons t cons
    | FSel sel -> fsym_of_sel t sel

  let rec of_old_flag = function
    | LogicOld.Datatype.FDt -> FDt
    | LogicOld.Datatype.FCodt -> FCodt
    | LogicOld.Datatype.Undef -> Undef
  and of_old_sort = function
    | LogicOld.Sort.SVar (ident) -> Sort.SVar(ident)
    | LogicOld.T_int.SInt -> IntTerm.SInt
    | LogicOld.T_real.SReal -> RealTerm.SReal
    | LogicOld.T_bool.SBool -> BoolTerm.SBool
    | LogicOld.T_dt.SDT(dt) -> DatatypeTerm.SDT(of_old dt)
    | LogicOld.T_dt.SUS(name, args) -> DatatypeTerm.SUS(name, List.map args ~f:of_old_sort)
    | old_sort -> failwith @@ sprintf "unsupport sort :%s" (LogicOld.Term.str_of_sort old_sort)
  and of_old_sel = function
    | LogicOld.Datatype.Sel(name, ret_sort) -> Sel(name, of_old_sort ret_sort)
    | LogicOld.Datatype.InSel(name, ret_name, args) -> InSel(name, ret_name, List.map args ~f:of_old_sort)
  and of_old_cons old_cons =
    let name = LogicOld.Datatype.name_of_cons old_cons in
    let sels = LogicOld.Datatype.sels_of_cons old_cons in
    {name = name; sels = List.map sels ~f:of_old_sel}
  and of_old_dt old_dt = 
    let name = LogicOld.Datatype.name_of_dt old_dt in
    let conses = LogicOld.Datatype.conses_of_dt old_dt in
    let args = LogicOld.Datatype.args_of_dt old_dt in
    {name = name; conses = List.map conses ~f:of_old_cons; args = List.map args ~f:of_old_sort}
  and of_old old_t = 
    let dts = LogicOld.Datatype.dts_of old_t in
    let name = LogicOld.Datatype.name_of old_t in
    let flag = LogicOld.Datatype.flag_of old_t in
    {name = name; flag = of_old_flag flag; dts = List.map dts ~f:of_old_dt}

  let rec to_old_flag = function
    | FDt -> LogicOld.Datatype.FDt
    | FCodt -> LogicOld.Datatype.FCodt
    | Undef -> LogicOld.Datatype.Undef
  and to_old_sort = function
    | Sort.SVar (ident) -> LogicOld.Sort.SVar(ident)
    | IntTerm.SInt -> LogicOld.T_int.SInt
    | RealTerm.SReal -> LogicOld.T_real.SReal
    | BoolTerm.SBool -> LogicOld.T_bool.SBool
    | DatatypeTerm.SDT(dt) -> LogicOld.T_dt.SDT(to_old dt)
    | DatatypeTerm.SUS(name, args) -> LogicOld.T_dt.SUS(name, List.map args ~f:to_old_sort)
    | _ -> assert false
  and to_old_sel = function
    | Sel(name, ret_sort) -> LogicOld.Datatype.Sel(name, to_old_sort ret_sort)
    | InSel(name, ret_name, args) -> LogicOld.Datatype.InSel(name, ret_name, List.map args ~f:to_old_sort)
  and to_old_cons cons =
    let name = name_of_cons cons in
    let sels = sels_of_cons cons |> List.map ~f:to_old_sel in
    LogicOld.Datatype.mk_cons name ~sels
  and to_old_dt dt = 
    let name = name_of_dt dt in
    let conses = conses_of_dt dt |> List.map ~f:to_old_cons in
    let args = args_of_dt dt |> List.map ~f:to_old_sort in
    {(LogicOld.Datatype.mk_dt name args) with conses = conses}
  and to_old t = 
    let dts = dts_of t in
    let name = name_of t in
    let flag = flag_of t in
    {name = name; flag = to_old_flag flag; dts = List.map dts ~f:to_old_dt}


  let look_up_base_cons t =
    let has_direct_base t =
      let conses = conses_of t in
      List.exists conses ~f:(
        fun cons -> 
          let sels = sels_of_cons cons in
          List.for_all sels ~f:(
            fun sel -> match sel with | Sel _ -> true | InSel _ -> false
          )
      )
    in
    let rec look_up_other_base t his=
      if List.exists his ~f:(fun t1 -> Stdlib.(=) (name_of t) (name_of t1)) then None
      else
        let conses = conses_of t in
        List.find conses ~f:(
          fun cons -> 
            let sels = sels_of_cons cons in
            List.for_all sels ~f:(
              fun sel -> match sel with 
                | Sel _ -> true 
                | InSel(_, ret_name, _) -> 
                  let ret_dt = update_name t ret_name in
                  if has_direct_base ret_dt then true
                  else Option.is_some @@ look_up_other_base ret_dt (t::his)
            )
        )
    in
    let conses = conses_of t in
    List.find conses ~f:(
      fun cons -> 
        let sels = sels_of_cons cons in
        List.for_all sels ~f:(
          fun sel -> match sel with 
            | Sel _ -> true 
            | InSel(_, ret_name, _) -> Option.is_some @@ look_up_other_base (update_name t ret_name) [t]
        ) 
    )

end
and DatatypeTerm : DatatypeTermType 
  with type dt := Datatype.t
   and type dtcons := Datatype.cons
   and type dtsel := Datatype.sel
   and type flag := Datatype.flag
= struct

  include Term

  type sym += 
    |DTSel of string * Datatype.t * Sort.t 
    |DTCons of string * Sort.t list * Datatype.t
  type Sort.t += 
    | SDT of Datatype.t  
    | SUS of string * (Sort.t list)

  let mk_cons dt name  =
    match Datatype.look_up_cons dt name with
    | Some(cons) ->
      let fsym = Datatype.fsym_of_cons dt cons in
      Term.mk_con fsym
    |_ -> failwith @@ "unkonwn cons :" ^ name

  let mk_sel dt name =
    match Datatype.look_up_sel dt name with
    | Some(sel) ->
      let fsym = Datatype.fsym_of_sel dt sel in
      Term.mk_con fsym
    | _ -> failwith @@ "unkonwn sel :" ^ name 

  let sels_of_cons fsym =
    match fsym with
    | DTCons(name, _, dt) -> 
      (match Datatype.look_up_cons dt name with
       | Some cons -> Datatype.sels_of_cons cons
       | _ -> assert false
      )
    | _ -> assert false

  let is_dt = function | SDT(dt) -> Datatype.is_dt dt | _ -> false
  let is_codt = function | SDT(dt) -> Datatype.is_dt dt | _ -> false
  let is_undef = function | SUS(_, _) -> true | _ -> false

  let rec is_finite_dt ?(his=[]) sort = 
    if (List.exists his ~f:(Stdlib.(=) sort)) then false
    else 
      match sort with
      | SDT(dt) -> 
        let conses = Datatype.conses_of dt in
        List.for_all conses ~f:(
          fun cons -> 
            let args = Datatype.sorts_of_cons_args dt cons in
            List.for_all args ~f:(fun arg -> is_finite_dt ~his:(sort::his) arg)
        )
      | _ -> false

  let is_cons = function App(Con (DTCons _, _), _, _) -> true | _ -> false
  let is_sel = function App(Con (DTSel _, _), _, _) -> true | _ -> false

  let str_of_sym = function
    | DTCons (name, _, _) -> name
    | DTSel (name, _, _) -> name
    | _ -> failwith "unkonwn sym"


  let mk_dummy f sort =
    match sort with
    | SDT(dt) when Datatype.is_dt dt-> 
      begin match Datatype.look_up_base_cons dt with
        | Some cons -> 
          let sorts = Datatype.sorts_of_cons_args dt cons in
          mk_apps (mk_cons dt (Datatype.name_of_cons cons)) (List.map sorts ~f:f)
        | None -> assert false
      end
    | SUS(name, _) -> mk_var @@ Ident.Tvar("dummy_" ^ name)
    | _ -> f sort
end

module type ArrayTermType = sig
  type sym +=
    | AStore
    | ASelect
    | AConst of Sort.t
  type Sort.t += SArray of Sort.t * Sort.t

  val mk_array_sort : Sort.t -> Sort.t -> Sort.t
  val mk_select : unit -> term
  val mk_store : unit -> term
  val mk_const_array : Sort.t -> term
  val index_sort_of : Sort.t -> Sort.t
  val elem_sort_of : Sort.t -> Sort.t
  val str_of_sym : sym -> string
end

module ArrayTerm : ArrayTermType = struct
  type sym +=
    | AStore
    | ASelect
    | AConst of Sort.t
  type Sort.t += SArray of Sort.t * Sort.t

  let mk_array_sort s1 s2 = SArray (s1, s2)
  let mk_select () = Term.mk_con ASelect 
  let mk_store () = Term.mk_con AStore 

  let mk_const_array sa  = Term.mk_con (AConst sa)

  let index_sort_of sa =
    match sa with
    | SArray (si, _) -> si
    | _ -> failwith "not array sort"

  let elem_sort_of sa =
    match sa with
    | SArray (_, se) -> se
    | _ -> failwith "not array sort"

  let str_of_sym = function
    | AStore -> "store"
    | ASelect -> "select"
    | AConst (_) -> sprintf "array_const " 
    | _ -> failwith "unknown sym"

end

module type RecFunTermType = sig
  type sym += |RecFVar of Ident.tvar * (Ident.tvar * Sort.t) list * Sort.t * term

  val mk_recfvar : Ident.tvar -> (Ident.tvar * Sort.t) list -> Sort.t -> term -> term
  val of_old_sym : (LogicOld.Sort.t -> Sort.t) -> (LogicOld.Term.t -> term) -> LogicOld.fun_sym -> sym
  val to_old_sym : (Sort.t -> LogicOld.Sort.t) -> (SortMap.t -> term -> term list -> LogicOld.Term.t)  -> sym -> LogicOld.fun_sym
  val str_of_sym : sym -> string
end
module RecFunTerm : RecFunTermType = struct
  type sym += |RecFVar of Ident.tvar * (Ident.tvar * Sort.t) list * Sort.t * term

  let mk_recfvar tvar env ret_sort body = Term.mk_con (RecFVar(tvar, env, ret_sort, body))

  let of_old_sym of_old_sort of_old_term = function
    | LogicOld.T_recfvar.RecFVar (tvar, env, ret_sort, body) -> 
      RecFVar (tvar, List.map env ~f:(fun (tvar, sort) -> (tvar, of_old_sort sort)), of_old_sort ret_sort, of_old_term body)
    | _ -> failwith "unknown sym"

  let to_old_sym old_sort_of (old_term_of) = function
    | RecFVar (tvar, env, ret_sort, body) -> 
      let senv = List.fold_left env ~init:(Map.Poly.empty) ~f:(fun senv (tvar, sort) -> Map.Poly.add_exn senv ~key:tvar ~data:sort) in
      let senv = Map.Poly.add_exn senv ~key:tvar ~data:ret_sort in
      LogicOld.T_recfvar.RecFVar (tvar, List.map env ~f:(fun (tvar, sort) -> (tvar, old_sort_of sort)), old_sort_of ret_sort, old_term_of senv body [])
    | _ -> failwith "unknown sym"

  let str_of_sym = function
    | RecFVar (tvar, _, _, _) -> Ident.name_of_tvar tvar
    | _ -> failwith "unknown sym"
end


module type ExtTermType = sig
  include RealIntTermType
  include BoolTermType
  include DatatypeTermType
  include ArrayTermType
  include RecFunTermType

  type sym += Leq | Geq | Lt | Gt | RLeq | RGeq | RLt | RGt | PDiv | IsInt
           | IsCons of string * Datatype.t | IsNotCons of string * Datatype.t

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

  (** Conversion *)
  val of_old_sort: LogicOld.Sort.t -> Sort.t
  val of_old_sort_bind: Ident.tvar * LogicOld.Sort.t -> Ident.tvar * Sort.t
  val of_old_sort_env: LogicOld.SortEnv.t -> SortEnv.t
  val to_old_sort: Sort.t -> LogicOld.Sort.t
  val to_old_sort_bind: Ident.tvar * Sort.t -> Ident.tvar * LogicOld.Sort.t

  val of_old_term: LogicOld.Term.t -> term
  val of_old_atom: LogicOld.Atom.t -> term
  val of_old_formula: LogicOld.Formula.t -> term

  val to_old_term: SortMap.t -> term -> term list -> LogicOld.Term.t
  val to_old_predicate: SortMap.t -> term -> LogicOld.Predicate.t
  val to_old_atom: SortMap.t -> term -> term list -> LogicOld.Atom.t
  val to_old_formula: SortMap.t -> term -> term list -> LogicOld.Formula.t
  val to_old_subst: SortMap.t -> (Ident.tvar, term) Map.Poly.t -> LogicOld.TermSubst.t

  val remove_dontcare_elem: (Ident.tvar * Sort.t) * term option -> Ident.tvar * term
  val remove_dontcare: ((Ident.tvar * Sort.t) * term option) list -> (Ident.tvar * term) list
end

module ExtTerm : ExtTermType
  with type dt := Datatype.t
   and type dtcons := Datatype.cons
   and type dtsel := Datatype.sel
   and type flag := Datatype.flag
= struct
  include BoolTerm
  include RealIntTerm
  include DatatypeTerm
  include ArrayTerm
  include RecFunTerm

  type sym += Leq | Geq | Lt | Gt | RLeq | RGeq | RLt | RGt | PDiv | IsInt 
           | IsCons of string * Datatype.t | IsNotCons of string * Datatype.t

  (** Construction *)
  let rec mk_dummy sort = match sort with
    | SInt -> IntTerm.zero () | SReal -> RealTerm.rzero ()
    | SBool -> BoolTerm.mk_bool false 
    | SDT _ | SUS _ -> DatatypeTerm.mk_dummy mk_dummy sort
    | SArray (_, se) -> mk_app (mk_const_array sort) (mk_dummy se)
    | _ -> assert false
  let mk_leq () = mk_con(Leq)
  let mk_geq () = mk_con(Geq)
  let mk_lt () = mk_con(Lt)
  let mk_gt () = mk_con(Gt)
  let mk_rleq () = mk_con(RLeq)
  let mk_rgeq () = mk_con(RGeq)
  let mk_rlt () = mk_con(RLt)
  let mk_rgt () = mk_con(RGt)
  let mk_pdiv () = mk_con(PDiv)
  let mk_isint () = mk_con(IsInt)
  let mk_int_ite () = mk_ite SInt
  let mk_real_ite () = mk_ite SReal
  let mk_int_eq () = mk_eq SInt
  let mk_real_eq () = mk_eq SReal
  let mk_int_neq () = mk_neq SInt
  let mk_real_neq () = mk_neq SReal
  let mk_is_cons name dt = mk_con(IsCons(name, dt))
  let mk_is_not_cons name dt = mk_con(IsNotCons(name, dt))

  let leq_of t1 t2 = mk_apps (mk_leq ()) [t1; t2]
  let geq_of t1 t2 = mk_apps (mk_geq ()) [t1; t2]
  let lt_of t1 t2 = mk_apps (mk_lt ()) [t1; t2]
  let gt_of t1 t2 = mk_apps (mk_gt ()) [t1; t2]

  (** Sorts *)
  let sym_sort_map =
    Map.force_merge
      (Map.force_merge RealIntTerm.sym_sort_map BoolTerm.sym_sort_map)
      (Map.Poly.of_alist_exn
         [ (Leq, Sort.SArrow(SInt, Sort.SArrow(SInt, SBool)));
           (Geq, Sort.SArrow(SInt, Sort.SArrow(SInt, SBool)));
           (Lt, Sort.SArrow(SInt, Sort.SArrow(SInt, SBool)));
           (Gt, Sort.SArrow(SInt, Sort.SArrow(SInt, SBool)));
           (RLeq, Sort.SArrow(SReal, Sort.SArrow(SReal, SBool)));
           (RGeq, Sort.SArrow(SReal, Sort.SArrow(SReal, SBool)));
           (RLt, Sort.SArrow(SReal, Sort.SArrow(SReal, SBool)));
           (RGt, Sort.SArrow(SReal, Sort.SArrow(SReal, SBool)));
           (PDiv, Sort.SArrow(SInt, Sort.SArrow(SInt, SBool)));
           (IsInt, Sort.SArrow(SReal, SBool)) ])
  let sort_of_sym = function
    | IntTerm.Int _ -> IntTerm.SInt
    | RealTerm.Real _ -> RealTerm.SReal
    | sym -> Map.Poly.find_exn sym_sort_map sym
  let arity_of_sym = open_arity_of_sym sort_of_sym
  let sort_of = open_sort_of sort_of_sym

  (** Printing *)
  let str_of_sym = function
    | True -> "True"
    | False -> "False"
    | Int n -> "Int " ^ (Z.to_string n)
    | Real r -> "Real " ^ (Q.to_string r)
    | Leq -> "Leq"
    | Geq -> "Geq"
    | Lt -> "Lt"
    | Gt -> "Gt"
    | RLeq -> "RLeq"
    | RGeq -> "RGeq"
    | RLt -> "RLt"
    | RGt -> "RGt"
    | PDiv -> "PDiv"
    | IsInt -> "IsInt"
    | IsCons (name, _) -> sprintf "Is %s" name
    | IsNotCons (name, _) -> sprintf "Is not %s" name
    | sym ->
      if Map.Poly.mem BoolTerm.sym_sort_map sym then BoolTerm.str_of_sym sym
      else if Map.Poly.mem RealIntTerm.sym_sort_map sym then RealIntTerm.str_of_sym sym
      else try DatatypeTerm.str_of_sym sym with _ ->
      try ArrayTerm.str_of_sym sym with _ -> failwith "ExtTerm.str_of_sym"
  let str_of_termlit = function
    | BoolLit true -> "true"
    | BoolLit false -> "false"
    | IntLit n -> Z.to_string n
    | RealLit r -> Q.to_string r
    | _ -> assert false
  let rec str_of_sort_theory = function
    | SInt -> "int"
    | SReal -> "real"
    | SBool -> "bool"
    | SDT(dt) -> Datatype.name_of dt
    | SUS(name, _) -> name
    | SArray (si, se) -> sprintf "array[%s, %s]" (str_of_sort_theory si) (str_of_sort_theory se)
    | _ -> failwith "unknown sort"
  let str_of_sort = open_str_of_sort str_of_sort_theory
  let str_of = open_str_of str_of_sort str_of_sym
  let str_of_subst = open_str_of_subst str_of

  (** Evaluation *)
  let is_termlit = function BoolTerm.BoolLit _ | IntTerm.IntLit _ | RealTerm.RealLit _ -> true | _ -> false
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
    | Leq -> FunLit (function | IntLit x -> FunLit (function | IntLit y -> BoolLit (Z.Compare.(<=) x y) | _ -> assert false)
                              | _ -> assert false)
    | Geq -> FunLit (function | IntLit x -> FunLit (function | IntLit y -> BoolLit (Z.Compare.(>=) x y) | _ -> assert false)
                              | _ -> assert false)
    | Lt -> FunLit (function | IntLit x -> FunLit (function | IntLit y -> BoolLit (Z.Compare.(<) x y) | _ -> assert false)
                             | _ -> assert false)
    | Gt -> FunLit (function | IntLit x -> FunLit (function | IntLit y -> BoolLit (Z.Compare.(>) x y) | _ -> assert false)
                             | _ -> assert false)
    | RLeq -> FunLit (function | RealLit x -> FunLit (function | RealLit y -> BoolLit (Q.(<=) x y) | _ -> assert false)
                               | _ -> assert false)
    | RGeq -> FunLit (function | RealLit x -> FunLit (function | RealLit y -> BoolLit (Q.(>=) x y) | _ -> assert false)
                               | _ -> assert false)
    | RLt -> FunLit (function | RealLit x -> FunLit (function | RealLit y -> BoolLit (Q.(<) x y) | _ -> assert false)
                              | _ -> assert false)
    | RGt -> FunLit (function | RealLit x -> FunLit (function | RealLit y -> BoolLit (Q.(>) x y) | _ -> assert false)
                              | _ -> assert false)
    | PDiv -> FunLit (function | IntLit x -> FunLit (function | IntLit y -> BoolLit (Z.Compare.(=) (Z.(mod) x y) Z.zero)
                                                              | _ -> assert false)
                               | _ -> assert false)
    | IsInt -> FunLit (function | RealLit x -> BoolLit (Z.Compare.(=) (Z.(mod) (Q.num x) (Q.den x)) Z.zero) | _ -> assert false)
    | sym ->
      if Map.Poly.mem BoolTerm.sym_sort_map sym then BoolTerm.eval_sym sym
      else if Map.Poly.mem RealIntTerm.sym_sort_map sym then RealIntTerm.eval_sym sym
      else assert false
  let eval = open_eval eval_sym of_termlit

  (** Conversion *)
  let rec of_old_sort = function
    | LogicOld.Sort.SArrow (s1, s2) -> Sort.SArrow (of_old_sort s1, of_old_sort s2)
    | LogicOld.T_bool.SBool -> SBool
    | LogicOld.T_real.SReal -> SReal
    | LogicOld.T_int.SInt -> SInt
    | LogicOld.T_dt.SDT (dt) -> SDT(Datatype.of_old dt)
    | LogicOld.T_dt.SUS (name, args) -> SUS(name, List.map args ~f:of_old_sort)
    | LogicOld.T_array.SArray(si, se) -> SArray(of_old_sort si, of_old_sort se)
    | _ -> assert false
  let of_old_sort_bind (x, s) = x, of_old_sort s
  let of_old_sort_env = LogicOld.SortEnv.map ~f:of_old_sort_bind
  let rec to_old_sort = function
    | Sort.SArrow (s1, s2) -> LogicOld.Sort.SArrow (to_old_sort s1, to_old_sort s2)
    | SBool -> LogicOld.T_bool.SBool
    | SReal -> LogicOld.T_real.SReal
    | SInt -> LogicOld.T_int.SInt
    | SDT(dt) -> LogicOld.T_dt.SDT (Datatype.to_old dt)
    | SUS(name, args) -> LogicOld.T_dt.SUS(name, List.map args ~f:to_old_sort)
    | SArray(si, se) -> LogicOld.T_array.SArray(to_old_sort si, to_old_sort se)
    | _ -> assert false
  let to_old_sort_bind (x, s) = x, to_old_sort s
  let of_unop = function
    | LogicOld.Formula.Not -> mk_not ()
  let of_binop = function
    | LogicOld.Formula.And -> mk_and ()
    | LogicOld.Formula.Or -> mk_or ()
    | LogicOld.Formula.Imply -> mk_imply ()
    | LogicOld.Formula.Iff-> mk_iff ()
  let rec of_old_fun_sym sym sargs =
    match sym, sargs with
    | LogicOld.FVar (x, _sorts), _ -> mk_var x
    | LogicOld.T_recfvar.RecFVar (_, _, _, _), _ -> Term.mk_con @@ RecFunTerm.of_old_sym of_old_sort of_old_term sym
    | LogicOld.T_bool.Formula phi, [] -> of_old_formula phi
    | LogicOld.T_bool.IfThenElse, [_; sort; _] -> mk_ite sort
    | LogicOld.T_real.Real r, [] -> mk_real r
    | LogicOld.T_real.RAdd, [_; _] -> mk_radd ()
    | LogicOld.T_real.RSub, [_; _] -> mk_rsub ()
    | LogicOld.T_real.RMult, [_; _] -> mk_rmult ()
    | LogicOld.T_real.RDiv, [_; _] -> mk_rdiv ()
    | LogicOld.T_real.RNeg, [_] -> mk_rneg ()
    | LogicOld.T_real.RAbs, [_] -> mk_rabs ()
    | LogicOld.T_int.Int n, [] -> mk_int n
    | LogicOld.T_int.Add, [_; _] -> mk_add ()
    | LogicOld.T_int.Sub, [_; _] -> mk_sub ()
    | LogicOld.T_int.Mult, [_; _] -> mk_mult ()
    | LogicOld.T_int.Div, [_; _] -> mk_div ()
    | LogicOld.T_int.Mod, [_; _] -> mk_mod ()
    | LogicOld.T_int.Neg, [_] -> mk_neg ()
    | LogicOld.T_int.Abs, [_] -> mk_abs ()
    | LogicOld.T_int.Rem, [_;_] -> mk_rem ()
    | LogicOld.T_real_int.ToReal, [_] -> mk_to_real ()
    | LogicOld.T_real_int.ToInt, [_] -> mk_to_int ()
    | LogicOld.T_dt.DTCons (name, _, dt), _ -> mk_cons (Datatype.of_old dt) name
    | LogicOld.T_dt.DTSel (name, dt, _), _ -> mk_sel (Datatype.of_old dt) name
    | LogicOld.T_array.AStore , _-> mk_store ()
    | LogicOld.T_array.ASelect , _ -> mk_select ()
    | LogicOld.T_array.AConst (sa), _ -> mk_const_array (of_old_sort sa)
    | _ -> assert false
  and of_old_pred_sym sym sargs =
    match sym, sargs with
    | LogicOld.T_bool.Eq, [sort; _] -> mk_eq sort
    | LogicOld.T_bool.Neq, [sort; _] -> mk_neq sort
    | LogicOld.T_int.Leq, [_; _]  -> mk_leq ()
    | LogicOld.T_int.Geq, [_; _] -> mk_geq ()
    | LogicOld.T_int.Lt, [_; _]  -> mk_lt ()
    | LogicOld.T_int.Gt, [_; _] -> mk_gt ()
    | LogicOld.T_real.RLeq, [_; _] -> mk_rleq ()
    | LogicOld.T_real.RGeq, [_; _] -> mk_rgeq ()
    | LogicOld.T_real.RLt, [_; _] -> mk_rlt ()
    | LogicOld.T_real.RGt, [_; _] -> mk_rgt ()
    | LogicOld.T_int.PDiv, [_; _] -> mk_pdiv ()
    | LogicOld.T_real_int.IsInt, [_] -> mk_isint ()
    | LogicOld.T_dt.IsCons (name, dt), _ -> mk_is_cons name (Datatype.of_old dt)
    | LogicOld.T_dt.IsNotCons (name, dt), _ -> mk_is_not_cons name (Datatype.of_old dt)
    | _ -> assert false
  and of_old_term = function
    | LogicOld.Term.Var (tvar, _sort, _) -> mk_var tvar
    | LogicOld.Term.FunApp (sym, args, _) ->
      let sargs = List.map args ~f:(fun t -> LogicOld.Term.sort_of t |> of_old_sort) in
      mk_apps (of_old_fun_sym sym sargs) (List.map ~f:of_old_term args)
  and of_old_atom = function
    | LogicOld.Atom.True _ -> mk_bool true
    | LogicOld.Atom.False _ -> mk_bool false
    | LogicOld.Atom.App (LogicOld.Predicate.Var (Ident.Pvar pvar, _), args, _) ->
      mk_apps (mk_var (Ident.Tvar pvar)) (List.map ~f:of_old_term args)
    | LogicOld.Atom.App (LogicOld.Predicate.Psym psym, args, _) ->
      let sargs = List.map args ~f:(fun t -> LogicOld.Term.sort_of t |> of_old_sort) in
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
      let bind = match bind with
        | LogicOld.Formula.Forall -> Forall
        | LogicOld.Formula.Exists -> Exists
        | LogicOld.Formula.Random _ -> failwith "unimplemented" in
      List.fold_right ~init:phi (LogicOld.SortEnv.list_of args)
        ~f:(fun (tvar, sort) acc -> mk_bind bind tvar (of_old_sort sort) acc)
    | LogicOld.Formula.LetRec _ -> failwith "conversion of letrec is not implemented yet"

  let to_old_unop = function
    | Not -> LogicOld.Formula.Not |> Option.some
    | _ -> None
  let to_old_binop = function
    | And -> LogicOld.Formula.And |> Option.some
    | Or -> LogicOld.Formula.Or |> Option.some
    | Imply -> LogicOld.Formula.Imply |> Option.some
    | Iff -> LogicOld.Formula.Iff |> Option.some
    | _ -> None
  let to_old_fun_sym to_old_term = function
    | IfThenElse -> LogicOld.T_bool.IfThenElse |> Option.some
    | Real r -> LogicOld.T_real.Real r |> Option.some
    | RAdd -> LogicOld.T_real.RAdd |> Option.some
    | RSub -> LogicOld.T_real.RSub |> Option.some
    | RMult -> LogicOld.T_real.RMult |> Option.some
    | RDiv -> LogicOld.T_real.RDiv |> Option.some
    | RNeg -> LogicOld.T_real.RNeg |> Option.some
    | RAbs -> LogicOld.T_real.RAbs |> Option.some
    | Int n -> LogicOld.T_int.Int n |> Option.some
    | Add -> LogicOld.T_int.Add |> Option.some
    | Sub -> LogicOld.T_int.Sub |> Option.some
    | Mult -> LogicOld.T_int.Mult |> Option.some
    | Div -> LogicOld.T_int.Div |> Option.some
    | Mod -> LogicOld.T_int.Mod |> Option.some
    | Neg -> LogicOld.T_int.Neg |> Option.some
    | Abs -> LogicOld.T_int.Abs |> Option.some
    | Rem -> LogicOld.T_int.Rem |> Option.some
    | ToReal -> LogicOld.T_real_int.ToReal |> Option.some
    | ToInt -> LogicOld.T_real_int.ToInt |> Option.some
    | DTCons (name, sorts, dt) -> LogicOld.T_dt.DTCons(name, List.map sorts ~f:to_old_sort, Datatype.to_old dt) |> Option.some
    | DTSel (name, dt, sort) -> LogicOld.T_dt.DTSel(name, Datatype.to_old dt, to_old_sort sort) |> Option.some
    | AStore -> LogicOld.T_array.AStore |> Option.some
    | ASelect -> LogicOld.T_array.ASelect |> Option.some
    | AConst (sa) -> LogicOld.T_array.AConst (to_old_sort sa) |> Option.some
    | RecFVar _ as sym -> RecFunTerm.to_old_sym to_old_sort to_old_term sym |> Option.some
    | _ -> None
  let to_old_pred_sym = function
    | Eq -> LogicOld.T_bool.Eq |> Option.some
    | Neq -> LogicOld.T_bool.Neq |> Option.some
    | Leq -> LogicOld.T_int.Leq |> Option.some
    | Geq -> LogicOld.T_int.Geq |> Option.some
    | Lt -> LogicOld.T_int.Lt |> Option.some
    | Gt -> LogicOld.T_int.Gt |> Option.some
    | RLeq -> LogicOld.T_real.RLeq |> Option.some
    | RGeq -> LogicOld.T_real.RGeq |> Option.some
    | RLt -> LogicOld.T_real.RLt |> Option.some
    | RGt -> LogicOld.T_real.RGt |> Option.some
    | PDiv -> LogicOld.T_int.PDiv |> Option.some
    | IsInt -> LogicOld.T_real_int.IsInt |> Option.some
    | IsCons (name, dt) -> LogicOld.T_dt.IsCons(name, Datatype.to_old dt) |> Option.some
    | IsNotCons (name, dt) -> LogicOld.T_dt.IsNotCons(name, Datatype.to_old dt) |> Option.some
    | _ -> None
  let sym_will_be_atom = function True | False -> true | _ -> false
  let rec to_old_term senv term args =
    let dummy_senv = SortEnv.of_old_sort_env of_old_sort !LogicOld.dummy_term_senv in
    match term with
    | Var (tvar, _) ->
      let sort = match SortMap.find senv tvar with
        | Some sort -> sort
        | None -> match List.find dummy_senv ~f:(fun (tvar1, _) -> Stdlib.(=) tvar tvar1) with
          | Some (_, sort) -> sort
          |_ ->
            print_endline @@ SortMap.str_of str_of_sort senv;
            failwith (Printf.sprintf "%s is not bound (old_term_of_term)" (Ident.name_of_tvar tvar)) in
      if Stdlib.(=) args [] then
        LogicOld.Term.mk_var tvar (to_old_sort sort)
      else
        let sargs, sret = Sort.args_ret_of sort in
        LogicOld.Term.mk_fvar_app tvar (List.map ~f:to_old_sort (sargs @ [sret]))
          (List.map args ~f:(fun term -> to_old_term senv term []))
    | Con (sym, _) -> begin
        match to_old_fun_sym (to_old_term) sym with
        | Some sym ->
          LogicOld.Term.mk_fsym_app sym @@ List.map args ~f:(fun term -> to_old_term senv term [])
        | None ->
          if sym_will_be_atom sym then LogicOld.T_bool.of_atom (to_old_atom senv term args)
          else LogicOld.T_bool.of_formula (to_old_formula senv term args)
      end
    | App (t1, t2, _) -> to_old_term senv t1 (t2::args)
    | Bin (Lambda, tvar, _, t, _) ->
      (match args with
       | [] -> assert false
       | arg :: args' ->
         to_old_term senv (subst (Map.Poly.singleton tvar arg) t) args')
    | Bin (_, _, _, _, _) -> assert false
    | Let _ -> failwith "let is not implemented yet"
    | TyApp (t, _, _) -> to_old_term senv t args
    | TyLam _ -> failwith "tylam is not implemented yet"
  and to_old_predicate senv term =
    match term with
    | Var (Ident.Tvar n as var, _) ->
      let sort = match SortMap.find senv var with
        | Some sort -> sort
        | None -> failwith (Printf.sprintf "%s is not bound (old_predicate_of_term)" (Ident.name_of_tvar var)) in
      let sargs = Sort.args_of sort in
      LogicOld.Predicate.mk_var (Ident.Pvar n) (List.map ~f:to_old_sort sargs)
    | Con (sym, _) -> begin
        match sym with
        | IfThenElse -> failwith "ite for bool not supported by old AST"
        | _ ->
          match to_old_pred_sym sym with
          | Some pred_sym -> LogicOld.Predicate.mk_psym pred_sym
          | None -> failwith (sprintf "to_old_predicate error:%s" @@ str_of term)
      end
    | App (_, _, _) -> assert false
    | Bin (Lambda, _, _, _, _) -> assert false
    | _ -> failwith "it is not implemented yet"
  and to_old_atom senv term args =
    match term with
    | Var (_, _) ->
      let pred = to_old_predicate senv term in
      let args = List.map ~f:(fun t -> to_old_term senv t []) args in
      LogicOld.Atom.mk_app pred args
    | Con (sym, _) -> begin
        match sym with
        | True -> assert (List.is_empty args); LogicOld.Atom.mk_true ()
        | False -> assert (List.is_empty args); LogicOld.Atom.mk_false ()
        | _ ->
          match sym, args with
          | IfThenElse, [_t1; _t2; _t3] -> assert false
          | _ ->
            let pred = to_old_predicate senv term in
            let args = List.map ~f:(fun t -> to_old_term senv t []) args in
            LogicOld.Atom.mk_app pred args
      end
    | App (t1, t2, _) -> to_old_atom senv t1 (t2::args)
    | Bin (Lambda, tvar, _, t, _) ->
      (match args with
       | [] -> assert false
       | arg :: args' ->
         to_old_atom senv (subst (Map.Poly.singleton tvar arg) t) args')
    | TyApp (t, _, _) -> to_old_atom senv t args
    | _ -> assert false
  and to_old_formula senv term args =
    let rec aux senv term args ~next =
      match term with
      | Var _ ->
        next @@ LogicOld.Formula.mk_atom @@ to_old_atom senv term args
      | Con (sym, _) -> begin
          match to_old_unop sym with
          | Some unop_sym -> begin
              match args with
              | [t] ->
                aux senv t [] ~next:(fun t' -> next @@ LogicOld.Formula.mk_unop unop_sym t')                
              | _ -> assert false
            end
          | None -> begin
              match to_old_binop sym with
              | Some binop_sym -> begin
                  match args with
                  | [t1; t2] ->
                    aux senv t1 [] ~next:(fun t1' -> aux senv t2 [] ~next:(fun t2' -> 
                        next @@ LogicOld.Formula.mk_binop binop_sym t1' t2'))
                  | _ -> failwith (String.concat ~sep:"\n" @@ List.map ~f:str_of args)
                end
              | None ->
                match sym, args with
                | IfThenElse, [t1; t2; t3] ->
                  aux senv t1 [] ~next:(
                    fun cond ->aux senv t2 [] ~next:(
                        fun then_branch -> aux senv t3 [] ~next:(
                            fun else_branch -> next @@ 
                              LogicOld.Formula.mk_or
                                (LogicOld.Formula.mk_and cond then_branch)
                                (LogicOld.Formula.mk_and (LogicOld.Formula.mk_neg cond) else_branch))))
                | _ -> next @@ LogicOld.Formula.mk_atom @@ to_old_atom senv term args
            end
        end
      | App (t1, t2, _) -> aux senv t1 (t2::args) ~next
      | Bin (Forall, tvar, s, t, _) ->
        (match args with
         | [] -> 
           aux (SortMap.set senv ~key:tvar ~data:s) t [] ~next:(
             fun t' -> next @@ LogicOld.Formula.mk_forall (LogicOld.SortEnv.singleton tvar (to_old_sort s)) @@ t')
         | _ -> assert false)
      | Bin (Exists, tvar, s, t, _) ->
        (match args with
         | [] -> 
           aux (SortMap.set senv ~key:tvar ~data:s) t [] ~next:(
             fun t' -> next @@ LogicOld.Formula.mk_exists (LogicOld.SortEnv.singleton tvar (to_old_sort s)) @@ t')
         | _ -> assert false)
      | Bin (Lambda, tvar, _, t, _) ->
        (match args with
         | [] -> assert false
         | arg :: args' ->
           aux senv (subst (Map.Poly.singleton tvar arg) t) args') ~next
      | TyApp (term, _, _) -> aux senv term args ~next
      | _ -> failwith (sprintf "to_old_formula error :%s" @@ str_of term)
    in aux senv term args ~next:(fun t -> t)
  let to_old_subst senv = Map.Poly.map ~f:(fun term -> to_old_term senv term [])

  let remove_dontcare_elem ((x, s), v) =
    match v with
    | None -> x, mk_dummy s
    | Some term -> x, term
  let remove_dontcare = List.map ~f:remove_dontcare_elem
end
