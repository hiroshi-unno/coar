(* Parser for SmtLib2 *)
open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld

(* TODO : should be replaced with appropriate configuration (dummy instantiation) *)
module Debug = Debug.Make(val Debug.Config.disable)

(* open Parsexp *)
module Sexp = Ppx_sexp_conv_lib.Sexp

let rec sort_of_sexp dtenv = function
  | Sexp.Atom "Int" -> T_int.SInt
  | Sexp.Atom "Real" -> T_real.SReal
  | Sexp.Atom "Bool" -> T_bool.SBool
  | Sexp.List (Sexp.Atom "Array" :: spars) ->
    begin match List.map spars ~f:(sort_of_sexp dtenv) with
      | [s1; s2] -> T_array.mk_array_sort s1 s2
      | _ -> assert false
    end
  | Sexp.List (Sexp.Atom name :: args) ->
    begin match DTEnv.look_up_dt dtenv name with
      | Some dt ->
        let dt = Datatype.fresh_of dt in
        let args = List.map args ~f:(sort_of_sexp dtenv) in
        T_dt.SDT (Datatype.update_args dt args)
      | _ -> failwith ("unknown sort : " ^ name)
    end
  | Sexp.Atom name ->
    Debug.print @@ lazy(sprintf "sort of sexp : %s" name);
    begin match DTEnv.look_up_dt dtenv name with
      | Some dt -> Datatype.sort_of @@ Datatype.fresh_of dt
      | _ -> Sort.SVar (Ident.Svar name)
    end
  | sexp -> failwith @@ Printf.sprintf "unknown sort: %s" (Sexp.to_string sexp)

let env_of_sexp dtenv = function
  | Sexp.List [Sexp.Atom var; Sexp.Atom "Int"] -> Ident.Tvar var, T_int.SInt
  | Sexp.List [Sexp.Atom var; Sexp.Atom "Real"] -> Ident.Tvar var, T_real.SReal
  | Sexp.List [Sexp.Atom var; sort] -> Ident.Tvar var, sort_of_sexp dtenv sort
  | sexp -> failwith @@ Printf.sprintf "unknown sort: %s" (Sexp.to_string sexp)

let of_params acc sexp dtenv =
  List.rev sexp |>
  List.fold ~f:(fun (acc, acc') -> function
      | Sexp.List [Sexp.Atom ident; sort] ->
        let e = Ident.Tvar ident, sort_of_sexp dtenv sort in
        Set.Poly.add acc e, Set.Poly.add acc' e
      | t -> failwith ("invalid param:" ^ Sexp.to_string t)) ~init:(Set.Poly.empty, acc)

let of_pred_sym = function
  | Sexp.Atom "=" -> T_bool.mk_eq
  | Sexp.Atom "<" -> T_num.mk_nlt
  | Sexp.Atom ">" -> T_num.mk_ngt
  | Sexp.Atom "<=" -> T_num.mk_nleq
  | Sexp.Atom ">=" -> T_num.mk_ngeq
  | op -> failwith @@ "parse error : unknown pred sym " ^ (Sexp.to_string_hum op)

let of_fun_sym = function
  | Sexp.Atom "+" -> T_num.mk_nadd
  | Sexp.Atom "-" -> T_num.mk_nsub
  | Sexp.Atom "*" -> T_num.mk_nmult
  | Sexp.Atom "/" -> T_real.mk_rdiv
  | Sexp.Atom "div" -> T_int.mk_div
  | Sexp.Atom "mod" -> T_int.mk_mod
  | Sexp.Atom "rem" -> T_int.mk_rem
  | Sexp.Atom "^" -> T_num.mk_npower
  | op -> failwith @@ "parse error : unknown fun sym " ^ (Sexp.to_string_hum op)

let rec of_formula tenv penv (fenv: LogicOld.FunEnv.t) dtenv phi = let open Formula in
  (fun ret ->
     Debug.print @@ lazy ("[smtlib2:of_formula]:" ^ Sexp.to_string phi);
     Debug.print @@ lazy ("[smtlib2:of_formula result]:" ^ Formula.str_of ret);
     ret) @@
  match phi with
  (* constant *)
  | Sexp.Atom "true" -> mk_atom (Atom.mk_true ())
  | Sexp.Atom "false" -> mk_atom (Atom.mk_false ())
  | Sexp.Atom ident -> begin
      match Set.Poly.find_map tenv ~f:(fun (key, sort) ->
          if Stdlib.(key = Ident.Tvar ident) then Some sort else None) with
      (* match List.Assoc.find ~equal:Stdlib.(=) tenv (Ident.Tvar ident) with *)
      | Some sort ->
        assert (Term.is_bool_sort sort);
        let var = Term.mk_var (Ident.Tvar ident) sort in
        let atom = Atom.mk_app (Predicate.Psym T_bool.Eq) [var; T_bool.of_atom (Atom.mk_true ())] in
        mk_atom atom
      | None -> begin
          (* let sorts = List.Assoc.find_exn ~equal:Stdlib.(=) penv (Ident.Pvar ident) in *)
          match Set.Poly.find penv
                  ~f:(fun (key, _sorts) -> Stdlib.(key = Ident.Pvar ident)) with
          | Some (_, sargs) ->
            assert (List.is_empty sargs);
            let pred = Predicate.mk_var (Ident.Pvar ident) sargs in
            mk_atom (Atom.mk_app pred [])
          | None ->
            match Set.Poly.find tenv ~f:(fun (key, _s) -> Stdlib.(key = Ident.Tvar ident)) with
            | Some (_, sort) ->
              let sargs, sret = Sort.args_ret_of sort in
              assert (Term.is_bool_sort sret);
              assert (List.is_empty sargs);
              let pred = Predicate.mk_var (Ident.Pvar ident) sargs in
              mk_atom (Atom.mk_app pred [])
            | None ->
              (* no arguments function *)
              match Map.Poly.find fenv (Ident.Tvar ident) with
              | Some ([], _, (Term.FunApp (T_bool.Formula phi, _, _)), _, _) -> phi
              | _ -> failwith (Printf.sprintf "%s is not bound" ident)
        end
    end

  (* logical operation *)
  | Sexp.List [Sexp.Atom "not"; phi] ->
    mk_neg (of_formula tenv penv fenv dtenv phi)
  | Sexp.List (Sexp.Atom "and" :: phis) ->
    let phis = List.rev_map phis ~f:(of_formula tenv penv fenv dtenv) in
    and_of phis
  | Sexp.List (Sexp.Atom "or" :: phis) ->
    let phis = List.rev_map phis ~f:(of_formula tenv penv fenv dtenv) in
    or_of phis
  | Sexp.List (Sexp.Atom "xor" :: phis) ->
    let phis = List.rev_map phis ~f:(of_formula tenv penv fenv dtenv) in
    xor_of phis
  | Sexp.List [Sexp.Atom "=>"; phi1; phi2] ->
    let phi1 = of_formula tenv penv fenv dtenv phi1 in
    let phi2 = of_formula tenv penv fenv dtenv phi2 in
    mk_imply phi1 phi2

  (* binder *)
  | Sexp.List [Sexp.Atom "forall"; Sexp.List params; phi] ->
    let params, tenv = of_params tenv params dtenv in
    let phi = of_formula tenv penv fenv dtenv phi in
    mk_forall (Set.Poly.to_list params) phi
  | Sexp.List [Sexp.Atom "exists"; Sexp.List params; phi] ->
    let params, tenv = of_params tenv params dtenv in
    let phi = of_formula tenv penv fenv dtenv phi in
    mk_exists (Set.Poly.to_list params) phi
  | Sexp.List [Sexp.Atom "random"; Sexp.List params; phi] ->
    let tenv, params = of_random_params tenv params penv fenv dtenv in
    let phi = of_formula tenv penv fenv dtenv phi in
    mk_randoms params phi

  (* predicate symbol application *)
  | Sexp.List [Sexp.Atom "=" as op; t1; t2]
  | Sexp.List [Sexp.Atom "<" as op; t1; t2]
  | Sexp.List [Sexp.Atom ">" as op; t1; t2]
  | Sexp.List [Sexp.Atom "<=" as op; t1; t2]
  | Sexp.List [Sexp.Atom ">=" as op; t1; t2] ->
    let t1 = of_term t1 tenv penv fenv dtenv  in
    let t2 = of_term t2 tenv penv fenv dtenv  in
    mk_atom (of_pred_sym op t1 t2)

  | Sexp.List (Sexp.Atom "distinct" :: ts) ->
    and_of @@ Set.Poly.to_list @@
    Set.fold_distinct_pairs ~f:(fun t1 t2 -> mk_atom @@ T_bool.mk_neq t1 t2) @@
    Set.Poly.of_list @@ List.map ~f:(fun t -> of_term t tenv penv fenv dtenv) ts
  (* let *)
  | Sexp.List [Sexp.Atom "let"; Sexp.List bounds; phi] ->
    let bounds = List.map bounds ~f:(function
        | Sexp.List [Sexp.Atom ident; t] ->
          let def = of_term t tenv penv fenv dtenv in
          Ident.Tvar ident, Term.sort_of def, def
        | x -> failwith @@ "Invalid param: " ^ (Sexp.to_string_hum x)) in
    let tenv', penv' =
      List.fold bounds ~init:(tenv, penv) ~f:(fun (tenv, penv) (tvar, sort, _) ->
          if Term.is_bool_sort sort then tenv, Set.Poly.add penv (Ident.tvar_to_pvar tvar, [])
          else Set.Poly.add tenv (tvar, sort), penv)
    in
    let phi = of_formula tenv' penv' fenv dtenv phi in
    List.fold ~init:phi ~f:(fun acc (var, sort, def) -> Formula.mk_let_formula var sort def acc) @@ List.rev bounds
  (* | Sexp.List [Sexp.Atom "let"; Sexp.List bounds; phi] ->
     (* print_endline "entry @ let"; *)
     let pbounds, tbounds =
      List.fold bounds ~init:(Map.Poly.empty, Map.Poly.empty)
        ~f:(fun (pbounds, tbounds) -> function
            | Sexp.List [Sexp.Atom ident; p_or_t] ->
              begin
                try
                  let phi = of_formula tenv penv fenv dtenv p_or_t in
                    (Map.Poly.add_exn pbounds ~key:(Ident.Pvar ident) ~data:([], phi)), tbounds
                with _ ->
                  let term = of_term p_or_t tenv penv fenv dtenv in
                  pbounds, Map.Poly.add_exn tbounds ~key:(Ident.Tvar ident) ~data:term
              end
            | x -> failwith @@ "Invalid param: " ^ (Sexp.to_string_hum x)) in
     let penv = Map.Poly.fold ~init:penv ~f:(fun ~key:var ~data:_ acc -> Set.Poly.add acc (var, [])) pbounds in
     let tenv = Map.Poly.fold ~init:tenv ~f:(fun ~key:var ~data:term acc -> Set.Poly.add acc (var, Term.sort_of term)) tbounds in
     let phi = of_formula tenv penv fenv dtenv phi in
     let phi = Map.Poly.fold tbounds ~init:phi ~f:(fun ~key:tvar ~data:term acc -> Formula.mk_let_formula tvar (Term.sort_of term) term acc) in
     Map.Poly.fold pbounds ~init:phi ~f:(fun ~key:pvar ~data:(_, phi) acc ->
      Formula.mk_let_formula (Ident.pvar_to_tvar pvar) T_bool.SBool (T_bool.of_formula phi) acc ) *)
  | Sexp.List [Sexp.Atom "ite"; cond; then_; else_] ->
    let cond = of_term cond tenv penv fenv dtenv in
    let then_ = of_term then_ tenv penv fenv dtenv in
    let else_ = of_term else_ tenv penv fenv dtenv in
    let t = T_bool.mk_if_then_else cond then_ else_ in
    if T_bool.is_sbool then_ then
      Formula.mk_atom @@
      Atom.mk_app (Predicate.Psym T_bool.Eq) [t; T_bool.of_atom (Atom.mk_true ())]
    else assert false
  | Sexp.List [Sexp.Atom "is_int"; t] ->
    let t = of_term t tenv penv fenv dtenv in
    mk_atom (T_real_int.mk_is_int t)
  | Sexp.List [Sexp.List [Sexp.Atom "_"; Sexp.Atom "is"; Sexp.List [Sexp.Atom name; _; _]]; t] ->
    let t = of_term t tenv penv fenv dtenv in
    mk_atom @@
    (match DTEnv.look_up_func dtenv name with
     | Some (dt, Datatype.FCons cons) -> T_dt.mk_is_cons dt (Datatype.name_of_cons cons) t
     | _ -> assert false)
  | Sexp.List [Sexp.List [Sexp.Atom "_"; Sexp.Atom "is"; Sexp.Atom name]; t] ->
    let t = of_term t tenv penv fenv dtenv in
    mk_atom @@
    (match DTEnv.look_up_func dtenv name with
     | Some (dt, Datatype.FCons cons) -> T_dt.mk_is_cons dt (Datatype.name_of_cons cons) t
     | _ -> assert false)
  (*TODO: support ':named' well*)
  | Sexp.List [Sexp.Atom "!"; t; Sexp.Atom ":named"; Sexp.Atom _] ->
    Debug.print @@ lazy ("! :named");
    let term = of_term t tenv penv fenv dtenv in
    if Term.is_bool_sort (Term.sort_of term) then of_formula tenv penv fenv dtenv t
    else failwith "must be bool fun"
  | Sexp.List (Sexp.Atom "!" :: t :: Sexp.Atom ":pattern" :: _) ->
    of_formula tenv penv fenv dtenv t
  (* predicate variable application *)
  | Sexp.List (Sexp.Atom ident :: args) ->
    Debug.print @@ lazy (sprintf "[formula]precicate %s" ident);
    let args = List.map args ~f:(fun t -> of_term t tenv penv fenv dtenv ) in
    (match Set.Poly.find penv ~f:(fun (key, _) -> Stdlib.(key = Ident.Pvar ident)) with
     | Some (_, sargs) ->
       let pred = Predicate.mk_var (Ident.Pvar ident) sargs in
       mk_atom (Atom.mk_app pred args)
     | None ->
       match Set.Poly.find tenv ~f:(fun (key, _sort) -> Stdlib.(key = Ident.Tvar ident)) with
       | Some (_, sort) ->
         let sargs, sret = Sort.args_ret_of sort in
         assert (Term.is_bool_sort sret);
         let pred = Predicate.mk_var (Ident.Pvar ident) sargs in
         mk_atom (Atom.mk_app pred args)
       | None ->
         match Map.Poly.find fenv (Tvar ident) with
         | Some (env, _, Term.FunApp (T_bool.Formula phi, _, _), false, _) ->
           assert (List.length args = List.length env);
           let var, _ = List.unzip env in
           let subst = Map.Poly.of_alist_exn @@ List.zip_exn var args in
           Formula.subst subst phi
         | Some (env, T_bool.SBool, _, true, _) ->
           assert (List.length args = List.length env);
           let _, sorts = List.unzip env in
           Formula.eq
             (Term.mk_fvar_app (Tvar ident) (sorts @ [T_bool.SBool]) args)
             (T_bool.mk_true ())
         | _ -> failwith (Printf.sprintf "%s is not bound" ident))
  | phi -> failwith @@ "parse error : " ^ (Sexp.to_string_hum phi)

and is_included_pvars tenv penv (fenv: LogicOld.FunEnv.t) dtenv= function
  | [] -> false
  | Sexp.List [Sexp.Atom _; t] :: sexps ->
    let phi = of_formula tenv penv fenv dtenv t in
    if (LogicOld.Formula.number_of_pvar_apps true phi) +
       (LogicOld.Formula.number_of_pvar_apps false phi) > 0 then true
    else is_included_pvars tenv penv fenv dtenv sexps
  | x::_ -> failwith @@ "invalid bounds: " ^ (Sexp.to_string_hum x)

and of_term t tenv penv (fenv: LogicOld.FunEnv.t) dtenv = let open Term in
  match t with
  | Sexp.Atom "true" -> T_bool.of_atom (Atom.mk_true ())
  | Sexp.Atom "false" -> T_bool.of_atom (Atom.mk_false ())
  | Sexp.Atom ident -> begin
      try
        (* case on integer/decimal constants *)
        T_num.mk_value ident
      with _ -> begin
          (* case on others *)
          match Set.Poly.find tenv ~f:(fun (key, _sort) -> Stdlib.(key = Ident.Tvar ident)) with
          | Some (_, sort) -> mk_var (Ident.Tvar ident) sort
          | None ->
            match Set.Poly.find penv ~f:(fun (key, _sorts) -> Stdlib.(key = Ident.Pvar ident)) with
            | Some (_, sorts) -> mk_var (Ident.Tvar ident) (Sort.mk_fun (sorts @ [T_bool.SBool]))
            | None ->
              match Map.Poly.find fenv (Ident.Tvar ident) with
              | Some (env, _, t, _, _) -> assert (List.is_empty env); t
              | None ->
                match DTEnv.look_up_func dtenv ident with
                | Some (dt, Datatype.FCons cons)
                  when List.is_empty @@ Datatype.sels_of_cons cons ->
                  T_dt.mk_cons dt ident []
                | _ -> failwith (Printf.sprintf "%s is not bound" ident)
        end
    end
  | Sexp.List [Sexp.Atom "-"; t] ->
    let t = of_term t tenv penv fenv dtenv in
    T_num.mk_nneg t
  | Sexp.List (Sexp.Atom "+" :: arg :: args) ->
    let arg = of_term arg tenv penv fenv dtenv in
    List.fold args ~init:arg ~f:(fun acc t -> T_num.mk_nadd acc (of_term t tenv penv fenv dtenv ))
(*
    let args = List.rev_map args ~f:(fun t -> of_term t tenv penv) in
    List.fold args ~init:arg ~f:(fun acc arg ->
        T_int.mk_add acc arg)*)
  | Sexp.List (Sexp.Atom "*" :: arg :: args) ->
    let arg = of_term arg tenv penv fenv dtenv  in
    List.fold args ~init:arg ~f:(fun acc t -> T_num.mk_nmult acc (of_term t tenv penv fenv dtenv ))
  | Sexp.List [Sexp.Atom "-" as op; t1; t2]
  | Sexp.List [Sexp.Atom "/" as op; t1; t2]
  | Sexp.List [Sexp.Atom "div" as op; t1; t2]
  | Sexp.List [Sexp.Atom "mod" as op; t1; t2]
  | Sexp.List [Sexp.Atom "rem" as op; t1; t2]
  | Sexp.List [Sexp.Atom "^" as op; t1; t2] ->
    let t1 = of_term t1 tenv penv fenv dtenv  in
    let t2 = of_term t2 tenv penv fenv dtenv  in
    (of_fun_sym op) t1 t2
  | Sexp.List [Sexp.Atom "ite"; cond; then_; else_] ->
    let cond = of_term cond tenv penv fenv dtenv  in
    let then_ = of_term then_ tenv penv fenv dtenv  in
    let else_ = of_term else_ tenv penv fenv dtenv  in
    T_bool.mk_if_then_else cond then_ else_

  (* let-expressions as term *)
  | Sexp.List [Sexp.Atom "let"; Sexp.List bounds; body] ->
    let aux bounds body =
      let bounds = List.rev_map bounds ~f:(function
          | Sexp.List [Sexp.Atom ident; t] ->
            Ident.Tvar ident, of_term t tenv penv fenv dtenv
          | x -> failwith @@ "invalid param : " ^ (Sexp.to_string_hum x)) in
      let tenv = List.fold bounds ~init:tenv ~f:(fun tenv (var, t) ->
          Set.Poly.add tenv (var, Term.sort_of t)) in
      let body = of_term body tenv penv fenv dtenv in
      List.fold bounds ~f:(fun acc (var, def) -> Term.mk_let_term var (Term.sort_of def) def acc) ~init:body
    in
    begin
      try if is_included_pvars tenv penv fenv dtenv bounds then
          failwith "Invalid let-expressions (It is not allowed to use let-term binding predicate applications into some name.)"
        else aux bounds body
      with _ -> aux bounds body
    end
  (* ToDo: support function applications *)
  | Sexp.List [Sexp.List [Sexp.Atom "_"; Sexp.Atom "is"; Sexp.Atom name]; t] ->
    let t = of_term t tenv penv fenv dtenv in
    let formula =
      Formula.mk_atom @@
      match DTEnv.look_up_func dtenv name with
      | Some (dt, Datatype.FCons cons) -> T_dt.mk_is_cons dt (Datatype.name_of_cons cons) t
      | _ -> assert false
    in
    Term.mk_fsym_app (T_bool.Formula formula) []
  | Sexp.List (Sexp.Atom ident :: args) when DTEnv.name_is_func dtenv ident ->
    Debug.print @@ lazy (sprintf "[term]datatype func %s" ident);
    let args = List.map args ~f:(fun t -> of_term t tenv penv fenv dtenv) in
    (match DTEnv.look_up_func dtenv ident with
     | Some (dt, Datatype.FCons (_)) -> T_dt.mk_cons dt ident args
     | Some (dt, Datatype.FSel (_)) ->
       begin match args with
         |[arg] -> T_dt.mk_sel dt ident arg
         | _ -> assert false
       end
     | _ -> T_bool.of_formula @@ of_formula tenv penv fenv dtenv t)
  | Sexp.List [Sexp.Atom "to_real"; t] ->
    let t = of_term t tenv penv fenv dtenv  in
    T_real_int.mk_to_real t
  | Sexp.List [Sexp.Atom "to_int"; t] ->
    let t = of_term t tenv penv fenv dtenv  in
    T_real_int.mk_to_int t
  | Sexp.List [Sexp.Atom "select"; t1; t2] ->
    let arr = of_term t1 tenv penv fenv dtenv in
    (match sort_of arr with
     | T_array.SArray (s1, s2) -> 
       let i = of_term t2 tenv penv fenv dtenv in
       T_array.mk_select s1 s2 arr i
     | _ -> failwith "")
  | Sexp.List [Sexp.Atom "store"; t1; t2; t3] ->
    let arr = of_term t1 tenv penv fenv dtenv in
    let i = of_term t2 tenv penv fenv dtenv in
    let e = of_term t3 tenv penv fenv dtenv in
    (match sort_of arr with
     | T_array.SArray (s1, s2) -> 
       T_array.mk_store s1 s2 arr i e
     | _ -> failwith "")
  | Sexp.List [Sexp.List [Sexp.Atom "as"; Sexp.Atom "const"; sort]; value] ->
    let arr_sort = sort_of_sexp dtenv sort in
    let arr_value = of_term value tenv penv fenv dtenv in
    (match arr_sort with
     | T_array.SArray (s1, s2) -> 
       T_array.mk_const_array s1 s2 arr_value
     | _ -> failwith "")
  | Sexp.List (Sexp.Atom ident :: args) ->
    begin
      match Map.Poly.find fenv (Tvar ident) with
      | Some (params, _, term, false, _) ->
        let args = List.map args ~f:(fun t -> of_term t tenv penv fenv dtenv ) in
        let var, _ = List.unzip params in
        let map = Map.Poly.of_alist_exn @@List.zip_exn var args in
        Term.subst map term
      | Some (params, ret_sort, _, true, _) ->
        Term.mk_fvar_app
          (Ident.Tvar ident)
          (List.map ~f:snd params @ [ret_sort])
          (List.map args ~f:(fun t -> of_term t tenv penv fenv dtenv))
      | _ ->
        begin
          match Set.Poly.find tenv ~f:(fun (key, _sort) -> Stdlib.(key = Ident.Tvar ident)) with
          | Some (_, sort) ->
            let atrms = List.map args ~f:(fun t -> of_term t tenv penv fenv dtenv) in
            let sargs, sret = Sort.args_ret_of sort in
            if Term.is_bool_sort sret then
              T_bool.of_formula @@ of_formula tenv penv fenv dtenv t
            else begin
              assert (List.length atrms = List.length sargs);
              Term.mk_fvar_app (Ident.Tvar ident) (sargs @ [sret]) (atrms)
            end
          | None ->
            T_bool.of_formula @@ of_formula tenv penv fenv dtenv t
        end end
  | _ -> T_bool.of_formula @@ of_formula tenv penv fenv dtenv t
and dist_of_sexp tenv penv fenv dtenv = function
  | Sexp.List [Sexp.Atom "Uniform"; t1; t2] ->
    let t1 = of_term t1 tenv penv fenv dtenv in
    let t2 = of_term t2 tenv penv fenv dtenv in
    Rand.mk_uniform t1 t2
  | Sexp.List [Sexp.Atom "Gauss"; t1; t2] ->
    let t1 = of_term t1 tenv penv fenv dtenv in
    let t2 = of_term t2 tenv penv fenv dtenv in
    Rand.mk_gauss t1 t2
  | Sexp.List [Sexp.Atom "IntUniform"; t1; t2] ->
    let t1 = of_term t1 tenv penv fenv dtenv in
    let t2 = of_term t2 tenv penv fenv dtenv in
    Rand.mk_int_uniform t1 t2
  | _ -> assert false
and of_random_params acc sexp penv fenv dtenv =
  List.rev sexp |>
  List.fold ~f:(fun (acc, params) -> function
      | Sexp.List [Sexp.Atom ident; dist] ->
        let rand = dist_of_sexp acc penv fenv dtenv dist in
        (Set.Poly.add acc (Ident.Tvar ident, Rand.sort_of rand),
         (Ident.Tvar ident, rand) :: params)
      | t -> failwith ("error of " ^ (Sexp.to_string t))) ~init:(acc, [])

let restrict_head bounds args fml =
  List.fold args
    ~init:(bounds, [], fml)
    ~f:(fun (bounds, args, fml) arg ->
        let arg_sort : Sort.t = Term.sort_of arg in
        let new_ident : Ident.tvar = Ident.mk_fresh_head_arg () in
        let new_arg : Term.t = Term.mk_var new_ident arg_sort in
        let bounds = (new_ident, arg_sort) :: bounds in
        let args = new_arg :: args in
        let fml =
          Formula.mk_and fml @@
          Formula.mk_atom @@ Atom.mk_app (Predicate.Psym T_bool.Eq) [new_arg; arg]
        in
        bounds, args, fml)

let is_available str =
  let logiclist = ["HORN";"QF_LIA";"QF_NRA";"QF_LIA";"QF_LRA";"QF_LIRA";"QF_NIA";"QF_NRA";"QF_NIRA";"LIA";"LRA";"NIA";"NRA";"SAT";"QF_DT";"QF_UF";"QF_ALIA";"ALL_SUPPORTED";"AUFLIA"] in
  List.exists logiclist ~f:(String.(=) str)

let mk_dt_sel dtenv dt dts sel =
  match sel with
  | Sexp.List [Sexp.Atom name; ret] ->
    begin match ret with
      | Sexp.Atom ret_name ->
        begin match List.find dts ~f:(fun dt -> Stdlib.(ret_name = Datatype.name_of_dt dt)) with
          | Some _ -> Datatype.mk_insel name ret_name (Datatype.args_of_dt dt)
          | None -> Datatype.mk_sel name @@ sort_of_sexp dtenv ret
        end
      | Sexp.List (Sexp.Atom ret_name :: args) ->
        begin match List.find dts ~f:(fun dt -> Stdlib.(ret_name = Datatype.name_of_dt dt)) with
          | Some _ ->
            if Stdlib.(Datatype.name_of_dt dt = ret_name) then
              Datatype.mk_insel name ret_name (Datatype.args_of_dt dt)
            else
              Datatype.mk_insel name ret_name (List.map args ~f:(sort_of_sexp dtenv))
          | None -> Datatype.mk_sel name @@ sort_of_sexp dtenv ret
        end
      | _ -> assert false
    end
  | _ -> assert false
let mk_dt_cons dtenv dt dts cons =
  match cons with
  | Sexp.Atom name
  | Sexp.List [Sexp.Atom name] -> Datatype.mk_cons name
  | Sexp.List (Sexp.Atom name :: sels) ->
    let sels = List.map sels ~f:(mk_dt_sel dtenv dt dts) in
    Datatype.mk_cons name ~sels
  | _ -> failwith @@ Sexp.to_string cons
let mk_new_datatypes dtenv dts funcs flag =
  let datatypes =
    List.map2_exn dts funcs ~f:(fun dt func ->
        match dt with
        | Sexp.List [Sexp.Atom name; Sexp.Atom "0"] -> Datatype.mk_dt name []
        | Sexp.List [Sexp.Atom name; Sexp.Atom _] ->
          begin match func with
            | Sexp.List (Sexp.List [Sexp.Atom "par"; Sexp.List args] :: _) ->
              Datatype.mk_dt name @@
              List.map args ~f:(function Sexp.Atom ident -> Sort.SVar (Ident.Svar ident) | _ -> assert false)
            | _ -> assert false
          end
        | _ -> assert false)
  in
  let datatypes =
    List.map2_exn datatypes funcs ~f:(fun dt -> function
        | Sexp.List (Sexp.List [Sexp.Atom "par"; Sexp.List _] :: conses)
        | Sexp.List conses ->
          let conses =
            List.fold_left conses ~init:[] ~f:(fun conses cons ->
                mk_dt_cons dtenv dt datatypes cons :: conses)
          in
          { dt with conses = conses }
        | _ -> assert false)
  in
  List.map datatypes ~f:(fun dt -> Datatype.create (Datatype.name_of_dt dt) datatypes flag)
let mk_old_datatypes dtenv dts flag args =
  let args = List.map args ~f:(function Sexp.Atom ident -> Sort.SVar (Ident.Svar ident) | _ -> assert false) in
  let datatypes =
    List.map dts ~f:(function
        | Sexp.List (Sexp.Atom name :: _) -> Datatype.mk_dt name args
        | _ -> assert false)
  in
  let datatypes =
    List.map2_exn datatypes dts ~f:(fun dt -> function
        | Sexp.List (_ :: conses) ->
          let conses =
            List.fold_left conses ~init:[] ~f:(fun conses cons ->
                mk_dt_cons dtenv dt datatypes cons :: conses)
          in
          { dt with conses = conses }
        | _ -> assert false)
  in
  List.map datatypes ~f:(fun dt -> Datatype.create (Datatype.name_of_dt dt) datatypes flag)


let rec toplevel acc tenv penv fnp_env wfp_env (fenv:LogicOld.FunEnv.t) dtenv = function
  | [] ->
    let acc =
      List.map acc ~f:(fun phi ->
          let phi' =
            phi
            |> Normalizer.normalize_let ~rename:true
            |> (Formula.elim_let_with_unknowns @@
                Set.Poly.map ~f:(fun (Ident.Pvar name) -> Ident.Tvar name) @@
                (Set.Poly.union_list [Set.Poly.map ~f:fst penv; Set.Poly.map ~f:fst fnp_env; Set.Poly.map ~f:fst wfp_env]))
            |> Normalizer.normalize
          in
          Debug.print @@ lazy (sprintf "[toplevel] %s" @@ Formula.str_of phi');
          phi')
    in
    Atomic.set
      LogicOld.ref_fenv
      (Map.force_merge (Map.Poly.filter fenv ~f:(fun (_, _, _, is_rec, _) -> is_rec)) @@
       Atomic.get LogicOld.ref_fenv);
    Ok (acc, tenv, penv, fnp_env, wfp_env, fenv, dtenv) (*(smt_of_formula acc tenv penv_all)*)
  | Sexp.List [Sexp.Atom "declare-var"; Sexp.Atom ident; sort] :: es ->
    let tenv' = Set.Poly.add tenv (Ident.Tvar ident, sort_of_sexp dtenv sort) in
    toplevel acc tenv' penv fnp_env wfp_env fenv dtenv es
  | Sexp.List [Sexp.Atom "set-logic"; Sexp.Atom logic] :: es when is_available logic ->
    toplevel acc tenv penv fnp_env wfp_env fenv dtenv es
  | Sexp.List (Sexp.Atom "set-info" :: Sexp.Atom ident :: t :: _) :: es -> begin
      let penv_all = Set.Poly.union_list [penv; fnp_env; wfp_env] in
      match Map.Poly.find fenv (Tvar ident) with
      | Some (params, ret_sort, body, is_rec, _) ->
        let property =
          Typeinf.typeinf_formula ~to_sus:true @@
          of_formula tenv penv_all fenv dtenv t
        in
        let fenv' = Map.Poly.set fenv ~key:(Tvar ident) ~data:(params, ret_sort, body, is_rec, property) in
        toplevel acc tenv penv fnp_env wfp_env fenv' dtenv es
      | None -> toplevel acc tenv penv fnp_env wfp_env fenv dtenv es
    end
  | Sexp.List (Sexp.Atom "set-info" :: _) :: es
  | Sexp.List (Sexp.Atom "set-option" :: _) :: es
  | Sexp.List [Sexp.Atom "get-model"] :: es
  | Sexp.List [Sexp.Atom "check-sat"] :: es
  | Sexp.List [Sexp.Atom "exit"] :: es ->
    toplevel acc tenv penv fnp_env wfp_env fenv dtenv es
  | Sexp.List [Sexp.Atom "declare-sort"; Sexp.Atom ident; Sexp.Atom numeral] :: es ->
    let datatype = Datatype.mk_uninterpreted_datatype ~numeral:(Int.of_string numeral) ident in
    let dtenv' = DTEnv.update_dt dtenv datatype in
    toplevel acc tenv penv fnp_env wfp_env fenv dtenv' es
  | Sexp.List [Sexp.Atom "declare-codatatypes"; Sexp.List args; Sexp.List dts] :: es
    when List.for_all args ~f:(function Sexp.Atom _ -> true | _ -> false) ->
    let datatypes = mk_old_datatypes dtenv dts Datatype.FCodt args in
    let dtenv' = List.fold_left datatypes ~init:dtenv ~f:DTEnv.update_dt in
    Debug.print @@ lazy (DTEnv.str_of dtenv');
    toplevel acc tenv penv fnp_env wfp_env fenv dtenv' es
  | Sexp.List [Sexp.Atom "declare-datatypes"; Sexp.List args; Sexp.List dts] :: es
    when List.for_all args ~f:(function Sexp.Atom _ -> true | _ -> false) ->
    let datatypes = mk_old_datatypes dtenv dts Datatype.FDt args in
    let dtenv' = List.fold_left datatypes ~init:dtenv ~f:DTEnv.update_dt in
    Debug.print @@ lazy (DTEnv.str_of dtenv');
    toplevel acc tenv penv fnp_env wfp_env fenv dtenv' es
  | Sexp.List [Sexp.Atom "declare-datatypes"; Sexp.List dts; Sexp.List funcs] :: es ->
    let datatypes = mk_new_datatypes dtenv dts funcs Datatype.FDt in
    let dtenv' = List.fold_left datatypes ~init:dtenv ~f:DTEnv.update_dt in
    Debug.print @@ lazy (DTEnv.str_of dtenv');
    toplevel acc tenv penv fnp_env wfp_env fenv dtenv' es
  | Sexp.List [Sexp.Atom "declare-codatatypes"; Sexp.List dts; Sexp.List funcs] :: es ->
    let datatypes = mk_new_datatypes dtenv dts funcs Datatype.FCodt in
    let dtenv' = List.fold_left datatypes ~init:dtenv ~f:DTEnv.update_dt in
    Debug.print @@ lazy (DTEnv.str_of dtenv');
    toplevel acc tenv penv fnp_env wfp_env fenv dtenv' es
  | Sexp.List [Sexp.Atom "declare-fun"; Sexp.Atom ident; Sexp.List param_tys; Sexp.Atom "Bool"] :: es ->
    (*Debug.print @@ lazy ("adding " ^ ident);*)
    let param_type = List.map param_tys ~f:(sort_of_sexp dtenv) in
    let penv' = Set.Poly.add penv (Ident.Pvar ident, param_type) in
    toplevel acc tenv penv' fnp_env wfp_env fenv dtenv es
  | Sexp.List [Sexp.Atom "declare-rel"; Sexp.Atom ident; Sexp.List param_tys] :: es ->
    (*Debug.print @@ lazy ("adding " ^ ident);*)
    let param_type = List.map param_tys ~f:(sort_of_sexp dtenv) in
    let penv' = Set.Poly.add penv (Ident.Pvar ident, param_type) in
    toplevel acc tenv penv' fnp_env wfp_env fenv dtenv es
  | Sexp.List [Sexp.Atom "declare-fnp"; Sexp.Atom ident; Sexp.List param_tys; Sexp.Atom "Bool"] :: es ->
    (*Debug.print @@ lazy ("adding " ^ ident);*)
    let param_type = List.map param_tys ~f:(sort_of_sexp dtenv) in
    let fnp_env' = Set.Poly.add fnp_env (Ident.Pvar ident, param_type) in
    toplevel acc tenv penv fnp_env' wfp_env fenv dtenv es
  | Sexp.List [Sexp.Atom "declare-wfp"; Sexp.Atom ident; Sexp.List param_tys; Sexp.Atom "Bool"] :: es ->
    (*Debug.print @@ lazy ("adding " ^ ident);*)
    let param_type = List.map param_tys ~f:(sort_of_sexp dtenv) in
    let wfp_env' = Set.Poly.add wfp_env (Ident.Pvar ident, param_type) in
    toplevel acc tenv penv fnp_env wfp_env' fenv dtenv es
  | Sexp.List [Sexp.Atom "declare-fun"; Sexp.Atom ident; Sexp.List param_tys; Sexp.Atom "Int"] :: es ->
    (*Debug.print @@ lazy ("adding " ^ ident);*)
    let param_type = List.map param_tys ~f:(sort_of_sexp dtenv) in
    let sort = Sort.mk_fun @@ param_type @ [T_int.SInt] in
    let tenv' = Set.Poly.add tenv (Ident.Tvar ident, sort) in
    toplevel acc tenv' penv fnp_env wfp_env fenv dtenv es
  | Sexp.List [Sexp.Atom "declare-fun"; Sexp.Atom ident; Sexp.List param_tys; Sexp.Atom "Real"] :: es ->
    (*Debug.print @@ lazy ("adding " ^ ident);*)
    let param_type = List.map param_tys ~f:(sort_of_sexp dtenv)in
    let sort = Sort.mk_fun @@ param_type @ [T_real_int.SReal] in
    let tenv' = Set.Poly.add tenv (Ident.Tvar ident, sort) in
    toplevel acc tenv' penv fnp_env wfp_env fenv dtenv es
  | Sexp.List [(Sexp.Atom "declare-fun"); (Sexp.Atom ident); (Sexp.List param_tys); ty] :: es ->
    Debug.print @@ lazy ("adding " ^ ident);
    let param_type = List.map param_tys ~f:(sort_of_sexp dtenv)in
    let ret_ty = sort_of_sexp dtenv ty in
    let sort = Sort.mk_fun @@ param_type @ [ret_ty] in
    let tenv' = Set.Poly.add tenv (Ident.Tvar ident, sort) in
    toplevel acc tenv' penv fnp_env wfp_env fenv dtenv es
  | Sexp.List [Sexp.Atom "declare-const"; Sexp.Atom ident; Sexp.Atom "Int"] :: es ->
    let tenv' = Set.Poly.add tenv (Ident.Tvar ident, T_int.SInt) in
    toplevel acc tenv' penv fnp_env wfp_env fenv dtenv es
  | Sexp.List [Sexp.Atom "declare-const"; Sexp.Atom ident; Sexp.Atom "Real"] :: es ->
    let tenv' = Set.Poly.add tenv (Ident.Tvar ident, T_real.SReal) in
    toplevel acc tenv' penv fnp_env wfp_env fenv dtenv es
  | Sexp.List [Sexp.Atom "define-fun"; Sexp.Atom ident; Sexp.List env; Sexp.Atom "Bool"; phi] :: es ->
    let env' = List.map env ~f:(env_of_sexp dtenv)in
    let tenv' = Set.Poly.union tenv (Set.Poly.of_list env') in (*this scope is only phi*)
    let penv_all = Set.Poly.union_list [penv; fnp_env; wfp_env] in
    let fenv' =
      Map.Poly.add_exn fenv
        ~key:(Tvar ident)
        ~data:(env', T_bool.SBool,
               (T_bool.of_formula @@ of_formula tenv' penv_all fenv dtenv phi),
               false, Formula.mk_true ())
    in
    toplevel acc tenv penv fnp_env wfp_env fenv' dtenv es
  | Sexp.List [Sexp.Atom "define-fun"; Sexp.Atom ident; Sexp.List env; (Sexp.Atom "Int" as sort); t] :: es
  | Sexp.List [Sexp.Atom "define-fun"; Sexp.Atom ident; Sexp.List env; (Sexp.Atom "Real" as sort); t] :: es ->
    let sort = sort_of_sexp dtenv sort in
    let env' = List.map env ~f:(env_of_sexp dtenv) in
    let tenv' = Set.Poly.union tenv (Set.Poly.of_list env') in (*this scope is only phi*)
    let fenv' =
      Map.Poly.add_exn
        fenv
        ~key:(Tvar ident)
        ~data:(env', sort, (of_term t tenv' penv fenv dtenv ), false, Formula.mk_true ())
    in
    toplevel acc tenv penv fnp_env wfp_env fenv' dtenv es
  | Sexp.List [Sexp.Atom "define-fun-rec"; Sexp.Atom ident; Sexp.List env; sort; t] :: es ->
    let env' = List.map env ~f:(env_of_sexp dtenv) in
    let tenv' = Set.Poly.union tenv (Set.Poly.of_list env') in (*this scope is only phi*)
    let sort = sort_of_sexp dtenv sort in
    let fenv' =
      Map.Poly.add_exn
        fenv
        ~key:(Tvar ident)
        ~data:(env', sort, (Term.mk_var (Ident.Tvar ident) sort), true, Formula.mk_true ())
    in
    let fenv'' =
      Map.Poly.add_exn fenv
        ~key:(Tvar ident)
        ~data:(env', sort, (Typeinf.typeinf_term ~to_sus:true @@ of_term t tenv' penv fenv' dtenv), true, Formula.mk_true ())
    in
    toplevel acc tenv penv fnp_env wfp_env fenv'' dtenv es
  | Sexp.List [Sexp.Atom "assert"; phi] :: es ->
    let penv_all = Set.Poly.union_list [penv; fnp_env; wfp_env] in
    let phi = of_formula tenv penv_all fenv dtenv phi in
    toplevel (phi :: acc) tenv penv fnp_env wfp_env fenv dtenv es
  | Sexp.List [Sexp.Atom "query"; phi] :: es ->
    let penv_all = Set.Poly.union_list [penv; fnp_env; wfp_env] in
    let phi = of_formula tenv penv_all fenv dtenv phi in
    let phi' = Formula.mk_neg phi in
    toplevel (phi' :: acc) tenv penv fnp_env wfp_env fenv dtenv es
  | Sexp.List [Sexp.Atom "rule"; phi] :: es ->
    let penv_all = Set.Poly.union_list [penv; fnp_env; wfp_env] in
    let phi = of_formula tenv penv_all fenv dtenv phi in
    let fvs = Formula.fvs_of phi |> Set.Poly.to_list in
    let bounds =
      List.filter_map fvs ~f:(fun v -> Set.Poly.find tenv ~f:(fun (v0, _) -> Stdlib.(v0 = v)))
    in
    let phi' = Formula.mk_forall bounds phi in
    toplevel (phi' :: acc) tenv penv fnp_env wfp_env fenv dtenv es
  | x -> failwith @@ "parse error : " ^ (Sexp.to_string_hum @@ Sexp.List x)

let toplevel ?(tenv=Set.Poly.empty) ?(penv=Set.Poly.empty) ?(fnp_env=Set.Poly.empty) ?(wfp_env=Set.Poly.empty) ?(fenv=Map.Poly.empty) ?(dtenv=Map.Poly.empty) =
  toplevel [] tenv penv fnp_env wfp_env fenv dtenv

let from_smt2_file filename =
  let open Result.Monad_infix in
  filename
  |> In_channel.create
  |> Lexing.from_channel
  |> Parser.program Lexer.token
  |> toplevel >>= (fun (acc, _tenv, _penv, _fnp_env, _wfp_env, _fenv, _) ->
      Debug.print @@ lazy (sprintf "before typeinf: %s" @@
                           Formula.str_of @@ Formula.and_of acc);
      let phi = Typeinf.typeinf_formula ~to_sus:true @@ Formula.and_of acc in
      Debug.print @@ lazy (sprintf "after typeinf: %s" @@ Formula.str_of phi);
      Result.return (phi))
  |> Result.map_error ~f:(fun err -> Error.of_string err)

let from_string ?(tenv=Set.Poly.empty) ?(penv=Set.Poly.empty) ?(fnp_env=Set.Poly.empty) ?(wfp_env=Set.Poly.empty) ?(fenv=Map.Poly.empty) ?(dtenv=Map.Poly.empty) str =
  Lexing.from_string str
  |> Parser.program Lexer.token
  |> toplevel ~tenv ~penv ~fnp_env ~wfp_env ~fenv ~dtenv
  |> ok_exn
