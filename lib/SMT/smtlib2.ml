(* Parser for SmtLib2 *)
open Core
open Common
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
  | Sexp.List ((Sexp.Atom "Array")::spars) ->
    begin match List.map spars ~f:(sort_of_sexp dtenv) with
      |[s1; s2] -> T_array.mk_array_sort s1 s2 
      | _ -> assert false
    end
  | Sexp.List ((Sexp.Atom name)::args) ->
    begin match DTEnv.look_up_dt dtenv name with
      | Some dt -> 
        let dt = Datatype.fresh_of dt in
        let args = List.map args ~f:(sort_of_sexp dtenv) in
        T_dt.SDT(Datatype.update_args dt args)
      | _ -> failwith ("unkonwn sort : " ^ name)
    end
  | Sexp.Atom name -> 
    Debug.print @@ lazy(sprintf "sort of sexp : %s" name);
    begin match DTEnv.look_up_dt dtenv name with
      | Some dt -> Datatype.sort_of @@ Datatype.fresh_of dt
      | _ -> Sort.SVar(Ident.Svar(name))
    end
  | sexp -> failwith @@ Printf.sprintf "unknown sort: %s" (Sexp.to_string sexp)

let env_of_sexp dtenv = function
  | Sexp.List [Sexp.Atom var; Sexp.Atom "Int"] -> (Ident.Tvar var, T_int.SInt)
  | Sexp.List [Sexp.Atom var; Sexp.Atom "Real"] -> (Ident.Tvar var, T_real.SReal)
  | Sexp.List [Sexp.Atom var; sort] -> (Ident.Tvar var, sort_of_sexp dtenv sort)
  | sexp -> failwith @@ Printf.sprintf "unknown sort: %s" (Sexp.to_string sexp)

let of_params acc sexp dtenv =
  List.rev sexp |>
  List.fold ~f:(fun (acc, acc') -> function
      | Sexp.List [Sexp.Atom ident; sort] -> 
        let e = (Ident.Tvar ident, sort_of_sexp dtenv sort) |> Set.Poly.singleton in 
        (Set.Poly.union e acc, Set.Poly.union e acc')
      | t -> failwith ("invalid param:" ^ (Sexp.to_string t))) ~init:(Set.Poly.empty, acc)

let of_pred_sym = function
  | Sexp.Atom "=" -> T_bool.mk_eq
  | Sexp.Atom "<" -> T_num.mk_nlt
  | Sexp.Atom ">" -> T_num.mk_ngt
  | Sexp.Atom "<=" -> T_num.mk_nleq
  | Sexp.Atom ">=" -> T_num.mk_ngeq
  | _ as op -> failwith @@ "parse error : unknown pred sym " ^ (Sexp.to_string_hum op)

let of_fun_sym = function
  | Sexp.Atom "+" -> T_num.mk_nadd
  | Sexp.Atom "-" -> T_num.mk_nsub
  | Sexp.Atom "*" -> T_num.mk_nmult
  | Sexp.Atom "/" -> T_real.mk_rdiv
  | Sexp.Atom "div" -> T_int.mk_div
  | Sexp.Atom "mod" -> T_int.mk_mod
  | Sexp.Atom "rem" -> T_int.mk_rem
  | Sexp.Atom "^" -> T_num.mk_npower
  | _ as op -> failwith @@ "parse error : unknown fun sym " ^ (Sexp.to_string_hum op)

let rec of_formula phi tenv penv fenv dtenv = let open Formula in
  Debug.print @@ lazy ("************ Debug:" ^ Sexp.to_string phi);
  match phi with
  (* constant *)
  | Sexp.Atom "true" -> mk_atom (Atom.mk_true ())
  | Sexp.Atom "false" -> mk_atom (Atom.mk_false ())
  | Sexp.Atom ident -> begin
      match Set.Poly.find_map tenv 
              ~f:(fun (key, sort) -> if Stdlib.(=) key (Ident.Tvar ident) then Some(sort) else None) with
      (* match Env.lookup (Ident.Tvar ident) tenv with *)
      | Some sort ->
        assert (Stdlib.(=) sort T_bool.SBool);
        let var = Term.mk_var (Ident.Tvar ident) sort in
        let atom = Atom.mk_app (Predicate.Psym T_bool.Eq) [var; T_bool.of_atom (Atom.mk_true ())] in
        mk_atom atom
      | None -> begin
          (* let sorts = Env.lookup_exn (Ident.Pvar ident) penv in *)
          (match Set.Poly.find penv
                   ~f:(fun (key, _sorts) -> Stdlib.(=) key (Ident.Pvar ident)) with
          | Some (_, sargs) ->
            assert (Stdlib.(=) sargs []);
            let pred = Predicate.mk_var (Ident.Pvar ident) sargs in
            mk_atom (Atom.mk_app pred [])
          | None ->
            match Set.Poly.find tenv
                    ~f:(fun (key, _sort) -> Stdlib.(=) key (Ident.Tvar ident)) with
            | Some (_, sort) ->
              let sargs, sret = Sort.args_ret_of sort in
              assert (Stdlib.(=) sret T_bool.SBool);
              assert (Stdlib.(=) sargs []);
              let pred = Predicate.mk_var (Ident.Pvar ident) sargs in
              mk_atom (Atom.mk_app pred [])
            | None ->
              (* no arguments function *)
              match Set.Poly.find fenv
                      ~f:(fun (key, env, _sort, _phi, _property, _is_rec) -> (Stdlib.(=) key ident) && Stdlib.(=) env []) with
              | Some (_, _, _, Term.FunApp(T_bool.Formula phi, _, _),_, _is_rec) -> phi
              | _ -> failwith (Printf.sprintf "%s is not bound" ident))
        end
    end

  (* logical operation *)
  | Sexp.List [Sexp.Atom "not"; phi] ->
    mk_neg (of_formula phi tenv penv fenv dtenv)
  | Sexp.List (Sexp.Atom "and" :: phis) ->
    let phis = List.rev_map phis ~f:(fun phi -> of_formula phi tenv penv fenv dtenv) in
    and_of phis
  | Sexp.List (Sexp.Atom "or" :: phis) ->
    let phis = List.rev_map phis ~f:(fun phi -> of_formula phi tenv penv fenv dtenv) in
    or_of phis
  | Sexp.List (Sexp.Atom "xor" :: phis) ->
    let phis = List.rev_map phis ~f:(fun phi -> of_formula phi tenv penv fenv dtenv) in
    xor_of phis
  | Sexp.List [Sexp.Atom "=>"; phi1; phi2] ->
    let phi1 = of_formula phi1 tenv penv fenv dtenv in
    let phi2 = of_formula phi2 tenv penv fenv dtenv in
    mk_imply phi1 phi2

  (* binder *)
  | Sexp.List [Sexp.Atom "forall"; Sexp.List params; phi] ->
    let params, tenv = of_params tenv params dtenv in
    let phi = of_formula phi tenv penv fenv dtenv in
    mk_forall (SortEnv.of_set params) phi
  | Sexp.List [Sexp.Atom "exists"; Sexp.List params; phi] ->
    let params, tenv = of_params tenv params dtenv in
    let phi = of_formula phi tenv penv fenv dtenv in
    mk_exists (SortEnv.of_set params) phi
  | Sexp.List [Sexp.Atom "random"; Sexp.List params; phi] ->
    let tenv, params = of_random_params tenv params penv fenv dtenv in
    let phi = of_formula phi tenv penv fenv dtenv in
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
    Util.Set.fold_distinct_pairs
      ~f:(fun t1 t2 -> mk_atom @@ T_bool.mk_neq t1 t2)
      (Set.Poly.of_list @@ List.map ~f:(fun t -> of_term t tenv penv fenv dtenv ) ts)

  (* let *)
  | Sexp.List [Sexp.Atom "let"; Sexp.List bounds; phi] ->
    (*    print_endline "entry @ let"; *)
    let pbounds, tbounds =
      List.fold bounds ~init:(Map.Poly.empty, Map.Poly.empty)
        ~f:(fun (pbounds, tbounds) ->
            function
            | Sexp.List [Sexp.Atom ident; p_or_t] ->
              begin
                try
                  let phi = of_formula p_or_t tenv penv fenv dtenv in
                  if (LogicOld.Formula.number_of_pvar_apps true phi) + (LogicOld.Formula.number_of_pvar_apps false phi) > 0 then 
                    (Map.Poly.add_exn pbounds ~key:(Ident.Pvar ident) ~data:(SortEnv.empty, phi)), tbounds
                  else failwith "this case is only for adr_39_.smt2 which is ill-formed to chc-comp18 format."
                with _ ->
                  let term = of_term p_or_t tenv penv fenv dtenv in
                  pbounds, Map.Poly.add_exn tbounds ~key:(Ident.Tvar ident) ~data:term
              end
            | x -> failwith @@ "Invalid param: " ^ (Sexp.to_string_hum x)) in
    let penv = Map.Poly.fold ~init:penv ~f:(fun ~key:var ~data:_ acc -> Set.Poly.add acc (var, [])) pbounds in
    let tenv = Map.Poly.fold ~init:tenv ~f:(fun ~key:var ~data:_ acc -> Set.Poly.add acc (var, T_bool.SBool(*ToDo: check if this is OK*))) tbounds in
    let phi = of_formula phi tenv penv fenv dtenv in
    phi |> Formula.subst_preds pbounds |> Formula.subst tbounds (*TODO: out of memory*)
  | Sexp.List [Sexp.Atom "ite"; cond; then_; else_] ->
    let cond = of_term cond tenv penv fenv dtenv in
    let then_ = of_term then_ tenv penv fenv dtenv in
    let else_ = of_term else_ tenv penv fenv dtenv in
    let t = T_bool.mk_if_then_else cond then_ else_ in
    Formula.mk_atom
      (Atom.mk_app (Predicate.Psym T_bool.Eq) [t; T_bool.of_atom (Atom.mk_true ())])
  | Sexp.List [Sexp.Atom "is_int"; t] ->
    let t = of_term t tenv penv fenv dtenv in
    mk_atom (T_real_int.mk_is_int t)
  | Sexp.List [(Sexp.List [Sexp.Atom "_"; Sexp.Atom "is"; Sexp.Atom name]); t] ->
    let t = of_term t tenv penv fenv dtenv in
    (match DTEnv.look_up_func dtenv name with
     |Some (dt, (Datatype.FCons cons) )  -> T_dt.mk_is_cons dt cons t
     |_ -> assert false
    )|> mk_atom
  (*TODO: support ':named' well*)
  | Sexp.List [Sexp.Atom "!"; t; Sexp.Atom ":named"; Sexp.Atom _] -> 
    Debug.print @@ lazy ("! :named");
    let term = of_term t tenv penv fenv dtenv in
    if Stdlib.(=) (Term.sort_of term) (T_bool.SBool) then
      of_formula t tenv penv fenv dtenv
    else
      failwith "must be bool fun"
  | Sexp.List ((Sexp.Atom "!")::t::Sexp.Atom ":pattern"::_) ->
    of_formula t tenv penv fenv dtenv
  (* predicate variable application *)
  | Sexp.List (Sexp.Atom ident :: args) ->
    Debug.print @@ lazy (sprintf "[formula]precicate %s" ident);
    let args = List.map args ~f:(fun t -> of_term t tenv penv fenv dtenv ) in
    (match Set.Poly.find penv
             ~f:(fun (key, _) -> Stdlib.(=) key (Ident.Pvar ident)) with
    | Some (_, sargs) ->
      let pred = Predicate.mk_var (Ident.Pvar ident) sargs in
      mk_atom (Atom.mk_app pred args)
    | None ->
      match Set.Poly.find tenv
              ~f:(fun (key, _sort) -> Stdlib.(=) key (Ident.Tvar ident)) with
      | Some (_, sort) ->
        let sargs, sret = Sort.args_ret_of sort in
        assert (Stdlib.(=) sret T_bool.SBool);
        let pred = Predicate.mk_var (Ident.Pvar ident) sargs in
        mk_atom (Atom.mk_app pred args)
      | None ->
        match Set.Poly.find fenv
                ~f:(fun (key, env, _ret_sort, _phi, _property, _is_rec) -> Stdlib.(=) key ident && (List.length args) = (List.length env)) with
        | Some (_, env, _, Term.FunApp(T_bool.Formula phi, _, _), _, _) ->
          let var, _ = List.unzip env in
          let map = Map.Poly.of_alist_exn @@List.zip_exn var args in
          Formula.subst map phi
        | _ -> failwith (Printf.sprintf "%s is not bound" ident))
  | _ as phi ->
    failwith @@ "parse error : " ^ (Sexp.to_string_hum phi)

and is_included_pvars tenv penv fenv dtenv= function
  | [] -> false
  | (Sexp.List [Sexp.Atom _; t])::sexps ->
    let phi = of_formula t tenv penv fenv dtenv in
    if (LogicOld.Formula.number_of_pvar_apps true phi) + (LogicOld.Formula.number_of_pvar_apps false phi) > 0 then true
    else is_included_pvars tenv penv fenv dtenv sexps  
  | x::_ -> failwith @@ "invalid bounds: " ^ (Sexp.to_string_hum x)

and of_term t tenv penv fenv dtenv = let open Term in
  let mk_formula_term () =
    let phi = of_formula t tenv penv fenv dtenv  in
    T_bool.of_formula phi
  in
  match t with
  | Sexp.Atom "true" -> T_bool.of_atom (Atom.mk_true ())
  | Sexp.Atom "false" -> T_bool.of_atom (Atom.mk_false ())
  | Sexp.Atom ident -> begin
      try
        (* case on integer/decimal constants *)
        T_num.mk_value ident
      with _ -> begin
          (* case on others *)
          match Set.Poly.find tenv
                  ~f:(fun (key, _sort) -> Stdlib.(=) key (Ident.Tvar ident)) with
          | Some (_, sort) -> mk_var (Ident.Tvar ident) sort
          | None ->
            match Set.Poly.find penv
                    ~f:(fun (key, _sorts) -> Stdlib.(=) key (Ident.Pvar ident)) with
            | Some (_, sorts) -> mk_var (Ident.Tvar ident) (Sort.mk_fun (sorts @ [T_bool.SBool]))
            | None -> 
              match Set.Poly.find fenv
                      ~f:(fun (key, env, _ret_sort, _t, _property, _is_rec) -> Stdlib.(=) key ident && Stdlib.(=) env []) with
              | Some (_, _, _, t, _, _) -> t
              | None -> 
                match DTEnv.look_up_func dtenv ident with
                |Some (dt, Datatype.FCons (cons)) when List.length @@ Datatype.sels_of_cons cons = 0->
                  T_dt.mk_cons dt ident []
                |_ -> failwith (Printf.sprintf "%s is not bound" ident)
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
          | Sexp.List [Sexp.Atom ident; t] -> Ident.Tvar ident, of_term t tenv penv fenv dtenv
          | x -> failwith @@ "invalid param : " ^ (Sexp.to_string_hum x)) in
      let tenv = List.fold bounds ~init:tenv
          ~f:(fun tenv (var, t) ->
              let m = (Set.Poly.singleton (var, Term.sort_of t)) in
              Set.Poly.union m tenv) in
      let body = of_term body tenv penv fenv dtenv in
      Term.subst (bounds |> Map.Poly.of_alist_exn) body
    in
    begin
      try if is_included_pvars tenv penv fenv dtenv bounds then
          failwith "Invalid let-expressions (It is not allowed to use let-term binding predicate applications into some name.)"
        else aux bounds body
      with _ -> aux bounds body
    end
  (* ToDo: support function applications *)
  | Sexp.List [(Sexp.List [Sexp.Atom "_"; Sexp.Atom "is"; Sexp.Atom name]); t] ->
    let t = of_term t tenv penv fenv dtenv in
    let formula = (match DTEnv.look_up_func dtenv name with
        |Some (dt, (Datatype.FCons cons ))  -> T_dt.mk_is_cons dt cons t
        |_ -> assert false
      )|> Formula.mk_atom in
    Term.mk_fsym_app (T_bool.Formula formula) []
  | Sexp.List (Sexp.Atom ident :: args) when DTEnv.name_is_func dtenv ident ->
    Debug.print @@ lazy (sprintf "[term]datatype func %s" ident);
    let args = List.map args ~f:(fun t -> of_term t tenv penv fenv dtenv ) in
    (match DTEnv.look_up_func dtenv ident with
     |Some (dt, Datatype.FCons (_)) -> T_dt.mk_cons dt ident args
     |Some (dt, Datatype.FSel (_)) ->
       begin match args with 
         |[arg] -> T_dt.mk_sel dt ident arg
         |_ -> assert false
       end
     |_ -> mk_formula_term ()
    )
  | Sexp.List [Sexp.Atom "to_real"; t] ->
    let t = of_term t tenv penv fenv dtenv  in
    T_real_int.mk_to_real t
  | Sexp.List [Sexp.Atom "to_int"; t] ->
    let t = of_term t tenv penv fenv dtenv  in
    T_real_int.mk_to_int t
  | Sexp.List [Sexp.Atom "select"; t1; t2] ->
    let arr = of_term t1 tenv penv fenv dtenv in
    let i = of_term t2 tenv penv fenv dtenv in
    T_array.mk_select arr i
  | Sexp.List [Sexp.Atom "store"; t1; t2; t3] ->
    let arr = of_term t1 tenv penv fenv dtenv in
    let i = of_term t2 tenv penv fenv dtenv in
    let e = of_term t3 tenv penv fenv dtenv in
    T_array.mk_store arr i e
  | Sexp.List [Sexp.List [Sexp.Atom "as"; Sexp.Atom "const"; sort]; value] ->
    let arr_sort = sort_of_sexp dtenv sort in
    let arr_value = of_term value tenv penv fenv dtenv in
    T_array.mk_const_array arr_sort arr_value
  | Sexp.List (Sexp.Atom ident :: args) ->
    begin
      match Set.Poly.find fenv ~f:(fun (key, _env, _ret_sort, _body, _property, _is_rec) -> Stdlib.(=) key ident) with
      | Some (_, env, _, term, _, false) -> 
        let args = List.map args ~f:(fun t -> of_term t tenv penv fenv dtenv ) in
        let var, _ = List.unzip env in
        let map = Map.Poly.of_alist_exn @@List.zip_exn var args in
        Term.subst map term
      | Some (name, env, ret_sort, body, _, true) ->
        let args = List.map args ~f:(fun t -> of_term t tenv penv fenv dtenv ) in
        T_recfvar.mk_recfvar_app (Ident.Tvar name) env (ret_sort) body args
      | _ ->
        begin 
          match Set.Poly.find tenv
                  ~f:(fun (key, _sort) -> Stdlib.(=) key (Ident.Tvar ident)) with
          | Some (_, sort) ->
            let atrms = List.map args ~f:(
                fun t -> of_term t tenv penv fenv dtenv
              ) in
            let sargs, sret = Sort.args_ret_of sort in
            if Stdlib.(=) sret T_bool.SBool then 
              mk_formula_term ()
            else begin
              assert (List.length atrms = List.length sargs);
              Term.mk_fvar_app (Ident.Tvar ident) (sargs @ [sret]) (atrms)
            end
          | None ->
            let phi = of_formula t tenv penv fenv dtenv  in
            T_bool.of_formula phi
        end end
  | _ -> mk_formula_term ()
and dist_of_sexp tenv penv fenv dtenv = function
  | Sexp.List [Sexp.Atom "Uniform"; t1; t2] ->
    let t1 = of_term t1 tenv penv fenv dtenv in
    let t2 = of_term t2 tenv penv fenv dtenv in
    Rand.mk_uniform t1 t2
  | Sexp.List [Sexp.Atom "Gauss"; t1; t2] ->
    let t1 = of_term t1 tenv penv fenv dtenv in
    let t2 = of_term t2 tenv penv fenv dtenv in
    Rand.mk_gauss t1 t2
  | _ -> assert false
and of_random_params acc sexp penv fenv dtenv =
  List.rev sexp |>
  List.fold ~f:(fun (acc, params) -> function
      | Sexp.List [Sexp.Atom ident; dist] ->
        let rand = dist_of_sexp acc penv fenv dtenv dist in
        let e = (Ident.Tvar ident, Rand.sort_of rand) |> Set.Poly.singleton in
        let p = (Ident.Tvar ident, rand) in
        (Set.Poly.union e acc, p::params)
      | t -> failwith ("error of " ^ (Sexp.to_string t))) ~init:(acc, [])

let str_of_tenv tenv =
  String.concat ~sep:", "
  @@ List.map
    ~f:(fun (tvar, sort) ->
        Printf.sprintf "(%s: %s)"(Ident.name_of_tvar tvar) (Printer.str_of_sort sort)
      )
  @@ Env.entries tenv

let str_of_penv penv =
  String.concat ~sep:", "
  @@ List.map ~f:(fun (ident, sorts) -> 
      Printf.sprintf "(%s: %s)" (Ident.name_of_pvar ident) 
      @@ String.concat ~sep:" -> " (List.map ~f:(fun sort -> Printer.str_of_sort sort) sorts)
    ) (Set.Poly.to_list penv)

let restrict_head bounds args fml =
  List.fold args
    ~init:(bounds, [], fml)
    ~f:(fun (bounds, args, fml) arg ->
        let arg_sort: Sort.t = Term.sort_of arg in
        let new_ident: Ident.tvar = Ident.mk_fresh_head_arg () in
        let new_arg: Term.t = Term.mk_var new_ident arg_sort in
        let bounds = (new_ident, arg_sort) :: bounds in
        let args = new_arg :: args in
        let fml = Formula.mk_and
            fml
            (Formula.mk_atom
               (Atom.mk_app
                  (Predicate.Psym T_bool.Eq)
                  [
                    new_arg;
                    arg;
                  ]
               )
            )
        in
        bounds, args, fml)

let is_available str =
  let logiclist = ["HORN";"QF_LIA";"QF_NRA";"QF_LIA";"QF_LRA";"QF_LIRA";"QF_NIA";"QF_NRA";"QF_NIRA";"LIA";"LRA";"NIA";"NRA";"SAT";"QF_DT";"QF_UF";"QF_ALIA";"ALL_SUPPORTED";"AUFLIA"] in
  List.exists logiclist ~f:(fun x -> String.(str = x))

let mk_dt_sel dtenv dt dts sel =
  match sel with
  | Sexp.List [Sexp.Atom name; ret] ->
    begin match ret with
      | Sexp.Atom ret_name ->
        begin match List.find dts ~f:(
            fun dt -> Stdlib.(=) ret_name @@ Datatype.name_of_dt dt 
          ) with
        | Some _ ->  Datatype.mk_insel name ret_name (Datatype.args_of_dt dt)
        | None -> Datatype.mk_sel name @@ sort_of_sexp dtenv ret
        end
      | Sexp.List ((Sexp.Atom ret_name)::args) ->
        begin match List.find dts ~f:(
            fun dt -> Stdlib.(=) ret_name @@ Datatype.name_of_dt dt 
          ) with
        | Some _ -> 
          if Stdlib.(=) (Datatype.name_of_dt dt) (ret_name) then 
            Datatype.mk_insel name ret_name (Datatype.args_of_dt dt)
          else                      
            Datatype.mk_insel name ret_name (List.map args ~f:(sort_of_sexp dtenv))
        | None -> Datatype.mk_sel name @@ sort_of_sexp dtenv ret
        end
      | _ -> assert false
    end
  |_ -> assert false
let mk_dt_cons dtenv dt dts cons =
  match cons with
  | Sexp.Atom name 
  | Sexp.List [Sexp.Atom name] -> Datatype.mk_cons name 
  | Sexp.List ((Sexp.Atom name)::sels) ->
    let sels = List.map sels ~f:(fun sel -> mk_dt_sel dtenv dt dts sel) in
    Datatype.mk_cons name ~sels:sels
  | _ -> failwith @@ Sexp.to_string cons
let mk_new_datatypes dtenv dts funcs flag =
  let datatypes = List.map2_exn dts funcs ~f:(
      fun dt func -> match dt with
        | Sexp.List [Sexp.Atom name; Sexp.Atom "0"] -> Datatype.mk_dt name []  
        | Sexp.List [Sexp.Atom name; Sexp.Atom _] ->
          begin match func with
            | Sexp.List ((Sexp.List [Sexp.Atom "par"; Sexp.List args])::_) ->
              let args = List.map args ~f:(function |Sexp.Atom ident ->  Sort.SVar(Ident.Svar(ident)) | _ -> assert false) in
              Datatype.mk_dt name args  
            | _ -> assert false
          end
        | _ -> assert false
    ) in
  let datatypes = List.map2_exn datatypes funcs ~f:(
      fun dt func ->
        match func with
        | Sexp.List ((Sexp.List [Sexp.Atom "par"; Sexp.List _])::conses)
        | Sexp.List conses ->
          let conses = List.fold_left conses ~init:[] ~f:(
              fun conses cons -> 
                mk_dt_cons dtenv dt datatypes cons::conses
            ) in
          {dt with conses = conses}
        | _ -> assert false
    ) in List.map datatypes ~f:(fun dt -> Datatype.create (Datatype.name_of_dt dt) datatypes flag) 
let mk_old_datatypes dtenv dts flag args=
  let args = List.map args ~f:(function |Sexp.Atom ident ->  Sort.SVar(Ident.Svar(ident)) | _ -> assert false) in
  let datatypes = List.map dts ~f:(
      fun dt -> match dt with
        | Sexp.List (Sexp.Atom name::_) -> Datatype.mk_dt name args
        | _ -> assert false
    ) in
  let datatypes = List.map2_exn datatypes dts ~f:(
      fun dt func ->
        match func with
        | Sexp.List (_::conses) ->  
          let conses = List.fold_left conses ~init:[] ~f:(
              fun conses cons -> 
                mk_dt_cons dtenv dt datatypes cons::conses
            ) in
          {dt with conses = conses}
        | _ -> assert false
    ) in List.map datatypes ~f:(fun dt -> Datatype.create (Datatype.name_of_dt dt) datatypes flag) 

let rec toplevel acc tenv penv fenv dtenv= function
  | [] -> 
    let fenv' = Set.Poly.filter_map fenv ~f:(fun (name, env, ret_sort, body, property, is_rec) -> if is_rec then Some (Ident.Tvar(name), env, ret_sort, body, property) else None) in
    Ok (acc, tenv, penv, fenv', dtenv) (*(smt_of_formula acc tenv penv)*)
  | (Sexp.List [Sexp.Atom "set-logic"; Sexp.Atom logic]) :: es when is_available logic
    -> toplevel acc tenv penv fenv dtenv es
  | (Sexp.List (Sexp.Atom "set-info" :: Sexp.Atom ident :: t :: _)) :: es ->
    begin match Set.Poly.find fenv ~f:(fun (name, _, _, _, _, is_rec) -> Stdlib.(=) name ident && is_rec) with
      | Some ((name, env, ret_sort, body, property, is_rec) as func)-> 
        let property' = Set.Poly.add property (Typeinf.typeinf @@ of_formula t tenv penv fenv dtenv) in
        let fenv' = Set.Poly.add (Set.Poly.remove fenv func) (name, env, ret_sort, body, property', is_rec) in
        toplevel acc tenv penv fenv' dtenv es
      | _ -> toplevel acc tenv penv fenv dtenv es
    end
  | (Sexp.List (Sexp.Atom "set-info" :: _) :: es)
  | (Sexp.List (Sexp.Atom "set-option" :: _)) :: es
  | (Sexp.List [Sexp.Atom "get-model"]) :: es
  | (Sexp.List [Sexp.Atom "check-sat"]) :: es
  | (Sexp.List [Sexp.Atom "exit"]) :: es
    -> toplevel acc tenv penv fenv dtenv es
  | (Sexp.List [Sexp.Atom "declare-sort"; Sexp.Atom ident; Sexp.Atom numeral])::ec -> 
    let datatype = Datatype.mk_uninterpreted_datatype ~numeral:(Int.of_string numeral) ident in
    let dtenv' = DTEnv.update_dt dtenv datatype in
    toplevel acc tenv penv fenv dtenv' ec
  | (Sexp.List [Sexp.Atom "declare-codatatypes"; Sexp.List args; Sexp.List dts]) :: es 
    when List.for_all args ~f:(function |Sexp.Atom _ -> true | _ -> false) ->
    let datatypes = mk_old_datatypes dtenv dts Datatype.FCodt args in
    let dtenv' = List.fold_left datatypes ~init:dtenv ~f:(
        fun dtenv dt -> DTEnv.update_dt dtenv dt
      ) in
    Debug.print @@ lazy (DTEnv.str_of dtenv');
    toplevel acc tenv penv fenv dtenv' es
  | (Sexp.List [Sexp.Atom "declare-datatypes"; Sexp.List args; Sexp.List dts]) :: es 
    when List.for_all args ~f:(function |Sexp.Atom _ -> true | _ -> false)->
    let datatypes = mk_old_datatypes dtenv dts Datatype.FDt args in
    let dtenv' = List.fold_left datatypes ~init:dtenv ~f:(
        fun dtenv dt -> DTEnv.update_dt dtenv dt
      ) in
    Debug.print @@ lazy (DTEnv.str_of dtenv');
    toplevel acc tenv penv fenv dtenv' es
  | (Sexp.List [Sexp.Atom "declare-datatypes";Sexp.List dts ;Sexp.List funcs]) :: es -> 
    let datatypes = mk_new_datatypes dtenv dts funcs Datatype.FDt in
    let dtenv' = List.fold_left datatypes ~init:dtenv ~f:(
        fun dtenv dt -> DTEnv.update_dt dtenv dt
      ) in
    Debug.print @@ lazy (DTEnv.str_of dtenv');
    toplevel acc tenv penv fenv dtenv' es
  | (Sexp.List [Sexp.Atom "declare-codatatypes";Sexp.List dts ;Sexp.List funcs]) :: es -> 
    let datatypes = mk_new_datatypes dtenv dts funcs Datatype.FCodt in
    let dtenv' = List.fold_left datatypes ~init:dtenv ~f:(
        fun dtenv dt -> DTEnv.update_dt dtenv dt
      ) in
    Debug.print @@ lazy (DTEnv.str_of dtenv');
    toplevel acc tenv penv fenv dtenv' es
  | (Sexp.List [Sexp.Atom "declare-fun"; Sexp.Atom ident; Sexp.List param_tys; Sexp.Atom "Bool"]) :: es ->
    (*Debug.print @@ lazy ("adding " ^ ident);*)
    let param_type = List.map param_tys ~f:(sort_of_sexp dtenv) in
    let penv' = Set.Poly.union penv (Set.Poly.singleton (Ident.Pvar ident, param_type)) in
    toplevel acc tenv penv' fenv dtenv es
  | (Sexp.List [Sexp.Atom "declare-fun"; Sexp.Atom ident; Sexp.List param_tys; Sexp.Atom "Int"]) :: es ->
    (*Debug.print @@ lazy ("adding " ^ ident);*)
    let param_type = List.map param_tys ~f:(sort_of_sexp dtenv) in
    let sort = Sort.mk_fun @@ param_type @ [T_int.SInt] in
    let tenv' = Set.Poly.union tenv (Set.Poly.singleton (Ident.Tvar ident, sort)) in
    toplevel acc tenv' penv fenv dtenv es
  | (Sexp.List [Sexp.Atom "declare-fun"; Sexp.Atom ident; Sexp.List param_tys; Sexp.Atom "Real"]) :: es ->
    (*Debug.print @@ lazy ("adding " ^ ident);*)
    let param_type = List.map param_tys ~f:(sort_of_sexp dtenv)in
    let sort = Sort.mk_fun @@ param_type @ [T_real_int.SReal] in
    let tenv' = Set.Poly.union tenv (Set.Poly.singleton (Ident.Tvar ident, sort)) in
    toplevel acc tenv' penv fenv dtenv es
  | (Sexp.List [(Sexp.Atom "declare-fun"); (Sexp.Atom ident); (Sexp.List param_tys); ty]) :: es ->
    Debug.print @@ lazy ("adding " ^ ident);
    let param_type = List.map param_tys ~f:(sort_of_sexp dtenv)in
    let ret_ty = sort_of_sexp dtenv ty in 
    let sort = Sort.mk_fun @@ param_type @ [ret_ty] in
    let tenv' = Set.Poly.union tenv (Set.Poly.singleton (Ident.Tvar ident, sort)) in
    toplevel acc tenv' penv fenv dtenv es
  | (Sexp.List [Sexp.Atom "declare-const"; Sexp.Atom ident; Sexp.Atom "Int"]) :: es ->
    let tenv' = Set.Poly.union tenv (Set.Poly.singleton (Ident.Tvar ident, T_int.SInt)) in
    toplevel acc tenv' penv fenv dtenv es
  | (Sexp.List [Sexp.Atom "declare-const"; Sexp.Atom ident; Sexp.Atom "Real"]) :: es ->
    let tenv' = Set.Poly.union tenv (Set.Poly.singleton (Ident.Tvar ident, T_real.SReal)) in
    toplevel acc tenv' penv fenv dtenv es
  | (Sexp.List [Sexp.Atom "define-fun"; Sexp.Atom ident; Sexp.List env; Sexp.Atom "Bool"; phi]) :: es ->
    let env' = List.map env ~f:(env_of_sexp dtenv)in
    let tenv' = Set.Poly.union tenv (Set.Poly.of_list env') in (*this scope is only phi*)
    let fenv' = Set.Poly.union fenv (Set.Poly.singleton (ident, env', T_bool.SBool, (T_bool.of_formula @@ of_formula phi tenv' penv fenv dtenv), Set.Poly.empty, false)) in
    toplevel acc tenv penv fenv' dtenv es
  | (Sexp.List [Sexp.Atom "define-fun"; Sexp.Atom ident; Sexp.List env; (Sexp.Atom "Int" as sort); t]) :: es
  | (Sexp.List [Sexp.Atom "define-fun"; Sexp.Atom ident; Sexp.List env; (Sexp.Atom "Real" as sort); t]) :: es ->
    let sort = sort_of_sexp dtenv sort in
    let env' = List.map env ~f:(env_of_sexp dtenv) in
    let tenv' = Set.Poly.union tenv (Set.Poly.of_list env') in (*this scope is only phi*)
    let fenv' = Set.Poly.union fenv (Set.Poly.singleton (ident, env', sort, (of_term t tenv' penv fenv dtenv ), Set.Poly.empty, false)) in
    toplevel acc tenv penv fenv' dtenv es
  | (Sexp.List [Sexp.Atom "define-fun-rec"; Sexp.Atom ident; Sexp.List env; sort; t]):: es ->
    let env' = List.map env ~f:(env_of_sexp dtenv) in
    let tenv' = Set.Poly.union tenv (Set.Poly.of_list env') in (*this scope is only phi*)
    let sort = sort_of_sexp dtenv sort in
    let fenv' = Set.Poly.union fenv (Set.Poly.singleton (ident, env', sort,(Term.mk_var (Ident.Tvar(ident))sort), Set.Poly.empty, true)) in
    let fenv'' = Set.Poly.union fenv (Set.Poly.singleton (ident, env', sort, (Typeinf.typeinf_term @@ of_term t tenv' penv fenv' dtenv), Set.Poly.empty, true)) in
    toplevel acc tenv penv fenv'' dtenv es
  | (Sexp.List [Sexp.Atom "assert"; phi]) :: es ->
    let phi = of_formula phi tenv penv fenv dtenv in
    toplevel (phi :: acc) tenv penv fenv dtenv es
  | _ as x -> failwith @@ "parse error : " ^ (Sexp.to_string_hum @@ Sexp.List x)

let toplevel = toplevel [] (Set.Poly.empty) (Set.Poly.empty) (Set.Poly.empty) (Map.Poly.empty)

let from_smt2_file filename =
  let open Result.Monad_infix in
  filename
  |> In_channel.create
  |> Lexing.from_channel
  |> Parser.program Lexer.token
  |> toplevel >>= (fun (acc, _tenv, _penv, _fenv,  _) -> 
      Debug.print @@ lazy (sprintf "before typeinf:%s" @@ Formula.str_of @@ Formula.and_of acc);
      let phi = Typeinf.typeinf @@ Formula.and_of acc in
      Debug.print @@ lazy (sprintf "after typeinf:%s" @@ Formula.str_of phi);
      Result.return (phi))
  |> Result.map_error ~f:(fun err -> Error.of_string err)
