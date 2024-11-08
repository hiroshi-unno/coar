(* Parser for SmtLib2 *)

open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* open Parsexp *)
module Sexp = Ppx_sexp_conv_lib.Sexp

let rec sort_of_sexp ~print dtenv = function
  | Sexp.Atom "Int" -> T_int.SInt
  | Sexp.Atom "Real" -> T_real.SReal
  | Sexp.Atom "Bool" -> T_bool.SBool
  | Sexp.Atom "String" -> T_string.SString
  | Sexp.List [ Sexp.Atom "Array"; s1; s2 ] ->
      T_array.mk_array_sort
        (sort_of_sexp ~print dtenv s1)
        (sort_of_sexp ~print dtenv s2)
  | Sexp.List [ Sexp.Atom "RegEx"; Sexp.Atom "String" ] -> T_regex.SRegEx
  | Sexp.List (Sexp.Atom name :: args) as sexp -> (
      match DTEnv.look_up_dt dtenv name with
      | Some dt ->
          T_dt.SDT
            (Datatype.update_params (Datatype.fresh_of dt)
            @@ List.map args ~f:(sort_of_sexp ~print dtenv))
      | _ ->
          failwith
          @@ sprintf "[sort_of_sexp] unknown sort: %s" (Sexp.to_string sexp))
  | Sexp.Atom name -> (
      print @@ lazy (sprintf "[sort_of_sexp] %s" name);
      match DTEnv.look_up_dt dtenv name with
      | Some dt -> Datatype.sort_of @@ Datatype.fresh_of dt
      | _ -> Sort.SVar (Ident.Svar name))
  | sexp ->
      failwith
      @@ sprintf "[sort_of_sexp] unknown sort: %s" (Sexp.to_string sexp)

let bind_of_sexp ~print dtenv = function
  | Sexp.List [ Sexp.Atom var; sort ] ->
      (Ident.Tvar var, sort_of_sexp ~print dtenv sort)
  | sexp ->
      failwith
      @@ sprintf "[bind_of_sexp] unknown bind: %s" (Sexp.to_string sexp)

let of_params ~print uni_senv sexps dtenv =
  List.rev sexps
  |> List.fold ~init:(uni_senv, Map.Poly.empty) ~f:(fun (uni_senv, acc) ->
       function
       | Sexp.List [ Sexp.Atom name; sort ] -> (
           try
             ( Map.Poly.add_exn uni_senv ~key:(Ident.Tvar name)
                 ~data:(sort_of_sexp ~print dtenv sort),
               Map.Poly.add_exn acc ~key:(Ident.Tvar name)
                 ~data:(sort_of_sexp ~print dtenv sort) )
           with _ -> failwith @@ name ^ " is already bound")
       | t -> failwith @@ "invalid param: " ^ Sexp.to_string t)

let is_con = function
  | "true" | "false" | "re.all" | "re.allchar" | "re.empty" | "re.nostr" -> true
  | _ -> false

let of_con = function
  | "true" -> T_bool.mk_true ()
  | "false" -> T_bool.mk_false ()
  | "re.all" | "re.allchar" -> T_regex.mk_full ()
  | "re.empty" | "re.nostr" -> T_regex.mk_empty ()
  | op -> failwith @@ "parse error : unknown constant symbol " ^ op

let is_pred_sym1 = function "is_int" -> true | _ -> false

let of_pred_sym1 = function
  | "is_int" -> T_irb.mk_is_int
  | op -> failwith @@ "parse error : unknown pred sym " ^ op

let is_fun_sym1 = function
  | "-" | "to_real" | "to_int" | "str.to.re" | "re.comp" | "re.*" | "re.+"
  | "re.opt" ->
      true
  | _ -> false

let of_fun_sym1 = function
  | "-" -> T_num.mk_nneg
  | "to_real" -> T_irb.mk_int_to_real
  | "to_int" -> T_irb.mk_real_to_int
  | "str.to.re" -> T_regex.mk_str_to_re
  | "re.comp" -> T_regex.mk_complement
  | "re.*" -> T_regex.mk_star
  | "re.+" -> T_regex.mk_plus
  | "re.opt" -> T_regex.mk_opt
  | op -> failwith @@ "parse error : unknown fun sym " ^ op

let is_pred_sym2 = function
  | "=" | "<" | ">" | "<=" | ">=" | "str.in.re" -> true
  | _ -> false

let of_pred_sym2 = function
  | "=" -> T_bool.mk_eq
  | "<" -> T_num.mk_nlt
  | ">" -> T_num.mk_ngt
  | "<=" -> T_num.mk_nleq
  | ">=" -> T_num.mk_ngeq
  | "str.in.re" -> T_regex.mk_str_in_regexp
  | op -> failwith @@ "parse error : unknown pred sym " ^ op

let is_fun_sym2 = function
  | "+" | "-" | "*" | "/" | "div" | "mod" | "rem" | "^" | "re.++" | "re.union"
  | "re.inter" ->
      true
  | _ -> false

let of_fun_sym2 = function
  | "+" -> T_num.mk_nadd
  | "-" -> T_num.mk_nsub
  | "*" -> T_num.mk_nmult
  | "/" -> T_real.mk_rdiv
  | "div" -> T_int.mk_div
  | "mod" -> T_num.mk_nmod
  | "rem" -> T_num.mk_nrem
  | "^" -> T_num.mk_npower
  | "re.++" -> T_regex.mk_concat
  | "re.union" -> T_regex.mk_union
  | "re.inter" -> T_regex.mk_inter
  | op -> failwith @@ "parse error : unknown fun sym " ^ op

let rec of_formula ~print ~inline (envs : Problem.envs) phi =
  let open Formula in
  (fun ret ->
    print @@ lazy ("[of_formula] input: " ^ Sexp.to_string phi);
    print @@ lazy ("[of_formula] output: " ^ Formula.str_of ret);
    ret)
  @@
  match phi with
  (* constant *)
  | Sexp.Atom "true" -> Formula.mk_true ()
  | Sexp.Atom "false" -> Formula.mk_false ()
  (* constant variable *)
  | Sexp.Atom name -> (
      match Map.Poly.find envs.uni_senv (Ident.Tvar name) with
      | Some sort ->
          assert (Term.is_bool_sort sort);
          Formula.of_bool_term @@ Term.mk_var (Ident.Tvar name) sort
      (*Formula.mk_atom @@ Atom.mk_pvar_app (Ident.Pvar name) [] []*)
      | None -> (
          match Map.Poly.find envs.exi_senv (Ident.Tvar name) with
          | Some sort ->
              assert (Term.is_bool_sort sort);
              Formula.mk_atom @@ Atom.mk_pvar_app (Ident.Pvar name) [] []
          | None -> (
              (* no arguments function *)
              match Map.Poly.find envs.fenv (Ident.Tvar name) with
              | Some
                  ( [],
                    T_bool.SBool,
                    Term.FunApp (T_bool.Formula phi, _, _),
                    _,
                    _ ) ->
                  if inline then phi
                  else
                    Formula.of_bool_term
                    @@ Term.mk_fvar_app (Ident.Tvar name) [ T_bool.SBool ] []
              | _ -> failwith @@ sprintf "%s is not bound" name)))
  (* logical operation *)
  | Sexp.List [ Sexp.Atom "not"; phi ] ->
      mk_neg @@ of_formula ~print ~inline envs phi
  | Sexp.List (Sexp.Atom "and" :: phis) ->
      and_of @@ List.rev_map phis ~f:(of_formula ~print ~inline envs)
  | Sexp.List (Sexp.Atom "or" :: phis) ->
      or_of @@ List.rev_map phis ~f:(of_formula ~print ~inline envs)
  | Sexp.List (Sexp.Atom "xor" :: phis) ->
      xor_of @@ List.rev_map phis ~f:(of_formula ~print ~inline envs)
  | Sexp.List [ Sexp.Atom "=>"; phi1; phi2 ] ->
      let phi1 = of_formula ~print ~inline envs phi1 in
      let phi2 = of_formula ~print ~inline envs phi2 in
      mk_imply phi1 phi2
  (* binder *)
  | Sexp.List [ Sexp.Atom "forall"; Sexp.List params; phi ] ->
      let uni_senv, params = of_params ~print envs.uni_senv params envs.dtenv in
      mk_forall (Map.Poly.to_alist params)
      @@ of_formula ~print ~inline { envs with uni_senv } phi
  | Sexp.List [ Sexp.Atom "exists"; Sexp.List params; phi ] ->
      let uni_senv, params = of_params ~print envs.uni_senv params envs.dtenv in
      mk_exists (Map.Poly.to_alist params)
      @@ of_formula ~print ~inline { envs with uni_senv } phi
  | Sexp.List [ Sexp.Atom "random"; Sexp.List params; phi ] ->
      let uni_senv, params = of_random_params ~print ~inline envs params in
      mk_randoms params @@ of_formula ~print ~inline { envs with uni_senv } phi
  (* let *)
  | Sexp.List [ Sexp.Atom "let"; Sexp.List bounds; phi ] ->
      let bounds =
        List.map bounds ~f:(function
          | Sexp.List [ Sexp.Atom name; t ] ->
              let def = of_term ~print ~inline envs t in
              (Ident.Tvar name, Term.sort_of def, def)
          | sexp -> failwith @@ "Invalid param: " ^ Sexp.to_string_hum sexp)
      in
      let uni_senv =
        List.fold bounds ~init:envs.uni_senv ~f:(fun uni_senv (tvar, sort, _) ->
            Map.Poly.add_exn uni_senv ~key:tvar ~data:sort)
      in
      let envs = { envs with uni_senv } in
      List.rev bounds
      |> List.fold ~init:(of_formula ~print ~inline envs phi)
           ~f:(fun body (var, sort, def) ->
             Formula.mk_let_formula var sort def body)
  (* ite *)
  | Sexp.List [ Sexp.Atom "ite"; cond; then_; else_ ] ->
      let t =
        T_bool.mk_if_then_else
          (of_term ~print ~inline envs cond)
          (of_term ~print ~inline envs then_)
          (of_term ~print ~inline envs else_)
      in
      if T_bool.is_sbool t then Formula.eq t @@ T_bool.mk_true ()
      else assert false
  (* unary predicate symbol application *)
  | Sexp.List [ Sexp.Atom op; t ] when is_pred_sym1 op ->
      mk_atom @@ of_pred_sym1 op @@ of_term ~print ~inline envs t
  (* binary predicate symbol application *)
  | Sexp.List [ Sexp.Atom op; t1; t2 ] when is_pred_sym2 op ->
      mk_atom
      @@ of_pred_sym2 op
           (of_term ~print ~inline envs t1)
           (of_term ~print ~inline envs t2)
  (* predicate symbol application *)
  | Sexp.List (Sexp.Atom "distinct" :: ts) ->
      and_of @@ Set.to_list
      @@ Set.fold_distinct_pairs ~init:Set.Poly.empty ~f:(fun acc x y ->
             Set.add acc @@ Formula.neq x y)
      @@ Set.Poly.of_list
      @@ List.map ts ~f:(of_term ~print ~inline envs)
  (* datatype predicate application *)
  | Sexp.List
      [
        Sexp.List
          [
            Sexp.Atom "_";
            Sexp.Atom "is";
            (Sexp.List [ Sexp.Atom name; _; _ ] | Sexp.Atom name);
          ];
        t;
      ] -> (
      match DTEnv.look_up_func envs.dtenv name with
      | Some (dt, Datatype.FCons cons) ->
          mk_atom
          @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons)
          @@ of_term ~print ~inline envs t
      | _ -> assert false)
  (*TODO: support ':named' well*)
  | Sexp.List [ Sexp.Atom "!"; t; Sexp.Atom ":named"; Sexp.Atom _ ] ->
      print @@ lazy "! :named";
      let sort = Term.sort_of @@ of_term ~print ~inline envs t in
      if Term.is_bool_sort sort then of_formula ~print ~inline envs t
      else failwith "must be bool fun"
  | Sexp.List (Sexp.Atom "!" :: t :: Sexp.Atom ":pattern" :: _) ->
      of_formula ~print ~inline envs t
  (* predicate variable application *)
  | Sexp.List (Sexp.Atom name :: args) -> (
      print @@ lazy (sprintf "[formula] predicate %s" name);
      let args = List.map args ~f:(of_term ~print ~inline envs) in
      match Map.Poly.find envs.exi_senv (Ident.Tvar name) with
      | Some sort ->
          let sargs, sret = Sort.args_ret_of sort in
          assert (Term.is_bool_sort sret);
          mk_atom @@ Atom.mk_pvar_app (Ident.Pvar name) sargs args
      | None -> (
          match Map.Poly.find envs.uni_senv (Ident.Tvar name) with
          | Some sort ->
              let sargs, sret = Sort.args_ret_of sort in
              assert (Term.is_bool_sort sret);
              mk_atom @@ Atom.mk_pvar_app (Ident.Pvar name) sargs args
          | None -> (
              match Map.Poly.find envs.fenv (Tvar name) with
              | Some
                  ( fargs,
                    T_bool.SBool,
                    Term.FunApp (T_bool.Formula phi, [], _),
                    false,
                    _ ) ->
                  if inline then (
                    assert (List.length args = List.length fargs);
                    let sub =
                      Map.Poly.of_alist_exn
                      @@ List.zip_exn (List.map ~f:fst fargs) args
                    in
                    Formula.subst sub phi)
                  else
                    Formula.of_bool_term
                    @@ Term.mk_fvar_app (Ident.Tvar name)
                         (List.map ~f:snd fargs @ [ T_bool.SBool ])
                         args
              | Some (fargs, T_bool.SBool, _, true, _) ->
                  assert (List.length args = List.length fargs);
                  Formula.of_bool_term
                  @@ Term.mk_fvar_app (Tvar name)
                       (List.map ~f:snd fargs @ [ T_bool.SBool ])
                       args
              | Some _ -> failwith ""
              | None -> failwith @@ sprintf "%s is not bound" name)))
  | sexp -> failwith @@ "parse error : " ^ Sexp.to_string_hum sexp

and is_included_pvars ~print ~inline envs = function
  | [] -> false
  | Sexp.List [ Sexp.Atom _; t ] :: sexps ->
      let phi = of_formula ~print ~inline envs t in
      if
        LogicOld.Formula.number_of_pvar_apps true phi
        + LogicOld.Formula.number_of_pvar_apps false phi
        > 0
      then true
      else is_included_pvars ~print ~inline envs sexps
  | sexp :: _ -> failwith @@ "invalid bounds: " ^ Sexp.to_string_hum sexp

and of_term ~print ~inline envs =
  let open Term in
  function
  (* ite *)
  | Sexp.List [ Sexp.Atom "ite"; cond; then_; else_ ] ->
      T_bool.mk_if_then_else
        (of_term ~print ~inline envs cond)
        (of_term ~print ~inline envs then_)
        (of_term ~print ~inline envs else_)
  (* let *)
  | Sexp.List [ Sexp.Atom "let"; Sexp.List def; body ] -> (
      let aux def body =
        let def =
          List.rev_map def ~f:(function
            | Sexp.List [ Sexp.Atom name; t ] ->
                (Ident.Tvar name, of_term ~print ~inline envs t)
            | sexp -> failwith @@ "invalid param : " ^ Sexp.to_string_hum sexp)
        in
        let uni_senv =
          List.fold def ~init:envs.uni_senv ~f:(fun uni_senv (tvar, t) ->
              Map.Poly.add_exn uni_senv ~key:tvar ~data:(Term.sort_of t))
        in
        let envs = { envs with uni_senv } in
        List.fold def ~init:(of_term ~print ~inline envs body)
          ~f:(fun acc (tvar, t) -> Term.mk_let_term tvar (Term.sort_of t) t acc)
      in
      try
        if is_included_pvars ~print ~inline envs def then
          failwith
            "Invalid let-expressions (It is not allowed to use let-term \
             binding predicate applications into some name.)"
        else aux def body
      with _ -> aux def body)
  (* constant *)
  | Sexp.Atom op when is_con op -> of_con op
  (* constant variable *)
  | Sexp.Atom name -> (
      if
        String.is_prefix name ~prefix:"\"" && String.is_suffix name ~suffix:"\""
      then T_string.make @@ String.sub name ~pos:1 ~len:(String.length name - 2)
      else
        try (* case on integer/decimal constants *) T_num.mk_value name
        with _ -> (
          (* other cases *)
          match Map.Poly.find envs.uni_senv (Ident.Tvar name) with
          | Some sort -> mk_var (Ident.Tvar name) sort
          | None -> (
              match Map.Poly.find envs.exi_senv (Ident.Tvar name) with
              | Some sort -> mk_var (Ident.Tvar name) sort
              | None -> (
                  match Map.Poly.find envs.fenv (Ident.Tvar name) with
                  | Some ([], ret_sort, t, false, _) ->
                      if inline then t
                      else Term.mk_fvar_app (Ident.Tvar name) [ ret_sort ] []
                  | Some ([], ret_sort, _, true, _) ->
                      Term.mk_fvar_app (Ident.Tvar name) [ ret_sort ] []
                  | Some _ -> failwith ""
                  | None -> (
                      match DTEnv.look_up_func envs.dtenv name with
                      | Some (dt, Datatype.FCons cons)
                        when List.is_empty @@ Datatype.sels_of_cons cons ->
                          T_dt.mk_cons dt name []
                      | _ -> failwith @@ sprintf "%s is not bound" name)))))
  (* unary function symbol application *)
  | Sexp.List [ Sexp.Atom op; t ] when is_fun_sym1 op ->
      of_fun_sym1 op @@ of_term ~print ~inline envs t
  (* binary function symbol application *)
  | Sexp.List [ Sexp.Atom op; t1; t2 ] when is_fun_sym2 op ->
      of_fun_sym2 op
        (of_term ~print ~inline envs t1)
        (of_term ~print ~inline envs t2)
  (* function symbol application *)
  | Sexp.List (Sexp.Atom "+" :: arg :: args) ->
      List.fold args ~init:(of_term ~print ~inline envs arg) ~f:(fun acc ->
          of_term ~print ~inline envs >> T_num.mk_nadd acc)
  | Sexp.List (Sexp.Atom "*" :: arg :: args) ->
      List.fold args ~init:(of_term ~print ~inline envs arg) ~f:(fun acc ->
          of_term ~print ~inline envs >> T_num.mk_nmult acc)
  | Sexp.List (Sexp.Atom "re.++" :: arg :: args) ->
      List.fold args ~init:(of_term ~print ~inline envs arg) ~f:(fun acc ->
          of_term ~print ~inline envs >> T_regex.mk_concat acc)
  (* datatype function application *)
  | Sexp.List (Sexp.Atom name :: args) as t
    when DTEnv.name_is_func envs.dtenv name -> (
      print @@ lazy (sprintf "[term] datatype func %s" name);
      match
        ( DTEnv.look_up_func envs.dtenv name,
          List.map args ~f:(of_term ~print ~inline envs) )
      with
      | Some (dt, Datatype.FCons _), args -> T_dt.mk_cons dt name args
      | Some (dt, Datatype.FSel _), [ arg ] -> T_dt.mk_sel dt name arg
      | Some (_, Datatype.FSel _), _ -> failwith ""
      | _ -> T_bool.of_formula @@ of_formula ~print ~inline envs t)
  (* array function application *)
  | Sexp.List [ Sexp.Atom "select"; t1; t2 ] -> (
      let arr = of_term ~print ~inline envs t1 in
      let i = of_term ~print ~inline envs t2 in
      match sort_of arr with
      | T_array.SArray (s1, s2) -> T_array.mk_select s1 s2 arr i
      | _ -> failwith "")
  | Sexp.List [ Sexp.Atom "store"; t1; t2; t3 ] -> (
      let arr = of_term ~print ~inline envs t1 in
      let i = of_term ~print ~inline envs t2 in
      let e = of_term ~print ~inline envs t3 in
      match sort_of arr with
      | T_array.SArray (s1, s2) -> T_array.mk_store s1 s2 arr i e
      | _ -> failwith "")
  | Sexp.List [ Sexp.List [ Sexp.Atom "as"; Sexp.Atom "const"; sort ]; value ]
    -> (
      let arr_sort = sort_of_sexp ~print envs.dtenv sort in
      let arr_value = of_term ~print ~inline envs value in
      match arr_sort with
      | T_array.SArray (s1, s2) -> T_array.mk_const_array s1 s2 arr_value
      | _ -> failwith "")
  (* function variable application *)
  | Sexp.List (Sexp.Atom name :: args) as t -> (
      match Map.Poly.find envs.fenv (Tvar name) with
      | Some (fargs, ret_sort, term, false, _) ->
          if inline then
            let sub =
              Map.Poly.of_alist_exn
              @@ List.zip_exn (List.map ~f:fst fargs)
              @@ List.map args ~f:(of_term ~print ~inline envs)
            in
            Term.subst sub term
          else
            Term.mk_fvar_app (Ident.Tvar name)
              (List.map ~f:snd fargs @ [ ret_sort ])
            @@ List.map args ~f:(of_term ~print ~inline envs)
      | Some (fargs, ret_sort, _, true, _) ->
          Term.mk_fvar_app (Ident.Tvar name)
            (List.map ~f:snd fargs @ [ ret_sort ])
          @@ List.map args ~f:(of_term ~print ~inline envs)
      | _ -> (
          match Map.Poly.find envs.exi_senv (Ident.Tvar name) with
          | Some sort ->
              let sargs, sret = Sort.args_ret_of sort in
              if Term.is_bool_sort sret then
                T_bool.of_formula @@ of_formula ~print ~inline envs t
              else (
                assert (List.length args = List.length sargs);
                Term.mk_fvar_app (Ident.Tvar name) (sargs @ [ sret ])
                @@ List.map args ~f:(of_term ~print ~inline envs))
          | None -> T_bool.of_formula @@ of_formula ~print ~inline envs t))
  | t -> T_bool.of_formula @@ of_formula ~print ~inline envs t

and dist_of_sexp ~print ~inline envs = function
  | Sexp.List [ Sexp.Atom "Uniform"; t1; t2 ] ->
      Rand.mk_uniform
        (of_term ~print ~inline envs t1)
        (of_term ~print ~inline envs t2)
  | Sexp.List [ Sexp.Atom "Gauss"; t1; t2 ] ->
      Rand.mk_gauss
        (of_term ~print ~inline envs t1)
        (of_term ~print ~inline envs t2)
  | Sexp.List [ Sexp.Atom "IntUniform"; t1; t2 ] ->
      Rand.mk_int_uniform
        (of_term ~print ~inline envs t1)
        (of_term ~print ~inline envs t2)
  | _ -> assert false

and of_random_params ~print ~inline envs sexp =
  List.fold (List.rev sexp) ~init:(envs.uni_senv, [])
    ~f:(fun (uni_senv, params) -> function
    | Sexp.List [ Sexp.Atom name; dist ] ->
        let rand = dist_of_sexp ~print ~inline envs dist in
        ( Map.Poly.add_exn uni_senv ~key:(Ident.Tvar name)
            ~data:(Rand.sort_of rand),
          (Ident.Tvar name, rand) :: params )
    | sexp -> failwith @@ "error of " ^ Sexp.to_string sexp)

(*let restrict_head bounds args fml =
  List.fold args ~init:(bounds, [], fml)
    ~f:(fun (bounds, args, fml) arg ->
        let arg_sort : Sort.t = Term.sort_of arg in
        let new_name : Ident.tvar = Ident.mk_fresh_head_arg () in
        let new_arg : Term.t = Term.mk_var new_name arg_sort in
        (new_name, arg_sort) :: bounds, new_arg :: args,
        Formula.and_of [fml; Formula.eq new_arg arg])*)

let is_available str =
  let logiclist =
    [
      "HORN";
      "SYGUS";
      "QF_LIA";
      "QF_NRA";
      "QF_LIA";
      "QF_LRA";
      "QF_LIRA";
      "QF_NIA";
      "QF_NRA";
      "QF_NIRA";
      "LIA";
      "LRA";
      "NIA";
      "NRA";
      "SAT";
      "QF_DT";
      "QF_UF";
      "QF_ALIA";
      "ALL_SUPPORTED";
      "AUFLIA";
    ]
  in
  List.exists logiclist ~f:(String.( = ) str)

let mk_dt_sel ~print dtenv dt dts = function
  | Sexp.List [ Sexp.Atom name; (Sexp.Atom ret_name as ret) ] -> (
      match List.find dts ~f:(Datatype.name_of_dt >> String.( = ) ret_name) with
      | Some _ -> Datatype.mk_insel name ret_name (Datatype.params_of_dt dt)
      | None -> Datatype.mk_sel name @@ sort_of_sexp ~print dtenv ret)
  | Sexp.List
      [ Sexp.Atom name; (Sexp.List (Sexp.Atom ret_name :: args) as ret) ] -> (
      match List.find dts ~f:(Datatype.name_of_dt >> String.( = ) ret_name) with
      | Some _ ->
          Datatype.mk_insel name ret_name
          @@
          if String.(Datatype.name_of_dt dt = ret_name) then
            Datatype.params_of_dt dt (*ToDo: args?*)
          else List.map args ~f:(sort_of_sexp ~print dtenv)
      | None -> Datatype.mk_sel name @@ sort_of_sexp ~print dtenv ret)
  | sexp -> failwith @@ Sexp.to_string sexp

let mk_dt_cons ~print dtenv dt dts = function
  | Sexp.Atom name | Sexp.List [ Sexp.Atom name ] -> Datatype.mk_cons name
  | Sexp.List (Sexp.Atom name :: sels) ->
      Datatype.mk_cons name
        ~sels:(List.map sels ~f:(mk_dt_sel ~print dtenv dt dts))
  | sexp -> failwith @@ sprintf "[mk_dt_cons] %s" (Sexp.to_string sexp)

let mk_new_datatypes ~print dtenv dts funcs flag =
  let datatypes =
    List.map2_exn funcs dts ~f:(fun func -> function
      | Sexp.List [ Sexp.Atom name; Sexp.Atom "0" ] -> Datatype.mk_dt name []
      | Sexp.List [ Sexp.Atom name; Sexp.Atom n ] -> (
          match func with
          | Sexp.List (Sexp.Atom "par" :: Sexp.List args :: _)
          | Sexp.List (Sexp.List [ Sexp.Atom "par"; Sexp.List args ] :: _) ->
              assert (List.length args = int_of_string n);
              Datatype.mk_dt name
              @@ List.map args ~f:(function
                   | Sexp.Atom name -> Sort.SVar (Ident.Svar name)
                   | _ -> assert false)
          | _ -> assert false)
      | _ -> assert false)
  in
  let datatypes =
    List.map2_exn datatypes funcs ~f:(fun dt -> function
      | Sexp.List [ Sexp.Atom "par"; Sexp.List _; Sexp.List conses ]
      | Sexp.List (Sexp.List [ Sexp.Atom "par"; Sexp.List _ ] :: conses)
      | Sexp.List conses ->
          let conses =
            List.fold_left ~init:[] conses ~f:(fun conses cons ->
                mk_dt_cons ~print dtenv dt datatypes cons :: conses)
          in
          { dt with conses }
      | _ -> assert false)
  in
  List.map datatypes ~f:(fun dt ->
      Datatype.make (Datatype.name_of_dt dt) datatypes flag)

let mk_old_datatypes ~print dtenv dts flag args =
  let args =
    List.map args ~f:(function
      | Sexp.Atom name -> Sort.SVar (Ident.Svar name)
      | _ -> assert false)
  in
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
                mk_dt_cons ~print dtenv dt datatypes cons :: conses)
          in
          { dt with conses }
      | _ -> assert false)
  in
  List.map datatypes ~f:(fun dt ->
      Datatype.make (Datatype.name_of_dt dt) datatypes flag)

let rec toplevel ~print ~inline acc (envs : Problem.envs) = function
  | [] ->
      let acc' =
        List.map acc
          ~f:
            (Normalizer.normalize_let ~rename:true
            >> Formula.elim_let_with_unknowns (Map.key_set envs.exi_senv)
            >> Normalizer.normalize)
      in
      (*ToDo*)
      LogicOld.set_fenv
      @@ Map.force_merge
           (Map.Poly.filter envs.fenv ~f:(fun (_, _, _, is_rec, _) -> is_rec))
      @@ LogicOld.get_fenv ();
      (acc', envs)
  | Sexp.List [ Sexp.Atom "set-logic"; Sexp.Atom logic ] :: es ->
      assert (is_available logic);
      toplevel ~print ~inline acc envs es
  | Sexp.List (Sexp.Atom "set-info" :: Sexp.Atom name :: t :: _) :: es -> (
      match Map.Poly.find envs.fenv (Tvar name) with
      | Some (fargs, ret_sort, body, is_rec, _ (* ToDo *)) ->
          let fenv' =
            (* ToDo *)
            let phi =
              Typeinf.typeinf_formula ~print ~to_sus:true
              @@ of_formula ~print ~inline envs t
            in
            Map.Poly.set envs.fenv ~key:(Tvar name)
              ~data:(fargs, ret_sort, body, is_rec, phi)
          in
          toplevel ~print ~inline acc { envs with fenv = fenv' } es
      | None -> toplevel ~print ~inline acc envs es (* ToDo: ignored? *))
  | Sexp.List (Sexp.Atom ("set-info" | "set-option") :: _) :: es
  | Sexp.List [ Sexp.Atom ("get-model" | "check-sat" | "exit") ] :: es ->
      toplevel ~print ~inline acc envs es (* ToDo: ignored? *)
  | Sexp.List [ Sexp.Atom "declare-sort"; Sexp.Atom name; Sexp.Atom numeral ]
    :: es ->
      let dtenv' =
        DTEnv.update_dt envs.dtenv
        @@ Datatype.mk_uninterpreted_datatype ~numeral:(Int.of_string numeral)
             name
      in
      toplevel ~print ~inline acc { envs with dtenv = dtenv' } es
  | Sexp.List [ Sexp.Atom "declare-datatypes"; Sexp.List args; Sexp.List dts ]
    :: es
    when List.for_all args ~f:(function Sexp.Atom _ -> true | _ -> false) ->
      let dtenv' =
        List.fold_left ~init:envs.dtenv ~f:DTEnv.update_dt
        @@ mk_old_datatypes ~print envs.dtenv dts Datatype.FDt args
      in
      print @@ lazy (sprintf "datatype env:\n%s" @@ DTEnv.str_of dtenv');
      toplevel ~print ~inline acc { envs with dtenv = dtenv' } es
  | Sexp.List [ Sexp.Atom "declare-datatypes"; Sexp.List dts; Sexp.List funcs ]
    :: es ->
      let dtenv' =
        List.fold_left ~init:envs.dtenv ~f:DTEnv.update_dt
        @@ mk_new_datatypes ~print envs.dtenv dts funcs Datatype.FDt
      in
      print @@ lazy (sprintf "datatype env:\n%s" @@ DTEnv.str_of dtenv');
      toplevel ~print ~inline acc { envs with dtenv = dtenv' } es
  | Sexp.List [ Sexp.Atom "declare-codatatypes"; Sexp.List args; Sexp.List dts ]
    :: es
    when List.for_all args ~f:(function Sexp.Atom _ -> true | _ -> false) ->
      let dtenv' =
        List.fold_left ~init:envs.dtenv ~f:DTEnv.update_dt
        @@ mk_old_datatypes ~print envs.dtenv dts Datatype.FCodt args
      in
      print @@ lazy (sprintf "datatype env:\n%s" @@ DTEnv.str_of dtenv');
      toplevel ~print ~inline acc { envs with dtenv = dtenv' } es
  | Sexp.List
      [ Sexp.Atom "declare-codatatypes"; Sexp.List dts; Sexp.List funcs ]
    :: es ->
      let dtenv' =
        List.fold_left ~init:envs.dtenv ~f:DTEnv.update_dt
        @@ mk_new_datatypes ~print envs.dtenv dts funcs Datatype.FCodt
      in
      print @@ lazy (sprintf "datatype env:\n%s" @@ DTEnv.str_of dtenv');
      toplevel ~print ~inline acc { envs with dtenv = dtenv' } es
  | Sexp.List
      [
        Sexp.Atom "declare-fnp";
        Sexp.Atom name;
        Sexp.List args;
        Sexp.Atom "Bool";
      ]
    :: es ->
      (*print @@ lazy ("adding " ^ name);*)
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name)
          ~data:
            (Sort.mk_fun
            @@ List.map args ~f:(sort_of_sexp ~print envs.dtenv)
            @ [ T_bool.SBool ])
      in
      let kind_map' =
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name) ~data:Kind.FN
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List
      [
        Sexp.Atom "declare-wfp";
        Sexp.Atom name;
        Sexp.List args;
        Sexp.Atom "Bool";
      ]
    :: es ->
      (*print @@ lazy ("adding " ^ name);*)
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name)
          ~data:
            (Sort.mk_fun
            @@ List.map args ~f:(sort_of_sexp ~print envs.dtenv)
            @ [ T_bool.SBool ])
      in
      let kind_map' =
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name) ~data:Kind.WF
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List
      [
        Sexp.Atom "declare-fun";
        Sexp.Atom name;
        Sexp.List args;
        Sexp.Atom "Bool";
      ]
    :: es ->
      (*print @@ lazy ("adding " ^ name);*)
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name)
          ~data:
            (Sort.mk_fun
            @@ List.map args ~f:(sort_of_sexp ~print envs.dtenv)
            @ [ T_bool.SBool ])
      in
      let kind_map' =
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name) ~data:Kind.Ord
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List [ Sexp.Atom "declare-fun"; Sexp.Atom name; Sexp.List args; ret ]
    :: es ->
      (*print @@ lazy ("adding " ^ name);*)
      let args_sort = List.map args ~f:(sort_of_sexp ~print envs.dtenv) in
      let ret_sort = sort_of_sexp ~print envs.dtenv ret in
      let fun_sort = Sort.mk_fun @@ args_sort @ [ ret_sort ] in
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name) ~data:fun_sort
      in
      let kind_map' =
        let kind =
          if Term.is_int_sort ret_sort then Kind.IntFun
          else if Term.is_regex_sort ret_sort && List.is_empty args_sort then
            Kind.RegEx
          else
            failwith
              ("synthesis of a function of the sort "
             ^ Term.str_of_sort fun_sort ^ " is not supported")
        in
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name) ~data:kind
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List [ Sexp.Atom "declare-const"; Sexp.Atom name; ty ] :: es ->
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name)
          ~data:(sort_of_sexp ~print envs.dtenv ty)
      in
      let kind_map' = envs.kind_map (*ToDo*) in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List
      [ Sexp.Atom "define-fun"; Sexp.Atom name; Sexp.List fargs; ty; body ]
    :: es ->
      let fenv' =
        let fargs' = List.map fargs ~f:(bind_of_sexp ~print envs.dtenv) in
        let sort = sort_of_sexp ~print envs.dtenv ty in
        let body =
          (* the scope is within body *)
          let uni_senv' =
            Map.force_merge envs.uni_senv (Map.Poly.of_alist_exn fargs')
          in
          let envs = { envs with uni_senv = uni_senv' } in
          Typeinf.typeinf_term ~print ~to_sus:true
          @@
          if Term.is_bool_sort sort then
            T_bool.of_formula @@ of_formula ~print ~inline envs body
          else of_term ~print ~inline envs body
        in
        Map.Poly.add_exn envs.fenv ~key:(Tvar name)
          ~data:(fargs', sort, body, false, Formula.mk_true ())
      in
      toplevel ~print ~inline acc { envs with fenv = fenv' } es
  | Sexp.List
      [ Sexp.Atom "define-fun-rec"; Sexp.Atom name; Sexp.List fargs; ty; body ]
    :: es ->
      let fenv' =
        let fargs' = List.map fargs ~f:(bind_of_sexp ~print envs.dtenv) in
        let sort = sort_of_sexp ~print envs.dtenv ty in
        let body =
          (* the scope is within body *)
          let uni_senv' =
            Map.force_merge envs.uni_senv (Map.Poly.of_alist_exn fargs')
          in
          let fenv' =
            let body_rec = Term.mk_var (Tvar name) sort (*ToDo*) in
            Map.Poly.add_exn envs.fenv ~key:(Tvar name)
              ~data:(fargs', sort, body_rec, true, Formula.mk_true ())
          in
          let envs = { envs with uni_senv = uni_senv'; fenv = fenv' } in
          Typeinf.typeinf_term ~print ~to_sus:true
          @@
          if Term.is_bool_sort sort then
            T_bool.of_formula @@ of_formula ~print ~inline envs body
          else of_term ~print ~inline envs body
        in
        Map.Poly.add_exn envs.fenv ~key:(Tvar name)
          ~data:(fargs', sort, body, true, Formula.mk_true ())
      in
      toplevel ~print ~inline acc { envs with fenv = fenv' } es
  | Sexp.List [ Sexp.Atom "assert"; phi ] :: es ->
      toplevel ~print ~inline
        (of_formula ~print ~inline envs phi :: acc)
        envs es
  (* extensions for CHCs *)
  | Sexp.List [ Sexp.Atom "declare-var"; Sexp.Atom name; sort ] :: es ->
      let uni_senv' =
        Map.Poly.add_exn envs.uni_senv ~key:(Ident.Tvar name)
          ~data:(sort_of_sexp ~print envs.dtenv sort)
      in
      toplevel ~print ~inline acc { envs with uni_senv = uni_senv' } es
  | Sexp.List [ Sexp.Atom "declare-rel"; Sexp.Atom name; Sexp.List args ] :: es
    ->
      (*print @@ lazy ("adding " ^ name);*)
      let exi_senv' =
        Map.Poly.add_exn envs.exi_senv ~key:(Ident.Tvar name)
          ~data:
            (Sort.mk_fun
            @@ List.map args ~f:(sort_of_sexp ~print envs.dtenv)
            @ [ T_bool.SBool ])
      in
      let kind_map' =
        Map.Poly.add_exn envs.kind_map ~key:(Ident.Tvar name) ~data:Kind.Ord
      in
      toplevel ~print ~inline acc
        { envs with exi_senv = exi_senv'; kind_map = kind_map' }
        es
  | Sexp.List [ Sexp.Atom "rule"; phi ] :: es ->
      let phi = of_formula ~print ~inline envs phi in
      let bounds =
        List.filter_map
          (Set.to_list @@ Formula.fvs_of phi)
          ~f:(fun v ->
            match Map.Poly.find envs.uni_senv v with
            | None -> None
            | Some s -> Some (v, s))
      in
      toplevel ~print ~inline (Formula.mk_forall bounds phi :: acc) envs es
  | Sexp.List [ Sexp.Atom "query"; phi ] :: es ->
      let phi = of_formula ~print ~inline envs phi in
      assert (Set.is_empty @@ Formula.fvs_of phi)
      (*ToDo: check that phi is a predicate variable without arguments*);
      toplevel ~print ~inline (Formula.mk_neg phi :: acc) envs es
  | sexps ->
      failwith @@ "parse error : " ^ Sexp.to_string_hum @@ Sexp.List sexps

let from_smt2_file ~print ~inline ?(uni_senv = Map.Poly.empty)
    ?(exi_senv = Map.Poly.empty) ?(kind_map = Map.Poly.empty)
    ?(fenv = Map.Poly.empty) ?(dtenv = Map.Poly.empty) filename =
  let phis, _envs =
    filename |> In_channel.create |> Lexing.from_channel
    |> Parser.program Lexer.token
    |> toplevel ~print ~inline [] { uni_senv; exi_senv; kind_map; fenv; dtenv }
  in
  let phi = Formula.and_of phis in
  print @@ lazy (sprintf "before typeinf: %s" @@ Formula.str_of phi);
  let phi' = Typeinf.typeinf_formula ~print ~to_sus:true phi in
  print @@ lazy (sprintf "after typeinf: %s" @@ Formula.str_of phi');
  phi'

let from_string ~print ~inline ?(uni_senv = Map.Poly.empty)
    ?(exi_senv = Map.Poly.empty) ?(kind_map = Map.Poly.empty)
    ?(fenv = Map.Poly.empty) ?(dtenv = Map.Poly.empty) =
  Lexing.from_string >> Parser.program Lexer.token
  >> toplevel ~print ~inline [] { uni_senv; exi_senv; kind_map; fenv; dtenv }
