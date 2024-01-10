open Core
open Typedtree
open Common
open Common.Ext
open Common.Util
open Ast.LogicOld

module Make (Config : Config.ConfigType) = struct
  let config = Config.config
  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))
  let _ = Debug.set_module_name "MBcsol"

  let str_of_stdbuf ~f obj =
    Buffer.clear Format.stdbuf;
    f Format.str_formatter obj;
    Buffer.contents Format.stdbuf
  let str_of_typedtree_structure = str_of_stdbuf ~f:Printtyped.implementation
  let str_of_typedtree_interface = str_of_stdbuf ~f:Printtyped.interface
  let str_of_parse_structure = str_of_stdbuf ~f:Pprintast.structure
  let str_of_tenv tenv =
    Buffer.clear Format.stdbuf;
    Bytepackager.package_files ~ppf_dump:Format.str_formatter tenv [] "";
    Buffer.contents Format.stdbuf
  let rec str_of_expr expr =
    match expr.exp_desc with
    | Texp_ident (p, _, _) -> "Texp_ident " ^ Path.name p
    | Texp_constant _ -> "Texp_constant"
    | Texp_let _ -> "Texp_let"
    | Texp_function _ -> "Texp_function"
    | Texp_apply (e, es) ->
      "Texp_apply : " ^
      String.concat ~sep:" " @@
      str_of_expr e :: List.map es ~f:(function (_, Some e) -> str_of_expr e | _ -> "")
    | Texp_match _ -> "Texp_match"
    | Texp_try _ -> "Texp_try"
    | Texp_variant _ -> "Texp_variant"
    | Texp_record _ -> "Texp_record"
    | Texp_field _ -> "Texp_field"
    | Texp_setfield _ -> "Texp_setfield"
    | Texp_array _ -> "Texp_array"
    | Texp_ifthenelse _ -> "Texp_ifthenelse"
    | Texp_sequence _ -> "Texp_sequence"
    | Texp_while _ -> "Texp_while"
    | Texp_for _ -> "Texp_for"
    | Texp_send _ -> "Texp_send"
    | Texp_new _ -> "Texp_new"
    | Texp_instvar _ -> "Texp_instvar"
    | Texp_setinstvar _ -> "Texp_setinstvar"
    | Texp_override _ -> "Texp_override"
    | Texp_letmodule _ -> "Texp_letmodule"
    | Texp_letexception _ -> "Texp_letexception"
    | Texp_assert _ -> "Texp_assert"
    | Texp_lazy _ -> "Texp_lazy"
    | Texp_object _ -> "Texp_object"
    | Texp_pack _ -> "Texp_pack"
    | Texp_letop _ -> "Texp_letop"
    | Texp_unreachable -> "Texp_unreachable"
    | Texp_extension_constructor _ -> "Texp_extension_constructor"
    | Texp_open _ -> "Texp_open"
    | Texp_tuple _ -> "Texp_tuple"
    | Texp_construct _ -> "Texp_construct"

  let rec sort_of_core_type ?(rectyps=None) dtenv (ct:core_type) =
    match ct.ctyp_desc with
    | Ttyp_var name ->
      (*print_endline @@ "Ttyp_var " ^ name;*)
      Sort.SVar (Svar name)
    | Ttyp_constr (ret_name, _, args) ->
      (*print_endline @@ "Ttyp_constr " ^ Path.name ret_name;*)
      let args = List.map args ~f:(sort_of_core_type ~rectyps dtenv) in
      (*List.iter args ~f:(fun arg -> print_endline @@ Term.str_of_sort arg);*)
      Ast.Typeinf.sort_of_name ~rectyps dtenv ~args @@ Path.name ret_name
    | Ttyp_any ->
      failwith "[sort_of_core_type] Ttyp_any not supported"
    | Ttyp_arrow (Nolabel, ct1, ct2) ->
      Sort.mk_arrow
        (sort_of_core_type ~rectyps dtenv ct1)
        (sort_of_core_type ~rectyps dtenv ct2)
    | Ttyp_arrow ((Labelled _ | Optional _), _, _) ->
      failwith "[sort_of_core_type] Ttyp_arrow not supported"
    | Ttyp_tuple elems ->
      T_tuple.STuple (List.map elems ~f:(sort_of_core_type ~rectyps dtenv))
    | Ttyp_object (_, _) ->
      failwith "[sort_of_core_type] Ttyp_object not supported"
    | Ttyp_class (_, _, _) ->
      failwith "[sort_of_core_type] Ttyp_class not supported"
    | Ttyp_alias (_, _) ->
      failwith "[sort_of_core_type] Ttyp_alias not supported"
    | Ttyp_variant (_, _, _) ->
      failwith "[sort_of_core_type] Ttyp_variant not supported"
    | Ttyp_poly (_, _) ->
      failwith "[sort_of_core_type] Ttyp_poly not supported"
    | Ttyp_package _ ->
      failwith "[sort_of_core_type] Ttyp_package not supported"
  exception NoTypeExpansion
  let rec sort_of_type_expr ?(lift = false) ?(env=Env.empty) dtenv ty =
    let open Types in
    match (Types.Transient_expr.repr ty).desc with
    | Tlink e ->
      sort_of_type_expr ~lift ~env dtenv e
    | Tpoly (ty, tys) ->
      let svs =
        Set.Poly.of_list @@ List.map tys ~f:(fun ty ->
            match sort_of_type_expr ~lift ~env dtenv ty with
            | Sort.SVar svar -> svar | _ -> failwith "sort_of_type_expr")
      in
      Sort.mk_poly svs @@ sort_of_type_expr ~lift ~env dtenv ty
    | Tconstr (p, args, _) ->
      let args = List.map args ~f:(sort_of_type_expr ~lift ~env dtenv) in
      (*print_endline @@ "Tconstr: (" ^ String.concat_map_list ~sep:"," args ~f:Term.str_of_sort ^ ") " ^ Path.name p;*)
      (try
         let _params, ty, _ = try Env.find_type_expansion p env with Stdlib.Not_found -> raise NoTypeExpansion in
         (*let params = List.map params ~f:(sort_of_type_expr ~lift ~env dtenv) in*)
         assert (List.is_empty args);
         let sort = sort_of_type_expr ~lift ~env dtenv ty in
         Debug.print @@ lazy
           (sprintf "[sort_of_type_expr.Tconstr] %s is locally instantiated to %s"
              (Path.name p) (Term.str_of_sort sort));
         sort
       with NoTypeExpansion -> Ast.Typeinf.sort_of_name dtenv (Path.name p) ~args)
    | Tvar None ->
      Sort.SVar (Svar (sprintf "s'%d" (Types.Transient_expr.repr ty).id))
    | Tvar (Some name) ->
      (try
         let p, _ = try Env.find_type_by_name (Longident.Lident name) env with Stdlib.Not_found -> raise NoTypeExpansion in
         let params, ty, _ = try Env.find_type_expansion p env with Stdlib.Not_found -> raise NoTypeExpansion in
         assert (List.is_empty params)(*ToDo*);
         let sort = sort_of_type_expr ~lift ~env dtenv ty in
         Debug.print @@ lazy
           (sprintf "[sort_of_type_expr.Tvar] %s is locally instantiated to %s"
              (Path.name p) (Term.str_of_sort sort));
         sort
       with NoTypeExpansion -> Sort.SVar (Svar name))
    | Tarrow (Nolabel, te1, te2, _) ->
      if lift then
        Sort.SArrow
          (sort_of_type_expr ~lift dtenv ~env te1,
           (Sort.mk_fresh_empty_open_opsig (),
            sort_of_type_expr ~lift dtenv ~env te2,
            Sort.mk_fresh_evar ()))
      else
        Sort.mk_arrow
          (sort_of_type_expr ~lift dtenv ~env te1)
          (sort_of_type_expr ~lift dtenv ~env te2)
    | Tarrow ((Labelled _ | Optional _), _, _, _) ->
      failwith @@ "unsupported type expr: tarrow " ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Ttuple elems ->
      T_tuple.STuple (List.map elems ~f:(sort_of_type_expr ~lift ~env dtenv))
    | Tobject _ ->
      failwith @@ "unsupported type expr: tobject " ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Tfield _ ->
      failwith @@ "unsupported type expr: tfiled " ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Tnil ->
      failwith @@ "unsupported type expr: tnil " ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Tsubst _ ->
      failwith @@ "unsupported type expr: tsubst " ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Tvariant _ ->
      failwith @@ "unsupported type expr: tvariant " ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Tunivar _ ->
      failwith @@ "unsupported type expr: tunivar " ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Tpackage _ ->
      failwith @@ "unsupported type expr: tpackage " ^ str_of_stdbuf ty ~f:Printtyp.type_expr
  let sort_of_expr ?(lift = false) dtenv expr =
    sort_of_type_expr ~lift dtenv ~env:expr.exp_env expr.exp_type

  let rec pattern_of dtenv (pat:Typedtree.pattern) : Ast.Pattern.t =
    let sort = sort_of_type_expr dtenv ~env:pat.pat_env pat.pat_type in
    match pat.pat_desc with
    | Tpat_var (name, _) ->
      Ast.Pattern.PVar (Tvar (Ident.name name), sort)
    | Tpat_any ->
      Ast.Pattern.PAny sort
    | Tpat_tuple pats ->
      Ast.Pattern.PTuple (List.map pats ~f:(pattern_of dtenv))
    | Tpat_alias (_pat'(*ToDo*), name, _) ->
      Ast.Pattern.PVar (Tvar (Ident.name name), sort)
    (* ToDo: pattern_of dtenv pat'*)
    (*failwith ((Ast.Pattern.str_of @@ pattern_of dtenv pat') ^ " and " ^ Ident.name name)*)
    | Tpat_constant _ ->
      failwith "[pattern_of] unsupported pattern: Tpat_constant"
    | Tpat_construct (_, cd, pats, _) -> begin
        match sort with
        | T_dt.SDT dt ->
          let pats = List.map pats ~f:(pattern_of dtenv) in
          Ast.Pattern.PCons (dt, cd.cstr_name, pats)
        | sort ->
          failwith @@ sprintf "[pattern_of] %s needs to be a datatype" @@
          Term.str_of_sort sort
      end
    | Tpat_variant (_, _, _) ->
      failwith "[pattern_of] unsupported pattern: Tpat_variant"
    | Tpat_record (_, _) ->
      failwith "[pattern_of] unsupported pattern: Tpat_record"
    | Tpat_array _ ->
      failwith "[pattern_of] unsupported pattern: Tpat_array"
    | Tpat_lazy _ ->
      failwith "[pattern_of] unsupported pattern: Tpat_lazy"
    | Tpat_or (_, _, _) ->
      failwith "[pattern_of] unsupported pattern: Tpat_or"

  let rec value_case_of case general_pat =
    match general_pat.pat_desc with
    | Tpat_value arg -> [ { case with c_lhs = (arg :> Typedtree.pattern) } ]
    | Tpat_or (pat1, pat2, None) -> value_case_of case pat1 @ value_case_of case pat2
    | Tpat_or (_, _, Some _) -> failwith "[value_case_of] or pattern not supported"
    | Tpat_exception _ -> failwith "[value_case_of] exception pattern not supported"

  let is_pure = function
    | Texp_ident _ -> true
    | Texp_constant _ -> true
    | Texp_function _ -> true
    | Texp_construct (_, _cd, []) -> true
    | _ -> false(*ToDo*)
  let is_fun = function
    | Texp_function _ -> true
    | _ -> false(*ToDo*)

  let is_raise s = String.(=) "raise" s || String.(=) "Stdlib.raise" s
  let is_shift0 = String.(=) "shift0"
  let is_shift = String.(=) "shift"
  let is_reset = String.(=) "reset"
  let is_perform = String.(=) "perform"
  let is_try_with = String.(=) "try_with"
  let is_match_with = String.(=) "match_with"
  let is_continue = String.(=) "continue"
  let is_keyword s =
    is_raise s || is_shift0 s || is_shift s || is_reset s
    || is_perform s || is_match_with s || is_try_with s || is_continue s
  let is_interpreted name =
    Ast.Rtype.is_fsym name || Ast.Rtype.is_psym name ||
    Ast.Rtype.is_unop name || Ast.Rtype.is_binop name

  let find_comp_attrs ?config ?renv ?dtenv ~attr_name attrs =
    let content_of attr =
      match attr.Parsetree.attr_payload with
      | Parsetree.PStr ps ->
        let ts, _, _, _, _ = Typemod.type_structure (Compmisc.initial_env ()) ps in
        begin match (List.hd_exn @@ List.rev ts.str_items).str_desc with
          | Tstr_eval (expr, _) ->
            begin match expr.exp_desc with
              | Texp_constant (Const_string (str, _, _)) -> str
              | _ -> failwith "unsupported"
            end
          | _ -> failwith "unsupported"
        end
      | _ -> failwith "unsupported"
    in
    let attr_opt =
      List.find attrs ~f:(fun attr -> Stdlib.(attr.Parsetree.attr_name.txt = attr_name))
    in
    match attr_opt with
    | Some attr ->
      let content = content_of attr in
      (match config with Some config -> Ast.Rtype.cgen_config := config | None -> ());
      (match renv with Some renv -> Ast.Rtype.renv_ref := renv | None -> ());
      (match dtenv with Some dtenv -> set_dtenv dtenv | None -> ());
      let c = Ast.RtypeParser.comp_ty Ast.RtypeLexer.token @@ Lexing.from_string content in
      Some c
    | None -> None
  let find_val_attrs ?config ?renv ?dtenv ~attr_name attrs =
    (* using RtypeParser.comp_ty insted of RtypeParser.val_ty
       because menher says "Warning: symbol val_ty is never accepted." *)
    match find_comp_attrs ?config ?renv ?dtenv ~attr_name attrs with
    | None -> None
    | Some (o, s, _, e) ->
      if ALMap.is_empty o && Ast.Rtype.is_pure_cont e then Some s
      else failwith "value type annotation expected"

  let rec fold_expr ~f dtenv senv expr (opsig, sort, cont) =
    let call_fold = fold_expr ~f dtenv in
    let mk_either ?(opsig = Sort.mk_fresh_empty_open_opsig ()) senv e =
      let sort = sort_of_expr ~lift:true dtenv e in
      match e.exp_desc with
      | Texp_ident (p, _, _)
        when Fn.non is_interpreted @@ Path.name p &&
             Fn.non is_keyword @@ Path.name p -> (* if [Path.name p] is a variable *)
        let econstrs, oconstrs, _next = call_fold senv e (Sort.empty_closed_opsig, sort, Sort.Pure) in
        econstrs, oconstrs, Second (Ast.Ident.Tvar (Path.name p), sort)
      | _ ->
        let evar = Sort.mk_fresh_evar () in
        let econstrs, oconstrs, next = call_fold senv e (opsig, sort, evar) in
        econstrs, oconstrs, First (is_pure e.exp_desc, next, sort, evar)
    in
    Debug.print @@ lazy
      (sprintf "[fold_expr] %s : %s" (str_of_expr expr) (Term.str_of_triple (opsig, sort, cont)));

    let attrs = expr.exp_attributes in
    let c_annot_MB_opt = find_comp_attrs ~dtenv ~attr_name:"annot_MB" attrs in
    let c_annot_opt = find_comp_attrs ~dtenv ~attr_name:"annot" attrs in
    let rty_annotated =
      List.exists attrs ~f:(fun attr -> Stdlib.(attr.attr_name.txt = "annot_rty"))
      || Option.is_some c_annot_opt
    in
    match c_annot_MB_opt, c_annot_opt with
    | Some c, _ | None, Some c ->
      let o, s, e = Ast.Rtype.full_sort_of_comp c in
      let _(*ToDo*), econstrs_annot, oconstrs_annot =
        Ast.Typeinf.subeff Map.Poly.empty (o, s, e) (opsig, sort, cont) in
      let econstrs, oconstrs, next =
        call_fold senv {expr with exp_attributes = [](*todo*)} (o, s, e)
      in
      Set.union econstrs_annot econstrs,
      Set.union oconstrs_annot oconstrs,
      if rty_annotated then f#f_annot (attrs, next) else next
    | None, None ->
      if rty_annotated then
        let econstrs, oconstrs, next =
          call_fold senv {expr with exp_attributes = [](*todo*)} (opsig, sort, cont) in
        econstrs, oconstrs, f#f_annot (attrs, next)
      else begin
        match expr.exp_desc with
        | Texp_ident (p, _, ty) ->
          let name = Path.name p in
          let _(*ToDo*), econstrs, oconstrs =
            let x_sort =
              match Map.Poly.find senv (Ast.Ident.Tvar name) with
              | Some x_sort ->
                (*print_endline @@ "[env] " ^ name ^ " : " ^ Term.str_of_sort x_sort;*)
                x_sort
              | None ->
                let sort =
                  Ast.Typeinf.generalize Map.Poly.empty(* any type variable that occur in ty.val_type must be alpha-renamed to avoid a conflict *) @@
                  sort_of_type_expr dtenv ~env:expr.exp_env ty.val_type
                in
                (*print_endline @@ "[ocaml] " ^ name ^ " : " ^ Term.str_of_sort sort;
                print_endline @@ "senv: " ^ str_of_sort_env_map Term.str_of_sort senv;*)
                sort
                (*failwith @@ sprintf "[fold_expr] %s not found" name*)
            in
            Ast.Typeinf.subeff Map.Poly.empty
              (Sort.empty_closed_opsig, x_sort, Sort.Pure) (opsig, sort, cont)
          in
          econstrs, oconstrs,
          if is_interpreted name then
            f#f_const @@ Term.mk_var (Ast.Ident.Tvar name) sort
          else if is_keyword name then
            failwith @@ "[fold_expr] " ^ name ^ " cannot be used as an identifier"
          else
            f#f_var (Ast.Ident.Tvar name, sort)
        | Texp_apply (e, es) when match e.exp_desc with
            Texp_ident (p, _, _) -> is_shift0 @@ Path.name p | _ -> false -> begin
            match es with
            | (_, Some e') :: [] ->
              (match e'.exp_desc with
               | Texp_function func ->
                 (match func.cases with
                  | [case] -> begin
                      match sort_of_type_expr ~lift:true dtenv ~env:case.c_lhs.pat_env case.c_lhs.pat_type with
                      | Sort.SArrow (x_sort1(* the sort of the shift0 exp *), (ovar1, x_sort2, evar1)) ->
                        let x_sort = Sort.SArrow (x_sort1, (ovar1, x_sort2, evar1)) in
                        let senv', x_opt =
                          match case.c_lhs.pat_desc with
                          | Tpat_var (name, _) ->
                            Map.Poly.set senv ~key:(Tvar (Ident.name name)) ~data:x_sort,
                            Some (Ast.Ident.Tvar (Ident.name name))
                          | Tpat_any -> senv, None
                          | _ -> failwith "shift0 @ 1"
                        in
                        let ovar2 = Sort.mk_fresh_empty_open_opsig () in
                        let sort2 = sort_of_expr ~lift:true dtenv case.c_rhs in
                        let evar2 = Sort.mk_fresh_evar () in
                        let econstrs2, oconstrs2, next2 =
                          call_fold senv' case.c_rhs (ovar2, sort2, evar2)
                        in
                        Set.add econstrs2
                          ([Sort.Eff (ovar1, x_sort2, evar1, ovar2, sort2, evar2)],
                           cont),
                        oconstrs2,
                        f#f_shift0 (x_opt, x_sort) (next2, ovar2, sort2, evar2)
                      | sort -> failwith @@ "shift0 @ 2: " ^ Term.str_of_sort sort
                    end
                  | _ -> failwith "shift0 @ 3")
               | _ -> failwith "shift0 @ 4")
            | e' :: es' ->
              call_fold senv
                ({ expr(*ToDo*) with
                   exp_desc = Texp_apply ({ expr(*ToDo*) with exp_desc = Texp_apply (e, [e']) }, es') })
                (opsig, sort, cont)
            | _ -> failwith "shift0 @ 5"
          end
        | Texp_apply (e, es) when match e.exp_desc with
            Texp_ident (p, _, _) -> is_shift @@ Path.name p | _ -> false -> begin
            match es with
            | (_, Some e') :: [] ->
              (match e'.exp_desc with
               | Texp_function func ->
                 (match func.cases with
                  | [case] -> begin
                      match sort_of_type_expr ~lift:true dtenv ~env:case.c_lhs.pat_env
                              case.c_lhs.pat_type with
                      | Sort.SArrow (x_sort1(* the sort of the shift exp *),
                                     (ovar1, x_sort2, evar1)) ->
                        let x_sort = Sort.SArrow (x_sort1, (ovar1, x_sort2, evar1)) in
                        let senv', x_opt =
                          match case.c_lhs.pat_desc with
                          | Tpat_var (name, _) ->
                            Map.Poly.set senv ~key:(Tvar (Ident.name name)) ~data:x_sort,
                            Some (Ast.Ident.Tvar (Ident.name name))
                          | Tpat_any -> senv, None
                          | _ -> failwith "shift @ 1"
                        in
                        (* type inference for shift (but shift0) introduces fresh type variables! *)
                        let sort_reset = Sort.mk_fresh_svar () in
                        let ovar2 = Sort.mk_fresh_empty_open_opsig () in
                        let sort2 = sort_of_expr ~lift:true dtenv case.c_rhs in
                        let evar2 = Sort.mk_fresh_evar () in
                        let econstrs1, oconstrs1, next1 =
                          call_fold senv' case.c_rhs
                            (Sort.empty_closed_opsig, sort2,
                             Sort.Eff (Sort.empty_closed_opsig, sort2, Sort.Pure,
                                       ovar2, sort_reset, evar2))
                        in
                        let next2 = f#f_reset (next1, sort2) in
                        Set.add econstrs1
                          ([Sort.Eff (ovar1, x_sort2, evar1, ovar2, sort_reset, evar2)],
                           cont),
                        oconstrs1,
                        f#f_shift0 (x_opt, x_sort) (next2, ovar2, sort2, evar2)
                      | sort -> failwith @@ "shift @ 2: " ^ Term.str_of_sort sort
                    end
                  | _ -> failwith "shift @ 3")
               | _ -> failwith "shift @ 4")
            | e' :: es' ->
              call_fold senv
                ({ expr(*ToDo*) with
                   exp_desc = Texp_apply ({ expr(*ToDo*) with exp_desc = Texp_apply (e, [e']) }, es') })
                (opsig, sort, cont)
            | _ -> failwith "shift @ 5"
          end
        | Texp_apply (e, es) when match e.exp_desc with
            Texp_ident (p, _, _) -> is_reset @@ Path.name p | _ -> false -> begin
            match es with
            | (_, Some e') :: [] ->
              (match e'.exp_desc with
               | Texp_function func ->
                 (match func.cases with
                  | [case] ->
                    let _ =
                      match case.c_lhs.pat_desc with
                      | Tpat_construct (_, cd, [], _) when Stdlib.(cd.cstr_name = "()") -> ()
                      | Tpat_any -> ()
                      | _ -> failwith "reset @ 1"
                    in
                    let sort1 = sort_of_expr ~lift:true dtenv case.c_rhs in
                    let econstrs1, oconstrs1, next1 =
                      call_fold senv case.c_rhs
                        (Sort.empty_closed_opsig,
                         sort1,
                         Sort.Eff (Sort.mk_fresh_empty_open_opsig ()(*ToDo*), sort1, Sort.Pure,
                                   opsig, sort, cont))
                    in
                    econstrs1, oconstrs1, f#f_reset (next1, sort1)
                  | _ -> failwith "reset @ 2")
               | _ -> failwith "reset @ 3")
            | e' :: es' ->
              call_fold senv
                ({ expr(*ToDo*) with
                   exp_desc = Texp_apply ({ expr(*ToDo*) with exp_desc = Texp_apply (e, [e']) }, es') })
                (opsig, sort, cont)
            | _ -> failwith "reset @ 4"
          end
        | Texp_apply (e, es) when match e.exp_desc with
            Texp_ident (p, _, _) -> is_perform @@ Path.name p || is_raise @@ Path.name p | _ -> false -> begin
            match es with
            | [(_, Some e')] ->
              begin match e'.exp_desc with
                | Texp_construct (_, cd, args) ->
                  let name = cd.cstr_name in
                  let econstrss, oconstrss, nexts_either =
                    List.unzip3 @@ List.map args ~f:(mk_either ~opsig senv)
                  in
                  let sort_args = List.map nexts_either ~f:(function First (_, _, sort, _) | Second (_, sort) -> sort) in
                  let evar_args = List.filter_map nexts_either ~f:(function First (_, _, _, evar) -> Some evar | Second (_, _) -> None) in

                  let ovar1 = Sort.mk_fresh_empty_open_opsig () in
                  let ovar2 = Sort.mk_fresh_empty_open_opsig () in
                  let svar1 = Sort.mk_fresh_svar () in
                  let svar2 = Sort.mk_fresh_svar () in
                  let evar1 = Sort.EVar (Ast.Ident.mk_fresh_evar ()) in
                  let evar2 = Sort.EVar (Ast.Ident.mk_fresh_evar ()) in
                  let sort_op_applied =
                    let sort_k = Sort.SArrow (sort, (ovar1, svar1, evar1)) in
                    Sort.SArrow (sort_k, (ovar2, svar2, evar2))
                  in
                  let opsig_op =
                    let rvar = Ast.Ident.mk_fresh_rvar () in
                    let sort_op = Sort.mk_fun @@ sort_args @ [sort_op_applied] in
                    Sort.OpSig (ALMap.singleton name sort_op, Some rvar)
                  in
                  let eff_op = Sort.Eff (ovar1, svar1, evar1, ovar2, svar2, evar2) in

                  Set.Poly.union_list @@
                  Set.Poly.singleton (List.rev (eff_op :: evar_args), cont) :: econstrss,

                  Set.Poly.union_list @@
                  Set.Poly.singleton (opsig, opsig_op) :: oconstrss,

                  f#f_perform e.exp_attributes name sort_op_applied nexts_either
                | _ -> failwith "perform"
              end
            | e' :: es' ->
              call_fold senv
                ({ expr(*ToDo*) with
                   exp_desc = Texp_apply ({ expr(*ToDo*) with exp_desc = Texp_apply (e, [e']) }, es') })
                (opsig, sort, cont)
            | _ -> failwith "perform"
          end
        | Texp_apply (e, es) when match e.exp_desc with
            Texp_ident (p, _, _) -> is_try_with @@ Path.name p || is_match_with @@ Path.name p | _ -> false -> begin
            match es with
            | [(_, Some e_body_fun); (_, Some e_body_arg); (_, Some e_handler)] ->
              let e_retc_opt, e_exnc_opt, e_effc =
                match e_handler.exp_desc with
                | Texp_record record ->
                  let expr_of label_name =
                    match Array.find record.fields ~f:(fun (l, _) -> Stdlib.(l.lbl_name = label_name)) with
                    | Some (_, Overridden (_, e)) -> e
                    | _ -> failwith "handling @ 1"
                  in
                  begin match record.fields with
                    | [| _ |] -> None, None, expr_of "effc"
                    | [| _;_;_ |] -> Some (expr_of "retc"), Some (expr_of "exnc"), expr_of "effc"
                    | _ -> failwith "handling @ 2"
                  end
                | _ -> failwith "handling @ 3"
              in

              (* effc *)
              let econstrss_op, oconstrss_op, nexts_op, op_names, sorts_op, clauses_op =
                let case =
                  match e_effc.exp_desc with
                  | Texp_function {cases = [case]; _} -> case
                  | _ -> failwith "handling @ eff1"
                in
                let senv' =
                  let s_pat_op = sort_of_type_expr ~lift:true dtenv ~env:case.c_lhs.pat_env case.c_lhs.pat_type in
                  let pat = pattern_of dtenv case.c_lhs in
                  let pat_senv = Ast.Pattern.senv_of pat s_pat_op in
                  Map.update_with(*shadowing*) senv pat_senv
                in
                match case.c_rhs.exp_desc with
                | Texp_match (e_op, cases, _) ->
                  let sort_op = sort_of_expr ~lift:true dtenv e_op in
                  List.unzip6 @@ List.map ~f:(fun case ->
                      let pat = pattern_of dtenv case.c_lhs in
                      let op_name, x_args, s_op_args =
                        match pat with
                        | Ast.Pattern.PCons (_dt, name, pat_args) ->
                          let x_args, s_args =
                            pat_args
                            |> List.map ~f:(function
                                | Ast.Pattern.PVar (x, sort) -> x, sort
                                | Ast.Pattern.PAny sort -> Ast.Ident.mk_fresh_tvar ()(*dummy*), sort
                                | _ -> failwith "handling @ eff2"
                              )
                            |> List.unzip
                          in
                          name, x_args, s_args
                        | _ -> failwith "handling @ eff3"
                      in
                      let s_annot_opts =
                        let attrss =
                          match case.c_lhs.pat_desc with
                          | Tpat_construct (_loc, _cd, pats, _) -> List.map ~f:(fun pat -> pat.pat_attributes) pats
                          | _ -> failwith "handling @ eff3-2"
                        in
                        List.map attrss ~f:(fun attrs ->
                            let t_annot_MB_opt = find_val_attrs ~dtenv ~attr_name:"annot_MB" attrs in
                            let t_annot_opt = find_val_attrs ~dtenv ~attr_name:"annot" attrs in
                            match t_annot_MB_opt, t_annot_opt with
                            | Some t, _ | None, Some t ->
                              let sort_annot = Ast.Rtype.sort_of_val t in
                              (* print_endline @@ sprintf "annot: %s" (Term.str_of_sort sort_annot); *)
                              Some sort_annot
                            | None, None -> None
                          )
                      in
                      let s_op_args = (* update with annotated sorts *)
                        List.map2_exn s_op_args s_annot_opts ~f:(fun s_op_arg s_annot_opt ->
                            Option.value ~default:s_op_arg s_annot_opt
                          )
                      in
                      let pat_senv =
                        let pat_senv = Ast.Pattern.senv_of pat sort_op in
                        let pat_senv_annot =
                          List.zip_exn x_args s_annot_opts
                          |> List.filter_map ~f:(fun (x, s_opt) -> Option.map s_opt ~f:(fun s -> (x, s)))
                          |> Map.Poly.of_alist_exn
                        in
                        Map.update_with pat_senv pat_senv_annot
                      in
                      let senv'' = Map.update_with(*shadowing*) senv' pat_senv in

                      match case.c_rhs.exp_desc with
                      | Texp_construct (_, {cstr_name = "Some"; _}, [{exp_desc = Texp_function {cases = [case]; _}; _}]) ->
                        let k_opt =
                          match pattern_of dtenv case.c_lhs with
                          | PVar (x, _) -> Some x
                          | PAny _ -> None
                          | _ -> failwith "handling @ eff4"
                        in
                        let s_fun_k =
                          let s_args =
                            match sort_of_type_expr ~lift:true ~env:case.c_lhs.pat_env dtenv case.c_lhs.pat_type with
                            | T_dt.SDT dt when Stdlib.(Datatype.name_of dt = "continuation") ->
                              Datatype.params_of dt
                            | _ -> failwith "handling @ eff7"
                          in
                          match s_args with
                          | [s_y; s_ans] ->
                            let evar = Sort.mk_fresh_evar () in
                            let ovar = Sort.mk_fresh_empty_open_opsig () in
                            Sort.SArrow (s_y, (ovar, s_ans, evar))
                          | _ -> failwith "handling @ eff8"
                        in
                        let senv''' =
                          match k_opt with
                          | Some k -> Map.Poly.add_exn ~key:k ~data:s_fun_k senv''
                          | None -> senv''
                        in

                        let e_clause = case.c_rhs in
                        let s_clause = sort_of_expr ~lift:true dtenv e_clause in
                        let evar = Sort.mk_fresh_evar () in
                        let ovar = Sort.mk_fresh_empty_open_opsig () in
                        let econstrs, oconstrs, next = call_fold senv''' e_clause (ovar, s_clause, evar) in
                        let sort_op = Sort.mk_fun @@ s_op_args @ [Sort.SArrow (s_fun_k, (ovar, s_clause, evar))] in
                        econstrs, oconstrs, next, op_name, sort_op, (x_args, s_op_args, k_opt, s_fun_k, (ovar, s_clause, evar))
                      | _ -> failwith "handling @ eff9"
                    ) @@
                  List.concat_map cases ~f:(fun case -> value_case_of case case.c_lhs)
                | _ -> failwith "handling @ eff10"
              in

              (* exnc *)
              let econstrss_exn, oconstrss_exn, nexts_exn, exn_names, sort_exns, clauses_exn =
                match e_exnc_opt with
                | None -> [], [], [], [], [], []
                | Some e_exnc ->
                  match e_exnc.exp_desc with
                  | Texp_function {cases; _} ->
                    List.unzip6 @@ List.map cases ~f:(fun case ->
                        let pat = pattern_of dtenv case.c_lhs in
                        let sort_pat =
                          sort_of_type_expr ~lift:true dtenv
                            ~env:case.c_lhs.pat_env case.c_lhs.pat_type
                        in
                        let pat_senv = Ast.Pattern.senv_of pat sort_pat in
                        let senv' = Map.update_with(*shadowing*) senv pat_senv in
                        let exn_name, x_args, s_op_args =
                          match pat with
                          | Ast.Pattern.PCons (_dt, name, pat_args) ->
                            let x_args, s_args =
                              pat_args
                              |> List.map ~f:(function
                                  | Ast.Pattern.PVar (x, sort) -> x, sort
                                  | Ast.Pattern.PAny sort -> Ast.Ident.mk_fresh_tvar ()(*dummy*), sort
                                  | _ -> failwith "handling @ exn1"
                                )
                              |> List.unzip
                            in
                            name, x_args, s_args
                          | Ast.Pattern.PAny _ | Ast.Pattern.PVar _ ->
                            failwith "write out all exception clauses explicitly"
                          | _ -> failwith "handling @ exn2"
                        in
                        let s_fun_k =
                          let svar1 = Sort.mk_fresh_svar () in
                          let svar2 = Sort.mk_fresh_svar () in
                          let evar = Sort.mk_fresh_evar () in
                          let ovar = Sort.mk_fresh_empty_open_opsig () in
                          Sort.SArrow (svar1, (ovar, svar2, evar))
                        in
                        let e_clause = case.c_rhs in
                        let s_clause = sort_of_expr ~lift:true dtenv e_clause in
                        let evar = Sort.mk_fresh_evar () in
                        let ovar = Sort.mk_fresh_empty_open_opsig () in
                        let econstrs, oconstrs, next = call_fold senv' e_clause (ovar, s_clause, evar) in
                        let sort_op = Sort.mk_fun @@ s_op_args @ [Sort.SArrow (s_fun_k, (ovar, s_clause, evar))] in
                        econstrs, oconstrs, next, exn_name, sort_op, (x_args, s_op_args, None, s_fun_k, (ovar, s_clause, evar))
                      )
                  | Texp_ident (p, _, ty) when is_raise @@ Path.name p ->
                    let sort_arg =
                      match sort_of_type_expr ~lift:true ~env:e_exnc.exp_env dtenv ty.val_type with
                      | Sort.SArrow (s, _) -> s
                      | _ -> failwith "handling @ exn3"
                    in
                    begin match sort_arg with
                      | T_dt.SDT _ ->
                        failwith "write out all exception clauses explicitly"
                      | Sort.SVar sv when Stdlib.(Ast.Ident.name_of_svar sv = "exn") ->
                        (* datatype [exn] is not in dtenv (i.e. [exn] is the build-in type)
                           and [raise] here is used as a dummy expression for [exnc] *)
                        [], [], [], [], [], []
                      | _ -> failwith @@ "handling @ exn4: " ^ Term.str_of_sort sort_arg
                    end
                  | _ -> failwith "handling @ exn5"
              in

              let econstrss, oconstrss, nexts, names, sorts, clauses =
                econstrss_op @ econstrss_exn,
                oconstrss_op @ oconstrss_exn,
                nexts_op @ nexts_exn,
                op_names @ exn_names,
                sorts_op @ sort_exns,
                clauses_op @ clauses_exn
              in
              let opsig_h = Sort.OpSig (ALMap.of_alist_exn @@ List.zip_exn names sorts, None) in

              let e_body =
                { e_body_fun with
                  exp_desc = Texp_apply (e_body_fun, [(Nolabel, Some e_body_arg)]);
                  exp_type = (*dummy*)
                    match Types.get_desc e_body_fun.exp_type with
                    | Types.Tarrow (_, _, ty_body, _) -> ty_body
                    | _ -> failwith "handling @ m1"
                }
              in
              let s_body =
                match sort_of_expr ~lift:true dtenv e_body_fun with
                | Sort.SArrow (_s_arg, (_o_body, s_body, _e_body)) -> s_body
                | _ -> failwith "handling @ m2"
              in

              (* retc *)
              let evar_retc = Sort.mk_fresh_evar () in
              let ovar_retc = Sort.mk_fresh_empty_open_opsig () in
              let econstrs_r, oconstrs_r, next_r, xr, sort_retc =
                match e_retc_opt with
                | None ->
                  let xr = Ast.Ident.mk_fresh_tvar () in
                  let _(*ToDo*), econstrs, oconstrs =
                    Ast.Typeinf.subeff Map.Poly.empty
                      (Sort.mk_fresh_empty_open_opsig (), s_body, Sort.Pure)
                      (ovar_retc, s_body, evar_retc)
                  in
                  econstrs, oconstrs, f#f_var (xr, s_body), xr, s_body
                | Some e_retc ->
                  begin match e_retc.exp_desc with
                    | Texp_function func ->
                      begin match func.cases with
                        | [case] ->
                          let sort_retc = sort_of_expr ~lift:true dtenv case.c_rhs in
                          let s_pat = sort_of_type_expr ~lift:true dtenv ~env:case.c_lhs.pat_env case.c_lhs.pat_type in
                          let pat = pattern_of dtenv case.c_lhs in
                          let pat_senv = Ast.Pattern.senv_of pat s_pat in
                          let senv' = Map.update_with(*shadowing*) senv pat_senv in
                          let econstrs, oconstrs, next =
                            call_fold senv' case.c_rhs (ovar_retc, sort_retc, evar_retc)
                          in
                          let xr =
                            match pat with
                            | PVar (xr, _) -> xr
                            | PAny _ -> Ast.Ident.mk_fresh_tvar ()(*dummy*)
                            | _ -> failwith "handling @ ret1"
                          in
                          econstrs, oconstrs, next, xr, sort_retc
                        | _ -> failwith "handling @ ret2"
                      end
                    | _ -> failwith "handling @ ret3"
                  end
              in

              let eff_body = Sort.Eff (ovar_retc, sort_retc, evar_retc, opsig, sort, cont) in
              let econstrs_b, oconstrs_b, next_b = call_fold senv e_body (opsig_h, s_body, eff_body) in

              Set.Poly.union_list @@ econstrs_b :: econstrs_r :: econstrss,
              Set.Poly.union_list @@ oconstrs_b :: oconstrs_r :: oconstrss,
              f#f_handling (next_b, s_body) (next_r, xr, ovar_retc, sort_retc, evar_retc) names nexts clauses
            | e1' :: e2' :: e3' :: es' ->
              call_fold senv
                ({ expr(*ToDo*) with
                   exp_desc = Texp_apply ({ expr(*ToDo*) with exp_desc = Texp_apply (e, [e1'; e2'; e3']) }, es') })
                (opsig, sort, cont)
            | _ -> failwith "handling @ l1"
          end
        | Texp_apply (e, es) when match e.exp_desc with
            Texp_ident (p, _, _) -> is_continue @@ Path.name p | _ -> false -> begin
            match es with
            | [(_, Some e_k)] ->
              begin match sort_of_expr ~lift:true dtenv e_k with
                | T_dt.SDT dt when Stdlib.(Datatype.name_of dt = "continuation") ->
                  call_fold senv e_k (opsig, sort, cont)
                | _ -> failwith "continue"
              end
            | e' ::  es' ->
              call_fold senv
                ({ expr(*ToDo*) with
                   exp_desc = Texp_apply ({ expr(*ToDo*) with exp_desc = Texp_apply (e, [e']) }, es') })
                (opsig, sort, cont)
            | _ -> failwith "continue"
          end
        | Texp_apply (e1, es) ->
          let econstrss, oconstrss, nexts_either =
            List.unzip3 @@ List.map ~f:(mk_either ~opsig senv) @@
            List.map es ~f:(function
                | (_label, Some e) -> e
                | (_label, None) -> failwith "default arg not supported")
          in
          let sort_args = List.map nexts_either ~f:(function First (_, _, sort, _) | Second (_, sort) -> sort) in
          let evar_args = List.filter_map nexts_either ~f:(function First (_, _, _, evar) -> Some evar | Second (_, _) -> None) in

          let _ovars', evars', sort_fun = Sort.of_args_ret ~opsig sort_args sort(*sort_of_expr dtenv e1*) in
          let evar1 = Sort.mk_fresh_evar () in
          let econstrs1, oconstrs1, next1 = call_fold senv e1 (opsig, sort_fun, evar1) in

          Set.Poly.union_list @@
          Set.Poly.singleton ((List.rev @@ evar1 :: evar_args) @ evars', cont) ::
          econstrs1 :: econstrss,

          Set.Poly.union_list @@ oconstrs1 :: oconstrss,

          f#f_apply (next1, evars', evar1) nexts_either
        | Texp_ifthenelse (e1, e2, Some e3) ->
          let sort1 = sort_of_expr ~lift:true dtenv e1 in
          let evar1 = Sort.mk_fresh_evar () in
          let econstrs1, oconstrs1, next1 = call_fold senv e1 (opsig, sort1, evar1) in

          let evar2 = Sort.mk_fresh_evar () in
          let econstrs2, oconstrs2, next2 = call_fold senv e2 (opsig, sort, evar2) in

          let evar3 = Sort.mk_fresh_evar () in
          let econstrs3, oconstrs3, next3 = call_fold senv e3 (opsig, sort, evar3) in

          Set.Poly.union_list
            [Set.Poly.of_list [([evar1; evar2], cont); ([evar1; evar3], cont)];
             econstrs1; econstrs2; econstrs3],
          Set.Poly.union_list
            [oconstrs1; oconstrs2; oconstrs3],
          f#f_ite (next1, evar1) (next2, evar2) @@ Some (next3, evar3)
        | Texp_ifthenelse (e1, e2, None) ->
          let sort1 = sort_of_expr ~lift:true dtenv e1 in
          let evar1 = Sort.mk_fresh_evar () in
          let econstrs1, oconstrs1, next1 = call_fold senv e1 (opsig, sort1, evar1) in

          let evar2 = Sort.mk_fresh_evar () in
          let econstrs2, oconstrs2, next2 = call_fold senv e2 (opsig, sort, evar2) in

          Set.Poly.union_list [Set.Poly.singleton ([evar1; evar2], cont); econstrs1; econstrs2],
          Set.Poly.union_list [oconstrs1; oconstrs2],
          f#f_ite (next1, evar1) (next2, evar2) None
        | Texp_constant Const_float r ->
          Set.Poly.singleton ([Sort.Pure], cont),
          Set.Poly.singleton (opsig, Sort.empty_closed_opsig),
          f#f_const @@ T_real.mk_real @@ Q.of_string r
        | Texp_constant Const_int i ->
          Set.Poly.singleton ([Sort.Pure], cont),
          Set.Poly.singleton (opsig, Sort.empty_closed_opsig),
          f#f_const @@ T_int.from_int i
        | Texp_constant Const_int32 i32 ->
          Set.Poly.singleton ([Sort.Pure], cont),
          Set.Poly.singleton (opsig, Sort.empty_closed_opsig),
          f#f_const @@ T_int.mk_int @@ Z.of_int32 i32
        | Texp_constant Const_int64 i64 ->
          Set.Poly.singleton ([Sort.Pure], cont),
          Set.Poly.singleton (opsig, Sort.empty_closed_opsig),
          f#f_const @@ T_int.mk_int @@ Z.of_int64 i64
        | Texp_constant Const_nativeint inative ->
          Set.Poly.singleton ([Sort.Pure], cont),
          Set.Poly.singleton (opsig, Sort.empty_closed_opsig),
          f#f_const @@ T_int.mk_int @@ Z.of_nativeint inative
        | Texp_constant Const_string (str, _, None) ->
          Set.Poly.singleton ([Sort.Pure], cont),
          Set.Poly.singleton (opsig, Sort.empty_closed_opsig),
          f#f_const @@ T_string.make str
        | Texp_constant Const_string (str, _, Some _) -> (* {...|...|...} *)
          Set.Poly.singleton ([Sort.Pure], cont),
          Set.Poly.singleton (opsig, Sort.empty_closed_opsig),
          f#f_const @@ T_string.make str
        | Texp_constant Const_char _ ->
          failwith @@ "[fold_expr] char is unsupported: " ^ str_of_expr expr
        | Texp_assert (e, _) ->
          let evar1 = Sort.mk_fresh_evar () in
          let econstrs, oconstrs, next =
            match e.exp_desc with
            | Texp_construct (_, cd, []) when String.(cd.cstr_name = "false") ->
              Set.Poly.empty, Set.Poly.empty, None
            | _ ->
              let econstrs, oconstrs, next =
                call_fold senv e (opsig, sort_of_expr ~lift:true dtenv e, evar1)
              in
              econstrs, oconstrs, Some next
          in
          Set.Poly.union_list [Set.Poly.singleton ([evar1], cont); econstrs],
          oconstrs,
          f#f_assert (next, evar1)
        | Texp_let (rec_flag, vbs, e2) ->
          let defs =
            List.map vbs ~f:(fun vb ->
                let pat = pattern_of dtenv vb.vb_pat in
                let expr = vb.vb_expr in
                let attrs = vb.vb_attributes in
                let t_annot_MB_opt = find_val_attrs ~dtenv ~attr_name:"annot_MB" attrs in
                let t_annot_opt = find_val_attrs ~dtenv ~attr_name:"annot" attrs in
                let rty_annotated =
                  List.exists attrs ~f:(fun attr -> Stdlib.(attr.attr_name.txt = "annot_rty"))
                  || Option.is_some t_annot_opt
                in
                if rty_annotated then
                  failwith "rtype annotations on let-bindings are not supported"; (*todo*)
                let sort =
                  match t_annot_MB_opt, t_annot_opt with
                  | Some t, _ | None, Some t -> Ast.Rtype.sort_of_val t
                  | None, None -> sort_of_expr ~lift:true dtenv expr
                in
                let pat_senv = Ast.Pattern.senv_of pat sort in
                pat_senv, pat, expr, sort)
          in
          let pats, econstrss, oconstrss, pure1s, is_fun1s, next1s, sort1s, evar1s =
            let senv_bounds =
              match rec_flag with
              | Recursive ->
                let pat_senvs =
                  List.map defs(* assume distinct *) ~f:(fun (pat_senv, _, _, _) -> pat_senv)
                in
                Map.update_with_list(*shadowing*) @@ senv :: pat_senvs
              | Nonrecursive -> senv
            in
            List.unzip8 @@ List.map defs ~f:(fun (_, pat, expr, sort) ->
                let evar = Sort.mk_fresh_evar () in
                let econstrs, oconstrs, next = call_fold senv_bounds expr (opsig, sort, evar) in
                pat, econstrs, oconstrs,
                is_pure expr.exp_desc, is_fun expr.exp_desc,
                next, sort, evar)
          in
          let senv_body =
            let pat_senvs =
              List.map defs(* assume distinct *) ~f:(fun (pat_senv, _, _, _) -> pat_senv)
            in
            let generalizable =
              List.for_all pure1s ~f:Fn.id &&
              List.for_all pats ~f:(fun pat -> Sort.is_arrow @@ Ast.Pattern.sort_of pat)
            in
            Map.update_with_list(*shadowing*) @@
            senv ::
            if generalizable then
              List.map pat_senvs ~f:(Map.Poly.map ~f:(Ast.Typeinf.generalize senv))
            else pat_senvs
          in
          let evar2 = Sort.mk_fresh_evar () in
          let econstrs, oconstrs, next = call_fold senv_body e2 (opsig, sort, evar2) in
          Set.Poly.union_list @@
          Set.Poly.singleton (evar1s @ [evar2], cont) :: econstrs :: econstrss,
          Set.Poly.union_list @@ oconstrs :: oconstrss,
          f#f_let_and (Stdlib.(rec_flag = Recursive)) pats
            (pure1s, is_fun1s, next1s, sort1s, evar1s) (next, evar2)
        | Texp_function func ->
          let sarg, (ovar, sret, evar) = match sort with
            | Sort.SArrow (sarg, (ovar, sret, evar)) -> sarg, (ovar, sret, evar)
            | _ -> failwith @@ "function type expected but " ^ Term.str_of_sort sort
          in
          let pats, econstrss, oconstrss, nexts, evars =
            List.unzip5 @@ List.map func.cases ~f:(fun case ->
                let sarg, econstrs_annot, oconstrs_annot = (* constr on MB type annotations on arguments *)
                  let attrs = case.c_lhs.pat_attributes in
                  let t_annot_MB_opt = find_val_attrs ~dtenv ~attr_name:"annot_MB" attrs in
                  let t_annot_opt = find_val_attrs ~dtenv ~attr_name:"annot" attrs in
                  match t_annot_MB_opt, t_annot_opt with
                  | Some t, _ | None, Some t ->
                    let sort_annot = Ast.Rtype.sort_of_val t in
                    (* print_endline @@ sprintf "annot: %s = %s" (Term.str_of_sort sort_annot) (Term.str_of_sort sarg); *)
                    let eqtype s1 s2 =
                      let _map, econstrs, oconstrs =
                        Ast.Typeinf.subtype Map.Poly.empty s1 s2 in
                      let _map, econstrs', oconstrs' =
                        Ast.Typeinf.subtype Map.Poly.empty s2 s1 in
                      Set.union econstrs econstrs', Set.union oconstrs oconstrs'
                    in
                    let econstrs, oconstrs = eqtype sarg sort_annot in
                    sort_annot, econstrs, oconstrs
                  | None, None -> sarg, Set.Poly.empty, Set.Poly.empty
                in
                let pat = pattern_of dtenv case.c_lhs in
                (*print_endline @@ Term.str_of_sort sarg;*)
                let pat_senv = Ast.Pattern.senv_of pat sarg in
                (*print_endline @@ str_of_sort_env_map Term.str_of_sort pat_senv;*)
                let senv' = Map.update_with(*shadowing*) senv pat_senv in
                let econstrs, oconstrs, next = call_fold senv' case.c_rhs (ovar, sret, evar) in
                pat, Set.union econstrs_annot econstrs, Set.union oconstrs_annot oconstrs, next, evar)
          in
          let t_annot_rty_opt = (* refinement type annotations on arguments *)
            match func.cases with
            | [case] ->
              let attrs = case.c_lhs.pat_attributes in
              let t_annot_rty_opt = find_val_attrs ~dtenv ~attr_name:"annot_rty" attrs in
              let t_annot_opt = find_val_attrs ~dtenv ~attr_name:"annot" attrs in
              begin match t_annot_rty_opt, t_annot_opt with
                | Some t, _ | None, Some t -> Some t
                | None, None -> None
              end
            | _ -> None (*todo*)
          in
          Set.Poly.union_list @@
          Set.Poly.singleton ([Sort.Pure], cont) :: econstrss,
          Set.Poly.union_list @@
          Set.Poly.singleton (opsig, Sort.empty_closed_opsig) :: oconstrss,
          f#f_function pats t_annot_rty_opt (nexts, evars)
        | Texp_construct (_, cd, args) -> begin
            match cd.cstr_name with
            | "true" ->
              assert (List.is_empty args);
              Set.Poly.singleton ([Sort.Pure], cont),
              Set.Poly.singleton (opsig, Sort.empty_closed_opsig),
              f#f_const @@ T_bool.mk_true ()
            | "false" ->
              assert (List.is_empty args);
              Set.Poly.singleton ([Sort.Pure], cont),
              Set.Poly.singleton (opsig, Sort.empty_closed_opsig),
              f#f_const @@ T_bool.mk_false ()
            | name -> begin
                let econstrss, oconstrss, nexts_either =
                  List.unzip3 @@ List.map args ~f:(mk_either ~opsig senv)
                in
                let sort_args = List.map nexts_either ~f:(function First (_, _, sort, _) | Second (_, sort) -> sort) in
                let evars = List.filter_map nexts_either ~f:(function First (_, _, _, evar) -> Some evar | Second (_, _) -> None) in

                let sort_fun = (*assume its application never causes a temporal effect*)
                  Sort.mk_fun @@ sort_args @ [sort]
                in
                match sort with
                | T_dt.SDT dt ->
                  let sort_cons =
                    let svs =
                      Set.Poly.of_list @@ List.filter_map (Datatype.params_of dt) ~f:(function
                          | Sort.SVar svar -> Some svar | _ -> None)
                    in
                    Sort.mk_poly svs @@
                    Sort.mk_fun @@ Datatype.sorts_of_cons_name dt name @ [sort]
                  in
                  (*print_endline @@ sprintf "SDT: %s <: %s"
                    (Term.str_of_sort sort_cons) (Term.str_of_sort sort_fun);*)
                  let _map(*ToDo*), econstrs, oconstrs =
                    Ast.Typeinf.subtype Map.Poly.empty(*ToDo*) sort_cons sort_fun
                  in

                  Set.Poly.union_list @@
                  Set.Poly.singleton (List.rev evars, cont) :: econstrs :: econstrss,

                  Set.Poly.union_list @@ oconstrs :: oconstrss,

                  f#f_construct dt name nexts_either
                | T_dt.SUS(*ToDo*) (name, params) when Map.Poly.mem dtenv name ->
                  let dt =
                    match DTEnv.look_up_dt dtenv name with
                    | None -> failwith ""
                    | Some dt -> dt
                  in
                  let sort_cons =
                    let svs =
                      Set.Poly.of_list @@ List.filter_map params ~f:(function
                          | Sort.SVar svar -> Some svar | _ -> None)
                    in
                    Sort.mk_poly svs @@
                    Sort.mk_fun @@ Datatype.sorts_of_cons_name dt name @ [sort]
                  in
                  (*print_endline @@ sprintf "SUS: %s <: %s"
                    (Term.str_of_sort sort_cons) (Term.str_of_sort sort_fun);*)
                  let _map(*ToDo*), econstrs, oconstrs =
                    Ast.Typeinf.subtype Map.Poly.empty(*ToDo*) sort_cons sort_fun
                  in

                  Set.Poly.union_list @@
                  Set.Poly.singleton (List.rev evars, cont) :: econstrs :: econstrss,

                  Set.Poly.union_list @@ oconstrs :: oconstrss,

                  f#f_construct dt name nexts_either
                | T_dt.SUS _ -> (* reachable here? *)
                  let res =(*ToDo*)
                    f#f_var (Tvar name, sort_fun),
                    List.map sort_args ~f:(fun _ -> Sort.Pure),
                    Sort.Pure
                  in

                  Set.Poly.union_list @@
                  Set.Poly.singleton (List.rev evars, cont) :: econstrss,

                  Set.Poly.union_list oconstrss,

                  f#f_apply res nexts_either
                | _ -> failwith @@ "unknown construct: " ^ name
              end
          end
        | Texp_tuple es ->
          let econstrss, oconstrss, nexts_either =
            List.unzip3 @@ List.map es ~f:(mk_either ~opsig senv)
          in
          let evars = List.filter_map nexts_either ~f:(function First (_, _, _, evar) -> Some evar | Second (_, _) -> None) in

          Set.Poly.union_list @@
          Set.Poly.singleton (List.rev evars, cont) :: econstrss,

          Set.Poly.union_list oconstrss,

          f#f_tuple nexts_either
        | Texp_match (e1, cases, _) ->
          let econstrs, oconstrs, matched = mk_either ~opsig senv e1 in
          let sort1 = match matched with First (_, _, sort, _) | Second (_, sort) -> sort in
          let evar1 = match matched with First (_, _, _, evar) -> [evar] | Second (_, _) -> [] in
          let pats, econstrss, oconstrss, nexts, evars =
            List.unzip5 @@ List.map ~f:(fun case ->
                let evar = Sort.mk_fresh_evar () in
                let pat = pattern_of dtenv case.c_lhs in
                let pat_senv = Ast.Pattern.senv_of pat sort1 in
                let senv' = Map.update_with(*shadowing*) senv pat_senv in
                let econstrs, oconstrs, next = call_fold senv' case.c_rhs (opsig, sort, evar) in
                pat, econstrs, oconstrs, next, evar) @@
            List.concat_map cases ~f:(fun case -> value_case_of case case.c_lhs)
          in
          Set.Poly.union_list @@
          (Set.Poly.of_list @@ List.map evars ~f:(fun evar -> evar1 @ [evar], cont)) ::
          econstrs :: econstrss,
          Set.Poly.union_list @@ oconstrs :: oconstrss,
          f#f_match matched pats (nexts, evars)
        | Texp_sequence (e1, e2) ->
          let sort1 = sort_of_expr ~lift:true dtenv e1 in
          let evar1 = Sort.mk_fresh_evar () in
          let econstrs1, oconstrs1, next1 = call_fold senv e1 (opsig, sort1, evar1) in

          let evar2 = Sort.mk_fresh_evar () in
          let econstrs2, oconstrs2, next2 = call_fold senv e2 (opsig, sort, evar2) in

          Set.Poly.union_list
            [Set.Poly.singleton ([evar1; evar2], cont); econstrs1; econstrs2],
          Set.Poly.union_list [oconstrs1; oconstrs2],
          f#f_sequence (next1, sort1, evar1) (next2, evar2)
        | Texp_unreachable
        | Texp_try (_, _)
        | Texp_variant (_, _)
        | Texp_record _
        | Texp_field (_, _, _)
        | Texp_setfield (_, _, _, _)
        | Texp_array _
        | Texp_while (_, _)
        | Texp_for (_, _, _, _, _, _)
        | Texp_send (_, _)
        | Texp_new (_, _, _)
        | Texp_instvar (_, _, _)
        | Texp_setinstvar (_, _, _, _)
        | Texp_override (_, _)
        | Texp_letmodule (_, _, _, _, _)
        | Texp_letexception (_, _)
        | Texp_lazy _
        | Texp_object (_, _)
        | Texp_pack _
        | Texp_letop _
        | Texp_extension_constructor (_, _)
        | Texp_open (_, _) -> failwith @@ "[fold_expr] unsupported expr: " ^ str_of_expr expr
      end
end
