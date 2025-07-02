open Core
open Typedtree
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast.LogicOld

let rec bvs pat acc =
  match pat.pat_desc with
  | Tpat_var (id, _, _) -> id :: acc
  | Tpat_tuple pats | Tpat_array pats ->
      List.fold_left ~init:acc pats ~f:(fun a p -> bvs p a)
  | Tpat_construct (_, _, pats, _) ->
      List.fold_left ~init:acc pats ~f:(fun a p -> bvs p a)
  | Tpat_record (fields, _) ->
      List.fold_left ~init:acc fields ~f:(fun a (_, _, p) -> bvs p a)
  | Tpat_alias (p, id, _, _) -> bvs p (id :: acc)
  | Tpat_or (p1, p2, _) -> bvs p1 (bvs p2 acc)
  | _ -> acc

let occurs bound (target : Ident.t) (e : expression) =
  let found = ref false in
  let bound = ref bound in

  let add_pat_ids pat = bound := bvs pat !bound in

  let rec expr e =
    match e.exp_desc with
    | Texp_ident (Path.Pident id, _, _) ->
        if Ident.equal id target && not (List.exists ~f:(Ident.equal id) !bound)
        then found := true
    | Texp_let (_, vbs, body) ->
        List.iter ~f:(fun vb -> expr vb.vb_expr) vbs;
        List.iter ~f:(fun vb -> add_pat_ids vb.vb_pat) vbs;
        expr body
    | Texp_sequence (e1, e2) ->
        expr e1;
        expr e2
    | Texp_function (params, fb) -> (
        List.iter ~f:(fun { fp_param; _ } -> bound := fp_param :: !bound) params;
        match fb with
        | Tfunction_body body_expr -> expr body_expr
        | Tfunction_cases { cases; _ } ->
            List.iter cases ~f:(fun { c_lhs; c_rhs; _ } ->
                add_pat_ids c_lhs;
                expr c_rhs))
    | Texp_apply (f, args) ->
        expr f;
        List.iter ~f:(function _, Some a -> expr a | _ -> ()) args
    | Texp_ifthenelse (cond, then_expr, else_expr) ->
        expr cond;
        expr then_expr;
        Option.iter else_expr ~f:expr
    | _ -> ()
  in

  expr e;
  !found

module Config = struct
  type t = { verbose : bool; for_cps_trans : bool } [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid MBcgen Configuration (%s): %s" filename msg)
end

module Make (Config : Config.ConfigType) = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_module_name "MBcgen"

  type handler_type = ATPHandler | ExceptionHandler | ATMHandler

  let str_of_stdbuf ~f obj =
    Buffer.clear Format.stdbuf;
    f Format.str_formatter obj;
    Buffer.contents Format.stdbuf

  let str_of_typedtree_structure = str_of_stdbuf ~f:Printtyped.implementation
  let str_of_typedtree_interface = str_of_stdbuf ~f:Printtyped.interface
  let str_of_parse_structure = str_of_stdbuf ~f:Pprintast.structure

  let str_of_tenv =
    str_of_stdbuf ~f:(fun ppf_dump tenv ->
        Bytepackager.package_files ~ppf_dump tenv [] "")

  let rec str_of_expr expr =
    match expr.exp_desc with
    | Texp_ident (p, _, _) -> "Texp_ident " ^ Path.name p
    | Texp_constant _ -> "Texp_constant"
    | Texp_let _ -> "Texp_let"
    | Texp_function _ -> "Texp_function"
    | Texp_apply (e, es) ->
        "Texp_apply : " ^ String.concat ~sep:" "
        @@ str_of_expr e
           :: List.map es ~f:(function _, Some e -> str_of_expr e | _ -> "")
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

  let rec sort_of_core_type ?(rectyps = None) dtenv (ct : core_type) =
    match ct.ctyp_desc with
    | Ttyp_var name ->
        if false then print_endline @@ "Ttyp_var " ^ name;
        Sort.SVar (Svar name)
    | Ttyp_constr (ret_name, _, args) ->
        if false then print_endline @@ "Ttyp_constr " ^ Path.name ret_name;
        let args = List.map args ~f:(sort_of_core_type ~rectyps dtenv) in
        if false then List.iter args ~f:(Term.str_of_sort >> print_endline);
        Ast.Typeinf.sort_of_name ~rectyps dtenv ~args @@ Path.name ret_name
    | Ttyp_any -> failwith "[sort_of_core_type] Ttyp_any not supported"
    | Ttyp_arrow (Nolabel, ct1, ct2) ->
        Sort.mk_arrow
          (sort_of_core_type ~rectyps dtenv ct1)
          (sort_of_core_type ~rectyps dtenv ct2)
          ~cont:Sort.Pure
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
    | Ttyp_poly (_, _) -> failwith "[sort_of_core_type] Ttyp_poly not supported"
    | Ttyp_package _ ->
        failwith "[sort_of_core_type] Ttyp_package not supported"
    | Ttyp_open _ -> failwith "[sort_of_core_type] Ttyp_open not supported"

  exception NoTypeExpansion

  let ref_id = ref Map.Poly.empty
  let print_log = false

  let rec sort_of_type_expr ?(lift = false) ?(env = Env.empty) dtenv ty =
    let repr = Types.Transient_expr.repr ty in
    match repr.desc with
    | Tlink e -> sort_of_type_expr ~lift ~env dtenv e
    | Tpoly (ty, tys) ->
        let svs =
          Set.Poly.of_list
          @@ List.map tys ~f:(fun ty ->
                 match sort_of_type_expr ~lift ~env dtenv ty with
                 | Sort.SVar svar -> svar
                 | _ -> failwith "sort_of_type_expr")
        in
        Sort.mk_poly svs @@ sort_of_type_expr ~lift ~env dtenv ty
    | Tconstr (p, args, _) -> (
        let args = List.map args ~f:(sort_of_type_expr ~lift ~env dtenv) in
        if print_log then
          print_endline
          @@ sprintf "[sort_of_type_expr] Tconstr: (%s) %s"
               (String.concat_map_list ~sep:"," args ~f:Term.str_of_sort)
               (Path.name p);
        try
          let _params, ty, _ =
            try Env.find_type_expansion p env
            with Stdlib.Not_found -> raise NoTypeExpansion
          in
          (*let params = List.map params ~f:(sort_of_type_expr ~lift ~env dtenv) in*)
          assert (List.is_empty args);
          let sort = sort_of_type_expr ~lift ~env dtenv ty in
          Debug.print
          @@ lazy
               (sprintf
                  "[sort_of_type_expr.Tconstr] %s is locally instantiated to %s"
                  (Path.name p) (Term.str_of_sort sort));
          sort
        with NoTypeExpansion ->
          if false then
            print_endline
            @@ sprintf "[sort_of_type_expr.Tconstr] %s not found"
            @@ Path.name p;
          let sort =
            (*Term.subst_sorts_sort !ref_id
            @@*)
            Ast.Typeinf.sort_of_name dtenv (Path.name p) ~args
          in
          if false then
            print_endline
              (sprintf "[sort_of_type_expr.Tconstr] sort: %s"
                 (Term.str_of_sort sort));
          (*match sort with
          | T_dt.SDT dt ->
              let sort' = T_dt.SDT (Datatype.fresh_of dt) in
              if false then
                print_endline
                  (sprintf "[sort_of_type_expr.Tconstr] sort': %s"
                     (Term.str_of_sort sort'));
              sort'
          | _ ->*)
          sort)
    | Tvar None -> Sort.SVar (Ast.Ident.Svar (sprintf "s'%d" repr.id))
    | Tvar (Some name) -> (
        try
          let p, _ =
            try Env.find_type_by_name (Longident.Lident name) env
            with Stdlib.Not_found -> raise NoTypeExpansion
          in
          let params, ty, _ =
            try Env.find_type_expansion p env
            with Stdlib.Not_found -> raise NoTypeExpansion
          in
          assert (List.is_empty params) (*ToDo*);
          let sort = sort_of_type_expr ~lift ~env dtenv ty in
          Debug.print
          @@ lazy
               (sprintf
                  "[sort_of_type_expr.Tvar] %s is locally instantiated to %s"
                  (Path.name p) (Term.str_of_sort sort));
          sort
        with NoTypeExpansion -> Sort.SVar (Svar name))
    | Tarrow (Nolabel, te1, te2, _) ->
        if lift then
          Sort.SArrow
            ( sort_of_type_expr ~lift dtenv ~env te1,
              {
                op_sig = Sort.mk_fresh_empty_open_opsig ();
                val_type = sort_of_type_expr ~lift dtenv ~env te2;
                cont_eff = Sort.mk_fresh_evar ();
              } )
        else
          Sort.mk_arrow
            (sort_of_type_expr ~lift dtenv ~env te1)
            (sort_of_type_expr ~lift dtenv ~env te2)
            ~cont:Sort.Pure
    | Tarrow ((Labelled _ | Optional _), _, _, _) ->
        failwith @@ "unsupported type expr: tarrow "
        ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Ttuple elems ->
        T_tuple.STuple (List.map elems ~f:(sort_of_type_expr ~lift ~env dtenv))
    | Tobject _ ->
        failwith @@ "unsupported type expr: tobject "
        ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Tfield _ ->
        failwith @@ "unsupported type expr: tfiled "
        ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Tnil ->
        failwith @@ "unsupported type expr: tnil "
        ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Tsubst _ ->
        failwith @@ "unsupported type expr: tsubst "
        ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Tvariant _ ->
        failwith @@ "unsupported type expr: tvariant "
        ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Tunivar _ ->
        failwith @@ "unsupported type expr: tunivar "
        ^ str_of_stdbuf ty ~f:Printtyp.type_expr
    | Tpackage _ ->
        failwith @@ "unsupported type expr: tpackage "
        ^ str_of_stdbuf ty ~f:Printtyp.type_expr

  let sort_of_expr ?(lift = false) dtenv expr =
    sort_of_type_expr ~lift dtenv ~env:expr.exp_env expr.exp_type

  let rec pattern_of dtenv ?(sort = None) (pat : Typedtree.pattern) =
    let sort =
      match sort with
      | None -> sort_of_type_expr dtenv ~env:pat.pat_env pat.pat_type
      | Some s -> s
    in
    match (pat.pat_desc, sort) with
    | Tpat_var (name, _, _), _ -> Ast.Pattern.PVar (Tvar (Ident.name name), sort)
    | Tpat_any, _ -> Ast.Pattern.PAny sort
    | Tpat_tuple pats, T_tuple.STuple sorts ->
        Ast.Pattern.PTuple
          (List.map2_exn sorts pats ~f:(fun s ->
               pattern_of dtenv ~sort:(Some s)))
    | Tpat_tuple _, _ ->
        failwith
        @@ sprintf "[pattern_of] %s needs to be a tuple type"
        @@ Term.str_of_sort sort
    | Tpat_alias (_pat' (*ToDo*), name, _, _), _ ->
        Ast.Pattern.PVar (Tvar (Ident.name name), sort)
    (* ToDo: pattern_of dtenv pat' *)
    (*failwith ((Ast.Pattern.str_of @@ pattern_of dtenv pat') ^ " and " ^ Ident.name name)*)
    | Tpat_constant _, _ ->
        failwith "[pattern_of] unsupported pattern: Tpat_constant"
    | Tpat_construct (_, cd, pats, _), T_dt.SDT dt ->
        let sorts =
          match Datatype.look_up_cons dt cd.cstr_name with
          | Some cons -> Datatype.sorts_of_cons dt cons
          | _ -> failwith @@ "unknown cons :" ^ cd.cstr_name
        in
        Ast.Pattern.PCons
          ( dt,
            cd.cstr_name,
            List.map2_exn sorts pats ~f:(fun s ->
                pattern_of dtenv ~sort:(Some s)) )
    | Tpat_construct (_, _, _, _), _ ->
        failwith
        @@ sprintf "[pattern_of] %s needs to be a datatype"
        @@ Term.str_of_sort sort
    | Tpat_variant (_, _, _), _ ->
        failwith "[pattern_of] unsupported pattern: Tpat_variant"
    | Tpat_record (_, _), _ ->
        failwith "[pattern_of] unsupported pattern: Tpat_record"
    | Tpat_array _, _ -> failwith "[pattern_of] unsupported pattern: Tpat_array"
    | Tpat_lazy _, _ -> failwith "[pattern_of] unsupported pattern: Tpat_lazy"
    | Tpat_or (_, _, _), _ ->
        failwith "[pattern_of] unsupported pattern: Tpat_or"

  let rec value_case_of case general_pat =
    match general_pat.pat_desc with
    | Tpat_value arg -> [ { case with c_lhs = (arg :> Typedtree.pattern) } ]
    | Tpat_or (pat1, pat2, None) ->
        value_case_of case pat1 @ value_case_of case pat2
    | Tpat_or (_, _, Some _) ->
        failwith "[value_case_of] or pattern not supported"
    | Tpat_exception _ ->
        failwith "[value_case_of] exception pattern not supported"

  let is_pure = function
    | Texp_ident _ -> true
    | Texp_constant _ -> true
    | Texp_function _ -> true
    | Texp_construct (_, _cd, []) -> true
    | _ -> false (*ToDo*)

  let is_fun = function Texp_function _ -> true | _ -> false (*ToDo*)
  let is_raise s = String.( = ) "raise" s || String.( = ) "Stdlib.raise" s
  let is_shift0 = String.( = ) "shift0"
  let is_shift = String.( = ) "shift"
  let is_reset = String.( = ) "reset"
  let is_perform = String.( = ) "perform"
  let is_perform_atp = String.( = ) "perform_atp"
  let is_try_with = String.( = ) "try_with"
  let is_match_with = String.( = ) "match_with"
  let is_continue = String.( = ) "continue"
  let is_unif = String.( = ) "unif"

  let is_keyword s =
    is_raise s || is_shift0 s || is_shift s || is_reset s || is_perform s
    || is_try_with s || is_match_with s || is_continue s || is_unif s

  let is_keyword_arity1 s =
    is_raise s || is_shift0 s || is_shift s || is_reset s || is_perform s
    || is_continue s || is_unif s

  let is_keyword_arity3 s = is_try_with s || is_match_with s

  let is_interpreted name =
    Ast.Rtype.(is_fsym name || is_psym name || is_unop name || is_binop name)

  let content_of attr =
    match attr.Parsetree.attr_payload with
    | Parsetree.PStr ps -> (
        let ts, _, _, _, _ =
          Typemod.type_structure (Compmisc.initial_env ()) ps
        in
        match (List.hd_exn @@ List.rev ts.str_items).str_desc with
        | Tstr_eval (expr, _) -> (
            match expr.exp_desc with
            | Texp_constant (Const_string (str, _, _)) -> str
            | _ -> failwith "unsupported")
        | _ -> failwith "unsupported")
    | _ -> failwith "unsupported"

  let find_attr name =
    List.find ~f:(fun attr -> String.(attr.Parsetree.attr_name.txt = name))

  let find_comp_attrs ?config ?renv ?dtenv ~attr_name attrs =
    match find_attr attr_name attrs with
    | None -> None
    | Some attr ->
        let content = content_of attr in
        (match config with
        | Some config -> Ast.Rtype.cgen_config := config
        | None -> ());
        (match renv with Some renv -> Ast.Rtype.renv_ref := renv | None -> ());
        (match dtenv with Some dtenv -> set_dtenv dtenv | None -> ());
        (* using RtypeParser.comp_ty insted of RtypeParser.val_ty
           because menher says "Warning: symbol val_ty is never accepted." *)
        Option.return
        @@ Ast.RtypeParser.comp_ty Ast.RtypeLexer.token
             (Lexing.from_string content)
             Map.Poly.empty (*ToDo*)

  let find_val_attrs ?config ?renv ?dtenv ~attr_name attrs =
    match find_comp_attrs ?config ?renv ?dtenv ~attr_name attrs with
    | None -> None
    | Some c ->
        if Ast.Rtype.(is_pure_opsig c.op_sig && is_pure_cont c.cont_eff) then
          Some c.val_type
        else failwith "value type annotation expected"

  let ovar_of_either = function
    | First (_, _, c) -> Some c.Sort.op_sig
    | Second (_, _) -> None

  let sort_of_either = function
    | First (_, _, c) -> c.Sort.val_type
    | Second (_, sort) -> sort

  let evar_of_either = function
    | First (_, _, c) -> Some c.Sort.cont_eff
    | Second (_, _) -> None

  let triple_of_either = function
    | First (_, _, c) -> Some c
    | Second (_, _) -> None

  let subst_all_either maps = function
    | First (pure, next, c) -> First (pure, next, Term.subst_triple maps c)
    | Second (x, sort) -> Second (x, Term.subst_sort maps sort)

  let is_ f e =
    match e.exp_desc with
    | Texp_ident (p, _, _) -> f @@ Path.name p
    | _ -> false

  let subeff svs c1 c2 =
    let map, econstrs, oconstrs = Ast.Typeinf.subeff svs c1 c2 in
    if config.for_cps_trans && (not @@ Sort.is_pure c1.cont_eff) then
      ( map,
        econstrs,
        Set.add oconstrs
          (* ToDo: weaken *)
          ( Term.subst_sorts_opsig (Map.Poly.filter_map map ~f:Fn.id) c1.op_sig,
            c2.op_sig ) )
    else (map, econstrs, oconstrs)

  let is_hrec = ref false
  let rec_vars = ref Set.Poly.empty

  let rec fold_expr ~f dtenv is_handled senv expr c0 =
    let call_fold = fold_expr ~f dtenv false in
    let call_fold_handled = fold_expr ~f dtenv true in
    let mk_either senv e =
      let sort = sort_of_expr ~lift:true dtenv e in
      match e.exp_desc with
      | Texp_ident (p, _, _)
        when (Fn.non is_interpreted @@ Path.name p)
             && (Fn.non is_keyword @@ Path.name p) ->
          (* if [Path.name p] is a variable *)
          let econstrs, oconstrs, _next =
            call_fold senv e (Sort.mk_triple_from_sort sort)
          in
          (econstrs, oconstrs, Second (Ast.Ident.Tvar (Path.name p), sort))
      | _ ->
          let ovar = Sort.mk_fresh_empty_open_opsig () in
          let evar = Sort.mk_fresh_evar () in
          let econstrs, oconstrs, next =
            call_fold senv e { op_sig = ovar; val_type = sort; cont_eff = evar }
          in
          ( econstrs,
            oconstrs,
            First
              ( is_pure e.exp_desc,
                next,
                Sort.{ op_sig = ovar; val_type = sort; cont_eff = evar } ) )
    in
    Debug.print
    @@ lazy
         (sprintf "[fold_expr] %s : %s" (str_of_expr expr)
            (Term.str_of_triple c0));
    let rty_annotated =
      List.exists expr.exp_attributes ~f:(fun attr ->
          String.(attr.attr_name.txt = "annot_rty"))
      || Option.is_some
         @@ find_comp_attrs ~dtenv ~attr_name:"annot" expr.exp_attributes
    in
    match
      ( find_comp_attrs ~dtenv ~attr_name:"annot_MB" expr.exp_attributes,
        find_comp_attrs ~dtenv ~attr_name:"annot" expr.exp_attributes )
    with
    | Some c, _ | None, Some c ->
        let c' = Ast.Rtype.triple_of_comp c in
        let _ (*ToDo*), econstrs_annot, oconstrs_annot =
          subeff Map.Poly.empty c' c0
        in
        let econstrs, oconstrs, next =
          call_fold senv { expr with exp_attributes = [] (*todo*) } c'
        in
        ( Set.union econstrs_annot econstrs,
          Set.union oconstrs_annot oconstrs,
          if rty_annotated then f#f_annot (expr.exp_attributes, next) else next
        )
    | None, None -> (
        if rty_annotated then
          let econstrs, oconstrs, next =
            call_fold senv { expr with exp_attributes = [] (*todo*) } c0
          in
          (econstrs, oconstrs, f#f_annot (expr.exp_attributes, next))
        else
          match expr.exp_desc with
          | Texp_ident (p, _, ty) ->
              let name = Path.name p in
              let x_sort =
                let x_sort =
                  let ocaml_sort =
                    sort_of_type_expr dtenv ~env:expr.exp_env ty.val_type
                  in
                  match Map.Poly.find senv (Ast.Ident.Tvar name) with
                  | Some x_sort ->
                      if print_log then (
                        print_endline
                        @@ sprintf "[env] %s : %s" name
                             (Term.str_of_sort x_sort);
                        print_endline
                        @@ sprintf "[ocaml] %s : %s" name
                             (Term.str_of_sort ocaml_sort));
                      x_sort
                  | None ->
                      if String.is_prefix ~prefix:"Stdlib." name then (
                        let sort =
                          Ast.Typeinf.generalize Map.Poly.empty
                            (* type variables that occur in ty.val_type must be alpha-renamed to avoid a conflict *)
                            ocaml_sort
                        in
                        if print_log then (
                          print_endline
                          @@ sprintf "[ocaml] %s : %s" name
                               (Term.str_of_sort sort);
                          print_endline
                          @@ sprintf "senv: %s"
                               (str_of_sort_env_map Term.str_of_sort senv));
                        sort)
                      else failwith @@ sprintf "[fold_expr] %s not found" name
                in
                let x_sort = Ast.Typeinf.instantiate x_sort in
                if
                  Sort.is_svar x_sort && not (Sort.is_svar c0.val_type (*ToDo*))
                then c0.val_type
                else x_sort
              in
              let map, econstrs, oconstrs =
                subeff
                  (Map.of_set_exn
                  @@ Set.Poly.map ~f:(Fn.flip Pair.make None)
                  @@ Term.svs_of_sort x_sort)
                  (Sort.mk_triple_from_sort x_sort)
                  c0
              in
              (ref_id :=
                 let stheta =
                   Map.Poly.map ~f:(Term.subst_sorts_sort !ref_id)
                   @@ Map.Poly.filter_map map ~f:Fn.id
                 in
                 let ref_id =
                   Map.Poly.map !ref_id ~f:(Term.subst_sorts_sort stheta)
                 in
                 Map.force_merge ref_id stheta);
              ( econstrs,
                oconstrs,
                if is_interpreted name then
                  f#f_const @@ Term.mk_var (Ast.Ident.Tvar name) c0.val_type
                else if is_keyword name then
                  failwith
                  @@ sprintf "[fold_expr] %s cannot be used as an identifier"
                       name
                else f#f_var (Ast.Ident.Tvar name, x_sort (*c0.val_type*)) )
          | Texp_apply (e, [ (_, Some e') ]) when is_ is_shift0 e -> (
              match e'.exp_desc with
              | Texp_function (param :: params, body) -> (
                  match param.fp_kind with
                  | Tparam_pat pat -> (
                      match
                        sort_of_type_expr ~lift:true dtenv ~env:pat.pat_env
                          pat.pat_type
                      with
                      | Sort.SArrow (_ (* the sort of the shift0 exp *), c1) as
                        x_sort ->
                          let senv', x_opt =
                            let tvar =
                              Ast.Ident.Tvar (Ident.name param.fp_param)
                            in
                            (Map.Poly.set senv ~key:tvar ~data:x_sort, Some tvar)
                          in
                          let expr' =
                            {
                              e' with
                              exp_desc = Texp_function (params, body);
                              exp_type =
                                (match Types.get_desc e'.exp_type with
                                | Types.Tarrow (_, _, ty_body, _) -> ty_body
                                | _ ->
                                    failwith @@ "shift0 @ 1: "
                                    ^ str_of_stdbuf e'.exp_type
                                        ~f:Printtyp.type_expr);
                            }
                          in
                          let c2 =
                            Sort.
                              {
                                op_sig = Sort.mk_fresh_empty_open_opsig ();
                                val_type = sort_of_expr ~lift:true dtenv expr';
                                cont_eff = Sort.mk_fresh_evar ();
                              }
                          in
                          let econstrs2, oconstrs2, next2 =
                            call_fold senv' expr' c2
                          in
                          ( Set.add econstrs2
                              ([ Sort.mk_cont_eff c1 c2 ], c0.cont_eff),
                            oconstrs2,
                            f#f_shift0 (x_opt, x_sort) (next2, c2) )
                      | sort ->
                          failwith @@ "shift0 @ 2: " ^ Term.str_of_sort sort)
                  | _ -> failwith "shift0 @ 3")
              | _ -> failwith "shift0 @ 4")
          | Texp_apply (e, [ (_, Some e') ]) when is_ is_shift e -> (
              match e'.exp_desc with
              | Texp_function (param :: params, body) -> (
                  match param.fp_kind with
                  | Tparam_pat pat -> (
                      match
                        sort_of_type_expr ~lift:true dtenv ~env:pat.pat_env
                          pat.pat_type
                      with
                      | Sort.SArrow (_ (* the sort of the shift exp *), c1) as
                        x_sort ->
                          let senv', x_opt =
                            match pat.pat_desc with
                            | Tpat_var (name, _, _) ->
                                let tvar = Ast.Ident.Tvar (Ident.name name) in
                                ( Map.Poly.set senv ~key:tvar ~data:x_sort,
                                  Some tvar )
                            | Tpat_any -> (senv, None)
                            | _ -> failwith "shift @ 1"
                          in
                          let expr' =
                            {
                              e' with
                              exp_desc = Texp_function (params, body);
                              exp_type =
                                (match Types.get_desc e'.exp_type with
                                | Types.Tarrow (_, _, ty_body, _) -> ty_body
                                | _ ->
                                    failwith @@ "shift @ 2: "
                                    ^ str_of_stdbuf e'.exp_type
                                        ~f:Printtyp.type_expr);
                            }
                          in
                          (* type inference for shift (but shift0) introduces fresh type variables! *)
                          let sort_reset = Sort.mk_fresh_svar () in
                          let ovar2 = Sort.mk_fresh_empty_open_opsig () in
                          let sort2 = sort_of_expr ~lift:true dtenv expr' in
                          let evar2 = Sort.mk_fresh_evar () in
                          let c_reset =
                            Sort.
                              {
                                op_sig = ovar2;
                                val_type = sort_reset;
                                cont_eff = evar2;
                              }
                          in
                          let econstrs1, oconstrs1, next1 =
                            call_fold senv' expr'
                              {
                                op_sig = Sort.empty_closed_opsig;
                                val_type = sort2;
                                cont_eff =
                                  Sort.mk_cont_eff
                                    (Sort.mk_triple_from_sort sort2)
                                    c_reset;
                              }
                          in
                          let next2 = f#f_reset (next1, sort2) in
                          ( Set.add econstrs1
                              ([ Sort.mk_cont_eff c1 c_reset ], c0.cont_eff),
                            oconstrs1,
                            f#f_shift0 (x_opt, x_sort)
                              ( next2,
                                {
                                  op_sig = ovar2;
                                  val_type = sort2;
                                  cont_eff = evar2;
                                } ) )
                      | sort ->
                          failwith @@ "shift @ 3: " ^ Term.str_of_sort sort)
                  | _ -> failwith "shift @ 4")
              | _ -> failwith "shift @ 5")
          | Texp_apply (e, [ (_, Some e') ]) when is_ is_reset e -> (
              match e'.exp_desc with
              | Texp_function (param :: params, body) -> (
                  match param.fp_kind with
                  | Tparam_pat pat ->
                      (match pat.pat_desc with
                      | Tpat_construct (_, cd, [], _)
                        when String.(cd.cstr_name = "()") ->
                          ()
                      | Tpat_any -> ()
                      | _ -> failwith "reset @ 1");
                      let expr' =
                        {
                          e' with
                          exp_desc = Texp_function (params, body);
                          exp_type =
                            (match Types.get_desc e'.exp_type with
                            | Types.Tarrow (_, _, ty_body, _) -> ty_body
                            | _ ->
                                failwith @@ "reset @ 2: "
                                ^ str_of_stdbuf e'.exp_type
                                    ~f:Printtyp.type_expr);
                        }
                      in
                      let sort1 = sort_of_expr ~lift:true dtenv expr' in
                      let econstrs1, oconstrs1, next1 =
                        call_fold senv expr'
                          {
                            op_sig = Sort.empty_closed_opsig;
                            val_type = sort1;
                            cont_eff =
                              Sort.mk_cont_eff
                                (Sort.mk_fresh_pure_triple_from_sort
                                   sort1 (*ToDo*))
                                c0;
                          }
                      in
                      (econstrs1, oconstrs1, f#f_reset (next1, sort1))
                  | _ -> failwith "reset @ 3")
              | _ -> failwith "reset @ 4")
          | Texp_apply (e, [ (_, Some e') ])
            when is_ (fun x -> is_perform x || is_perform_atp x || is_raise x) e
            -> (
              match e'.exp_desc with
              | Texp_construct (_, cd, args) ->
                  let econstrss, oconstrss, nexts_either =
                    List.unzip3 @@ List.map args ~f:(mk_either senv)
                  in
                  let is_atp =
                    (*ToDo: support ATP handlers in RCaml *)
                    config.for_cps_trans
                    &&
                    (*ToDo: ad hoc*)
                    is_ is_perform_atp e
                  in
                  let op_sort, op_cont =
                    if is_atp then
                      ( Sort.mk_fun
                        @@ List.map nexts_either ~f:sort_of_either
                        @ [ c0.val_type ],
                        Sort.Pure )
                    else
                      let c1 = Sort.mk_fresh_triple () in
                      let c2 = Sort.mk_fresh_triple () in
                      ( Sort.mk_fun
                        @@ List.map nexts_either ~f:sort_of_either
                        @ [ Sort.SArrow (Sort.SArrow (c0.val_type, c1), c2) ],
                        Sort.mk_cont_eff c1 c2 )
                  in
                  let opsig_op =
                    Sort.OpSig
                      ( ALMap.singleton cd.cstr_name op_sort,
                        Some (Ast.Ident.mk_fresh_rvar ()) )
                  in
                  ( Set.Poly.union_list
                    @@ Set.Poly.singleton
                         ( List.rev
                             (op_cont
                             :: List.filter_map nexts_either ~f:evar_of_either),
                           c0.cont_eff )
                       :: econstrss,
                    Set.Poly.union_list
                    @@ (Set.Poly.of_list
                       @@ List.map ~f:(Pair.make c0.op_sig)
                       @@ opsig_op
                          :: List.filter_map nexts_either ~f:ovar_of_either)
                       :: oconstrss,
                    f#f_perform is_atp e.exp_attributes
                      (cd.cstr_name, c0.val_type, op_cont)
                      nexts_either )
              | _ -> failwith "perform")
          | Texp_apply
              ( e,
                [
                  (_, Some e_body_fun); (_, Some e_body_arg); (_, Some e_handler);
                ] )
            when is_ (fun x -> is_try_with x || is_match_with x) e ->
              let e_retc_opt, e_exnc_opt, e_effc =
                match e_handler.exp_desc with
                | Texp_record record -> (
                    let expr_of label_name =
                      match
                        Array.find record.fields ~f:(fun (l, _) ->
                            String.(l.lbl_name = label_name))
                      with
                      | Some (_, Overridden (_, e)) -> e
                      | _ -> failwith "handling @ 1"
                    in
                    match record.fields with
                    | [| _ |] -> (None, None, expr_of "effc")
                    | [| _; _; _ |] ->
                        ( Some (expr_of "retc"),
                          Some (expr_of "exnc"),
                          expr_of "effc" )
                    | _ -> failwith "handling @ 2")
                | _ -> failwith "handling @ 3"
              in
              (* effc *)
              let ( econstrss_op,
                    oconstrss_op,
                    nexts_op,
                    names_op,
                    kinds_op,
                    sorts_op,
                    clauses_op ) =
                let pat, body =
                  match e_effc.exp_desc with
                  | Texp_function ([ param ], Tfunction_body body) -> (
                      match param.fp_kind with
                      | Tparam_pat pat -> (pat, body)
                      | _ -> failwith "handling @ eff1")
                  | _ -> failwith "handling @ eff2"
                in
                let senv' =
                  let s_pat_op =
                    sort_of_type_expr ~lift:true dtenv ~env:pat.pat_env
                      pat.pat_type
                  in
                  Map.update_with (*shadowing*) senv
                  @@ Ast.Pattern.senv_of
                       (pattern_of dtenv ~sort:(Some s_pat_op) pat)
                       s_pat_op
                in
                match body.exp_desc with
                | Texp_match (e_op, cases, _, _) ->
                    let sort_op = sort_of_expr ~lift:true dtenv e_op in
                    List.unzip7
                    @@ List.map ~f:(fun case ->
                           let pat =
                             pattern_of dtenv ~sort:(Some sort_op) case.c_lhs
                           in
                           if false then
                             print_endline
                             @@ sprintf "case: %s"
                                  (Ast.Pattern.str_of ~with_sort:true pat);
                           let op_name, (x_op_params, s_op_params) =
                             match pat with
                             | Ast.Pattern.PCons (_dt, name, pat_params) ->
                                 ( name,
                                   List.unzip
                                   @@ List.map pat_params ~f:(function
                                        | Ast.Pattern.PAny sort ->
                                            ( Ast.Ident.mk_fresh_tvar
                                                ~prefix:(Some "dummy")
                                                () (*dummy*),
                                              sort )
                                        | Ast.Pattern.PVar b -> b
                                        | _ -> failwith "handling @ eff3") )
                             | _ -> failwith "handling @ eff4"
                           in
                           let s_annot_opts =
                             match case.c_lhs.pat_desc with
                             | Tpat_construct (_loc, _cd, pats, _) ->
                                 List.map pats ~f:(fun pat ->
                                     match
                                       ( find_val_attrs ~dtenv
                                           ~attr_name:"annot_MB"
                                           pat.pat_attributes,
                                         find_val_attrs ~dtenv
                                           ~attr_name:"annot" pat.pat_attributes
                                       )
                                     with
                                     | Some t, _ | None, Some t ->
                                         let sort_annot =
                                           Ast.Rtype.sort_of_val t
                                         in
                                         if print_log then
                                           print_endline
                                           @@ sprintf "annot: %s"
                                                (Term.str_of_sort sort_annot);
                                         Some sort_annot
                                     | None, None -> None)
                             | _ -> failwith "handling @ eff5"
                           in
                           let s_op_params =
                             (* update with annotated sorts *)
                             List.map2_exn s_op_params s_annot_opts
                               ~f:(fun s_op_param ->
                                 Option.value ~default:s_op_param)
                           in
                           let senv'' =
                             let pat_senv =
                               Map.update_with (Ast.Pattern.senv_of pat sort_op)
                               @@ Map.Poly.of_alist_exn
                               @@ List.filter_map ~f:(fun (x, s_opt) ->
                                      Option.map s_opt ~f:(Pair.make x))
                               @@ List.zip_exn x_op_params s_annot_opts
                             in
                             Map.update_with (*shadowing*) senv' pat_senv
                           in
                           match case.c_rhs.exp_desc with
                           | Texp_construct
                               ( _,
                                 { cstr_name = "Some"; _ },
                                 [
                                   ({
                                      exp_desc =
                                        Texp_function (k_arg :: args, body);
                                      _;
                                    } as exp0);
                                 ] ) ->
                               let is_atp =
                                 let is_cont_app e =
                                   match e.exp_desc with
                                   | Texp_apply
                                       ( e,
                                         [ (_, Some k); (_, Some arg) (*ToDo*) ]
                                       ) ->
                                       is_ is_continue e
                                       && is_
                                            (fun k ->
                                              String.(
                                                k = Ident.name k_arg.fp_param))
                                            k
                                       && (not @@ occurs [] k_arg.fp_param arg)
                                   | _ -> false (*ToDo*)
                                 in
                                 (*ToDo: support generic handlers in RCaml *)
                                 config.for_cps_trans
                                 && List.is_empty
                                      args (* no handler parameters *)
                                 &&
                                 match body with
                                 | Tfunction_body e -> (
                                     match e.exp_desc with
                                     | Texp_let (_, vbs, e) ->
                                         is_cont_app e
                                         && List.for_all vbs ~f:(fun vb ->
                                                (* k_arg.fp_param does not occur free in vb *)
                                                not
                                                @@ occurs (bvs vb.vb_pat [])
                                                     k_arg.fp_param vb.vb_expr)
                                     | _ -> is_cont_app e)
                                 | Tfunction_cases _ ->
                                     failwith "handling @ eff6"
                               in
                               Debug.print
                               @@ lazy
                                    (sprintf "%s handler for %s"
                                       (if is_atp then "ATP" else "ATM")
                                       (Ast.Pattern.str_of pat));
                               let op_sig_gen =
                                 Sort.mk_fresh_empty_open_opsig ()
                               in
                               let k_pat =
                                 match k_arg.fp_kind with
                                 | Tparam_pat k_pat -> k_pat
                                 | _ -> failwith "handling @ eff7"
                               in
                               let s_arity, c_ini =
                                 match
                                   sort_of_type_expr ~lift:true
                                     ~env:k_pat.pat_env dtenv k_pat.pat_type
                                 with
                                 | T_dt.SDT dt
                                   when String.(
                                          Datatype.name_of dt = "continuation")
                                   -> (
                                     match Datatype.params_of dt with
                                     | [ s_arity; s_ans ] ->
                                         if false then
                                           print_endline
                                           @@ sprintf "s_arity: %s, s_ans: %s"
                                                (Term.str_of_sort s_arity)
                                                (Term.str_of_sort s_ans);
                                         let c_ini =
                                           Sort.
                                             {
                                               op_sig =
                                                 (if is_atp then op_sig_gen
                                                  else
                                                    Sort
                                                    .mk_fresh_empty_open_opsig
                                                      ());
                                               val_type = s_ans;
                                               cont_eff =
                                                 (if is_atp then Sort.Pure
                                                  else if true then
                                                    Sort.mk_fresh_evar ()
                                                  else
                                                    Sort.Eff
                                                      ( Sort.mk_fresh_triple (),
                                                        Sort.mk_fresh_triple ()
                                                      ));
                                             }
                                         in
                                         (s_arity, c_ini)
                                     | _ -> failwith "handling @ eff8")
                                 | _ -> failwith "handling @ eff9"
                               in
                               let s_cont = Sort.SArrow (s_arity, c_ini) in
                               if false then
                                 print_endline
                                 @@ sprintf "s_cont: %s"
                                      (Term.str_of_sort s_cont);
                               let k_cont_opt, senv_clause =
                                 match
                                   pattern_of dtenv k_pat ~sort:(Some s_cont)
                                 with
                                 | PAny _ -> (None, senv'')
                                 | PVar (k, _) ->
                                     ( Some k,
                                       Map.Poly.add_exn ~key:k ~data:s_cont
                                         senv'' )
                                 | _ -> failwith "handling @ eff10"
                               in
                               let e_clause =
                                 {
                                   exp0 with
                                   exp_desc = Texp_function (args, body);
                                   exp_type =
                                     (match Types.get_desc exp0.exp_type with
                                     | Types.Tarrow (_, _, ty_body, _) ->
                                         ty_body
                                     | _ ->
                                         failwith
                                         @@ sprintf "handling @ eff11: %s"
                                              (str_of_stdbuf exp0.exp_type
                                                 ~f:Printtyp.type_expr));
                                 }
                               in
                               let c_fin =
                                 Sort.
                                   {
                                     op_sig =
                                       (if is_atp then op_sig_gen
                                        else Sort.mk_fresh_empty_open_opsig ());
                                     val_type =
                                       sort_of_expr ~lift:true dtenv e_clause;
                                     cont_eff =
                                       (if is_atp then Sort.Pure
                                        else Sort.mk_fresh_evar ());
                                   }
                               in
                               let econstrs, oconstrs, next =
                                 call_fold senv_clause e_clause c_fin
                               in
                               let op_kind =
                                 if is_atp then ATPHandler else ATMHandler
                               in
                               let op_sort =
                                 if is_atp then
                                   (Sort.mk_eff_fun s_op_params
                                      (*@ [
                                          (* dummy continuation *)
                                          Sort.mk_fresh_svar ();
                                        ]*)
                                      Sort.
                                        {
                                          op_sig =
                                            Sort.empty_closed_opsig (*ToDo*);
                                          val_type = s_arity;
                                          cont_eff = Sort.Pure;
                                        })
                                     .val_type
                                 else
                                   Sort.mk_fun @@ s_op_params
                                   @ [ Sort.SArrow (s_cont, c_fin) ]
                               in
                               if false then
                                 print_endline
                                 @@ sprintf "op_sort: %s"
                                      (Term.str_of_sort op_sort);
                               if print_log then
                                 Debug.print
                                 @@ lazy
                                      (sprintf "senv_clause:\n%s\nop_sort: %s"
                                         (str_of_sort_env_map Term.str_of_sort
                                            senv_clause)
                                         (Term.str_of_sort op_sort));
                               ( econstrs,
                                 Set.add oconstrs (c0.op_sig, op_sig_gen)
                                 (* ToDo: generate other constraints on op_sig_gen *),
                                 next,
                                 op_name,
                                 op_kind,
                                 op_sort,
                                 ( x_op_params,
                                   s_op_params,
                                   k_cont_opt,
                                   s_cont,
                                   c_fin ) )
                           | _ -> failwith "handling @ eff12")
                    @@ List.concat_map cases ~f:(fun case ->
                           value_case_of case case.c_lhs)
                | _ -> failwith "handling @ eff113"
              in
              (* exnc *)
              let ( econstrss_exn,
                    oconstrss_exn,
                    nexts_exn,
                    names_exn,
                    sorts_exn,
                    clauses_exn ) =
                match e_exnc_opt with
                | None -> ([], [], [], [], [], [])
                | Some e_exnc -> (
                    match e_exnc.exp_desc with
                    | Texp_function (params, b) ->
                        let pat_body_list =
                          match (params, b) with
                          | [ param ], Tfunction_body body -> (
                              match param.fp_kind with
                              | Tparam_pat pat -> [ (pat, body) ]
                              | _ -> failwith "handling @ exn1")
                          | [], Tfunction_cases { cases; _ } ->
                              List.map cases ~f:(fun case ->
                                  (case.c_lhs, case.c_rhs))
                          | _ -> failwith "handling @ exn2"
                        in
                        List.unzip6
                        @@ List.map pat_body_list ~f:(fun (pat0, e_clause) ->
                               let sort_pat =
                                 sort_of_type_expr ~lift:true dtenv
                                   ~env:pat0.pat_env pat0.pat_type
                               in
                               let pat =
                                 pattern_of dtenv ~sort:(Some sort_pat) pat0
                               in
                               let exn_name, (x_exn_params, s_exn_params) =
                                 match pat with
                                 | Ast.Pattern.PCons (_dt, name, pat_params) ->
                                     ( name,
                                       List.unzip
                                       @@ List.map pat_params ~f:(function
                                            | Ast.Pattern.PAny sort ->
                                                ( Ast.Ident.mk_fresh_tvar
                                                    ~prefix:(Some "dummy")
                                                    () (*dummy*),
                                                  sort )
                                            | Ast.Pattern.PVar b -> b
                                            | _ -> failwith "handling @ exn3")
                                     )
                                 | Ast.Pattern.(PAny _ | PVar _) ->
                                     failwith
                                       "write out all exception clauses \
                                        explicitly"
                                 | _ -> failwith "handling @ exn4"
                               in
                               let s_arity = Sort.mk_fresh_svar () in
                               let c_ini = Sort.mk_fresh_triple () in
                               let s_cont = Sort.SArrow (s_arity, c_ini) in
                               let c_fin =
                                 Sort.
                                   {
                                     op_sig = Sort.mk_fresh_empty_open_opsig ();
                                     val_type =
                                       sort_of_expr ~lift:true dtenv e_clause;
                                     cont_eff = Sort.mk_fresh_evar ();
                                   }
                               in
                               let econstrs, oconstrs, next =
                                 call_fold
                                   (Map.update_with (*shadowing*) senv
                                      (Ast.Pattern.senv_of pat sort_pat))
                                   e_clause c_fin
                               in
                               let exn_sort =
                                 Sort.mk_fun @@ s_exn_params
                                 @ [ Sort.SArrow (s_cont, c_fin) ]
                               in
                               ( econstrs,
                                 oconstrs,
                                 next,
                                 exn_name,
                                 exn_sort,
                                 ( x_exn_params,
                                   s_exn_params,
                                   None,
                                   s_cont,
                                   c_fin ) ))
                    | Texp_ident (p, _, ty) when is_raise @@ Path.name p -> (
                        let sort_arg =
                          match
                            sort_of_type_expr ~lift:true ~env:e_exnc.exp_env
                              dtenv ty.val_type
                          with
                          | Sort.SArrow (s, _) -> s
                          | _ -> failwith "handling @ exn5"
                        in
                        match sort_arg with
                        | T_dt.SDT _ ->
                            failwith
                              "write out all exception clauses explicitly"
                        | Sort.SVar sv
                          when String.(Ast.Ident.name_of_svar sv = "exn") ->
                            (* datatype [exn] is not in dtenv (i.e. [exn] is the build-in type)
                                   and [raise] here is used as a dummy expression for [exnc] *)
                            ([], [], [], [], [], [])
                        | _ ->
                            failwith @@ "handling @ exn6: "
                            ^ Term.str_of_sort sort_arg)
                    | _ -> failwith "handling @ exn7")
              in
              let econstrss, oconstrss, nexts, names, kinds, sorts, clauses =
                ( econstrss_op @ econstrss_exn,
                  oconstrss_op @ oconstrss_exn,
                  nexts_op @ nexts_exn,
                  names_op @ names_exn,
                  kinds_op @ List.map names_exn ~f:(Fn.const ExceptionHandler),
                  sorts_op @ sorts_exn,
                  clauses_op @ clauses_exn )
              in
              let s_body =
                match sort_of_expr ~lift:true dtenv e_body_fun with
                | Sort.SArrow (_s_arg, c_body) -> c_body.val_type
                | _ -> failwith "handling @ m2"
              in
              (* retc *)
              let econstrs_r, oconstrs_r, next_r, x_r, c_r =
                let evar_retc = Sort.mk_fresh_evar () in
                let ovar_retc = Sort.mk_fresh_empty_open_opsig () in
                match e_retc_opt with
                | None ->
                    let x_r = Ast.Ident.mk_fresh_tvar ~prefix:(Some "x_r") () in
                    let c_r =
                      Sort.
                        {
                          op_sig = ovar_retc;
                          val_type = s_body;
                          cont_eff = evar_retc;
                        }
                    in
                    let _ (*ToDo*), econstrs, oconstrs =
                      subeff Map.Poly.empty
                        {
                          op_sig = Sort.mk_fresh_empty_open_opsig ();
                          val_type = s_body;
                          cont_eff = Sort.Pure;
                        }
                        c_r
                    in
                    (econstrs, oconstrs, f#f_var (x_r, s_body), x_r, c_r)
                | Some e_retc ->
                    let pat0, body =
                      match e_retc.exp_desc with
                      | Texp_function (param :: params, body) -> (
                          match param.fp_kind with
                          | Tparam_pat pat ->
                              ( pat,
                                {
                                  e_retc with
                                  exp_desc = Texp_function (params, body);
                                  exp_type =
                                    (match Types.get_desc e_retc.exp_type with
                                    | Types.Tarrow (_, _, ty_body, _) -> ty_body
                                    | _ ->
                                        failwith @@ "handling @ ret1: "
                                        ^ str_of_stdbuf e_retc.exp_type
                                            ~f:Printtyp.type_expr);
                                } )
                          | _ -> failwith "handling @ ret2")
                      | _ -> failwith "handling @ ret3"
                    in
                    let c_r =
                      Sort.
                        {
                          op_sig = ovar_retc;
                          val_type = sort_of_expr ~lift:true dtenv body;
                          cont_eff = evar_retc;
                        }
                    in
                    let s_pat =
                      sort_of_type_expr ~lift:true dtenv ~env:pat0.pat_env
                        pat0.pat_type
                    in
                    let pat = pattern_of dtenv ~sort:(Some s_pat) pat0 in
                    let econstrs, oconstrs, next =
                      call_fold
                        (Map.update_with (*shadowing*) senv
                        @@ Ast.Pattern.senv_of pat s_pat)
                        body c_r
                    in
                    let x_r =
                      match pat with
                      | PAny _ | PCons (_, "()", []) ->
                          Ast.Ident.mk_fresh_tvar ~prefix:(Some "dummy")
                            () (*dummy*)
                      | PVar (x_r, _) -> x_r
                      | _ ->
                          failwith @@ "handling @ ret4: "
                          ^ Ast.Pattern.str_of pat
                    in
                    (econstrs, oconstrs, next, x_r, c_r)
              in
              let econstrs_b, oconstrs_b, next_b, c_b =
                let c_b =
                  Sort.
                    {
                      op_sig = Sort.mk_fresh_empty_open_opsig ();
                      val_type = s_body;
                      cont_eff = Sort.mk_fresh_evar ();
                    }
                in
                let exp_body =
                  {
                    e_body_fun with
                    exp_desc =
                      Texp_apply (e_body_fun, [ (Nolabel, Some e_body_arg) ]);
                    exp_type =
                      (*dummy*)
                      (match Types.get_desc e_body_fun.exp_type with
                      | Types.Tarrow (_, _, ty_body, _) -> ty_body
                      | _ ->
                          failwith @@ "handling @ m1: "
                          ^ str_of_stdbuf expr.exp_type ~f:Printtyp.type_expr);
                  }
                in
                is_hrec :=
                  Set.exists !rec_vars ~f:(fun x ->
                      occurs []
                        (Ident.create_local (Ast.Ident.name_of_tvar x))
                        exp_body);
                if false then
                  print_endline
                  @@ sprintf "is_hrec: %s, rec_vars: %s"
                       (Bool.string_of !is_hrec)
                       (Set.to_list !rec_vars
                       |> List.map ~f:Ast.Ident.name_of_tvar
                       |> String.concat ~sep:", ");
                if print_log then
                  print_endline
                  @@ sprintf "opsig: %s" (Term.str_of_opsig c_b.op_sig);
                let econstrs_b, oconstrs_b, next_b =
                  call_fold_handled senv exp_body c_b
                in
                let _ (*ToDo*), econstrs, oconstrs =
                  subeff Map.Poly.empty c_b
                    {
                      op_sig =
                        Sort.OpSig
                          ( ALMap.of_alist_exn @@ List.zip_exn names sorts
                            (* ToDo: assuming that all operations are handled or forwarded? *),
                            None );
                      val_type = s_body;
                      cont_eff = Sort.mk_cont_eff c_r c0;
                    }
                in
                ( Set.union econstrs_b econstrs,
                  Set.union oconstrs_b oconstrs,
                  next_b,
                  c_b )
              in
              ( Set.Poly.union_list (econstrs_b :: econstrs_r :: econstrss),
                Set.Poly.union_list (oconstrs_b :: oconstrs_r :: oconstrss),
                f#f_handling (next_b, c_b) (next_r, x_r, c_r)
                @@ List.zip4_exn names kinds nexts clauses )
          | Texp_apply (e, [ (_, Some e') ]) when is_ is_continue e -> (
              match sort_of_expr ~lift:true dtenv e' with
              | T_dt.SDT dt when String.(Datatype.name_of dt = "continuation")
                ->
                  call_fold senv e' c0
              | _ -> failwith "continue")
          | Texp_apply (e, [ (_, Some e') ]) when is_ is_unif e ->
              let sort = sort_of_expr ~lift:false dtenv e' in
              let econstrs, oconstrs, next =
                call_fold senv e' (Sort.mk_triple_from_sort sort)
              in
              ( Set.add econstrs ([ Sort.Pure ], c0.cont_eff),
                oconstrs,
                f#f_unif (next, sort) )
          | Texp_apply (e, e1' :: e2' :: e3' :: es')
            when is_ is_keyword_arity3 e ->
              call_fold senv
                {
                  expr (*ToDo*) with
                  exp_desc =
                    Texp_apply
                      ( {
                          expr (*ToDo*) with
                          exp_desc = Texp_apply (e, [ e1'; e2'; e3' ]);
                        },
                        es' );
                }
                c0
          | Texp_apply (e, e' :: es') when is_ is_keyword_arity1 e ->
              call_fold senv
                {
                  expr (*ToDo*) with
                  exp_desc =
                    Texp_apply
                      ( { expr (*ToDo*) with exp_desc = Texp_apply (e, [ e' ]) },
                        es' );
                }
                c0
          | Texp_apply (e1, es) ->
              assert (not @@ is_ is_keyword e1);
              let econstrss, oconstrss, nexts_either =
                List.unzip3
                @@ List.map es ~f:(function
                     | _label, Some e -> mk_either senv e
                     | _label, None -> failwith "default arg not supported")
              in
              let ovars', evars', sort_fun =
                Sort.of_args_ret
                  (List.map nexts_either ~f:sort_of_either)
                  c0.val_type
                (*sort_of_expr dtenv e1*)
              in
              let ovar1 = Sort.mk_fresh_empty_open_opsig () in
              let evar1 = Sort.mk_fresh_evar () in
              let econstrs1, oconstrs1, next1 =
                call_fold senv e1
                  { op_sig = ovar1; val_type = sort_fun; cont_eff = evar1 }
              in
              ( Set.Poly.union_list
                @@ Set.Poly.singleton
                     ( (List.rev
                       @@ evar1
                          :: List.filter_map nexts_either ~f:evar_of_either)
                       @ evars',
                       c0.cont_eff )
                   :: econstrs1 :: econstrss,
                Set.Poly.union_list
                @@ (Set.Poly.of_list
                   @@ List.map ~f:(Pair.make c0.op_sig)
                   @@ (ovar1 :: ovars')
                   @ List.filter_map nexts_either ~f:ovar_of_either)
                   :: oconstrs1 :: oconstrss,
                f#f_apply is_handled
                  (is_pure e1.exp_desc, next1, ovars', ovar1, evars', evar1)
                  nexts_either )
          | Texp_ifthenelse (e1, e2, e3_opt) -> (
              let evar1 = Sort.mk_fresh_evar () in
              let econstrs1, oconstrs1, next1 =
                call_fold senv e1
                  {
                    op_sig = c0.op_sig;
                    val_type = sort_of_expr ~lift:true dtenv e1;
                    cont_eff = evar1;
                  }
              in
              let evar2 = Sort.mk_fresh_evar () in
              let econstrs2, oconstrs2, next2 =
                call_fold senv e2 { c0 with cont_eff = evar2 }
              in
              match e3_opt with
              | None ->
                  ( Set.Poly.union_list
                      [
                        Set.Poly.singleton ([ evar1; evar2 ], c0.cont_eff);
                        econstrs1;
                        econstrs2;
                      ],
                    Set.Poly.union_list [ oconstrs1; oconstrs2 ],
                    f#f_ite (next1, evar1) (next2, evar2) None )
              | Some e3 ->
                  let evar3 = Sort.mk_fresh_evar () in
                  let econstrs3, oconstrs3, next3 =
                    call_fold senv e3 { c0 with cont_eff = evar3 }
                  in
                  ( Set.Poly.union_list
                      [
                        Set.Poly.of_list
                          [
                            ([ evar1; evar2 ], c0.cont_eff);
                            ([ evar1; evar3 ], c0.cont_eff);
                          ];
                        econstrs1;
                        econstrs2;
                        econstrs3;
                      ],
                    Set.Poly.union_list [ oconstrs1; oconstrs2; oconstrs3 ],
                    f#f_ite (next1, evar1) (next2, evar2) @@ Some (next3, evar3)
                  ))
          | Texp_constant c ->
              let t =
                match c with
                | Const_float r -> T_real.mk_real @@ Q.of_string r
                | Const_int i -> T_int.from_int i
                | Const_int32 i32 -> T_int.mk_int @@ Z.of_int32 i32
                | Const_int64 i64 -> T_int.mk_int @@ Z.of_int64 i64
                | Const_nativeint inative ->
                    T_int.mk_int @@ Z.of_nativeint inative
                | Const_string (str, _, (None | Some _ (* {...|...|...} *))) ->
                    T_string.make str
                | Const_char _ ->
                    failwith @@ "[fold_expr] char is unsupported: "
                    ^ str_of_expr expr
              in
              ( Set.Poly.singleton ([ Sort.Pure ], c0.cont_eff),
                Set.Poly.singleton (c0.op_sig, Sort.empty_closed_opsig) (*ToDo*),
                f#f_const t )
          | Texp_assert (e, _) ->
              let evar1 = Sort.mk_fresh_evar () in
              let econstrs, oconstrs, next =
                match e.exp_desc with
                | Texp_construct (_, cd, [])
                  when String.(cd.cstr_name = "false") ->
                    (Set.Poly.empty, Set.Poly.empty, None)
                | _ ->
                    let econstrs, oconstrs, next =
                      call_fold senv e
                        {
                          op_sig = c0.op_sig;
                          val_type = sort_of_expr ~lift:true dtenv e;
                          cont_eff = evar1;
                        }
                    in
                    (econstrs, oconstrs, Some next)
              in
              ( Set.Poly.union_list
                  [ Set.Poly.singleton ([ evar1 ], c0.cont_eff); econstrs ],
                oconstrs,
                f#f_assert (next, evar1) )
          | Texp_let (rec_flag, vbs, e2) ->
              let defs =
                List.map vbs ~f:(fun vb ->
                    if
                      List.exists vb.vb_attributes ~f:(fun attr ->
                          String.(attr.attr_name.txt = "annot_rty"))
                      || Option.is_some
                         @@ find_val_attrs ~dtenv ~attr_name:"annot"
                              vb.vb_attributes
                    then
                      failwith
                        "rtype annotations on let-bindings are not supported";
                    (*todo*)
                    let sort =
                      match
                        ( find_val_attrs ~dtenv ~attr_name:"annot_MB"
                            vb.vb_attributes,
                          find_val_attrs ~dtenv ~attr_name:"annot"
                            vb.vb_attributes )
                      with
                      | Some t, _ | None, Some t -> Ast.Rtype.sort_of_val t
                      | None, None -> sort_of_expr ~lift:true dtenv vb.vb_expr
                    in
                    let pat = pattern_of dtenv ~sort:(Some sort) vb.vb_pat in
                    (Ast.Pattern.senv_of pat sort, pat, vb.vb_expr, sort))
              in
              let ( pats,
                    econstrss,
                    oconstrss,
                    pure1s,
                    is_fun1s,
                    next1s,
                    sort1s,
                    evar1s ) =
                let senv_bounds =
                  match rec_flag with
                  | Recursive ->
                      Map.update_with_list
                      (*shadowing*)
                      @@ senv
                         :: List.map defs (* assume distinct *) ~f:Quadruple.fst
                  | Nonrecursive -> senv
                in
                List.unzip8
                @@ List.map defs ~f:(fun (_, pat, expr, sort) ->
                       let evar = Sort.mk_fresh_evar () in
                       let old_rec_vars = !rec_vars in
                       (rec_vars :=
                          match rec_flag with
                          | Recursive -> Ast.Pattern.tvars_of pat
                          | Nonrecursive -> Set.Poly.empty);
                       let econstrs, oconstrs, next =
                         call_fold senv_bounds expr
                           {
                             op_sig = c0.op_sig;
                             val_type = sort;
                             cont_eff = evar;
                           }
                       in
                       rec_vars := old_rec_vars;
                       ( pat,
                         econstrs,
                         oconstrs,
                         is_pure expr.exp_desc,
                         is_fun expr.exp_desc,
                         next,
                         sort,
                         evar ))
              in
              let senv_body =
                let pat_senvs =
                  List.map defs (* assume distinct *) ~f:Quadruple.fst
                in
                let generalizable =
                  List.for_all pure1s ~f:Fn.id
                  && List.for_all pats ~f:(Ast.Pattern.sort_of >> Sort.is_arrow)
                in
                Map.update_with_list
                (*shadowing*)
                @@ senv
                   ::
                   (if generalizable then
                      List.map pat_senvs
                        ~f:(Map.Poly.map ~f:(Ast.Typeinf.generalize senv))
                    else pat_senvs)
              in
              let evar2 = Sort.mk_fresh_evar () in
              let econstrs, oconstrs, next =
                call_fold senv_body e2 { c0 with cont_eff = evar2 }
              in
              ( Set.Poly.union_list
                @@ Set.Poly.singleton (evar1s @ [ evar2 ], c0.cont_eff)
                   :: econstrs :: econstrss,
                Set.Poly.union_list (oconstrs :: oconstrss),
                f#f_let_and
                  Stdlib.(rec_flag = Recursive)
                  pats
                  (pure1s, is_fun1s, next1s, sort1s, evar1s)
                  (next, evar2) )
          | Texp_function ([], Tfunction_body body) -> call_fold senv body c0
          | Texp_function (param :: params, body) -> (
              let sarg, sret =
                match c0.val_type with
                | Sort.SArrow (sarg, sret) -> (sarg, sret)
                | _ ->
                    failwith @@ "function type expected but " ^ Term.str_of_sort
                    @@ c0.val_type
              in
              match param.fp_kind with
              | Tparam_pat pat0 ->
                  let sarg, econstrs_annot, oconstrs_annot =
                    (* constr on MB type annotations on arguments *)
                    let attrs = pat0.pat_attributes in
                    match
                      ( find_val_attrs ~dtenv ~attr_name:"annot_MB" attrs,
                        find_val_attrs ~dtenv ~attr_name:"annot" attrs )
                    with
                    | None, None -> (sarg, Set.Poly.empty, Set.Poly.empty)
                    | Some t, _ | None, Some t ->
                        let sort_annot = Ast.Rtype.sort_of_val t in
                        if print_log then
                          print_endline
                          @@ sprintf "annot: %s = %s"
                               (Term.str_of_sort sort_annot)
                               (Term.str_of_sort sarg);
                        let eqtype s1 s2 =
                          let _map (*ToDo*), econstrs, oconstrs =
                            Ast.Typeinf.subtype Map.Poly.empty s1 s2
                          in
                          let _map (*ToDo*), econstrs', oconstrs' =
                            Ast.Typeinf.subtype Map.Poly.empty s2 s1
                          in
                          ( Set.union econstrs econstrs',
                            Set.union oconstrs oconstrs' )
                        in
                        let econstrs, oconstrs = eqtype sarg sort_annot in
                        (sort_annot, econstrs, oconstrs)
                  in
                  if print_log then print_endline @@ Term.str_of_sort sarg;
                  let pat = pattern_of dtenv ~sort:(Some sarg) pat0 in
                  let pat_senv = Ast.Pattern.senv_of pat sarg in
                  if print_log then
                    print_endline
                    @@ str_of_sort_env_map Term.str_of_sort pat_senv;
                  let expr' =
                    {
                      expr with
                      exp_desc = Texp_function (params, body);
                      exp_type =
                        (match Types.get_desc expr.exp_type with
                        | Types.Tarrow (_, _, ty_body, _) -> ty_body
                        | _ ->
                            failwith @@ "not supported: "
                            ^ str_of_stdbuf expr.exp_type ~f:Printtyp.type_expr);
                    }
                  in
                  let econstrs, oconstrs, next =
                    call_fold
                      (Map.update_with (*shadowing*) senv pat_senv)
                      expr' sret
                  in
                  let t_annot_rty_opt =
                    (* refinement type annotations on arguments *)
                    let attrs = pat0.pat_attributes in
                    match
                      ( find_val_attrs ~dtenv ~attr_name:"annot_rty" attrs,
                        find_val_attrs ~dtenv ~attr_name:"annot" attrs )
                    with
                    | None, None -> None
                    | Some t, _ | None, Some t -> Some t
                  in
                  ( Set.add
                      (Set.union econstrs_annot econstrs)
                      ([ Sort.Pure ], c0.cont_eff),
                    Set.add
                      (Set.union oconstrs_annot oconstrs)
                      (c0.op_sig, Sort.empty_closed_opsig),
                    f#f_function [ pat ] t_annot_rty_opt
                      ([ next ], [ sret.cont_eff ]) )
              | _ -> failwith "not supported")
          | Texp_function ([], Tfunction_cases func) ->
              let sarg, sret =
                match c0.val_type with
                | Sort.SArrow (sarg, sret) -> (sarg, sret)
                | _ ->
                    failwith @@ "function type expected but " ^ Term.str_of_sort
                    @@ c0.val_type
              in
              let pats, econstrss, oconstrss, nexts, evars =
                List.unzip5
                @@ List.map func.cases ~f:(fun case ->
                       let sarg, econstrs_annot, oconstrs_annot =
                         (* constr on MB type annotations on arguments *)
                         match
                           ( find_val_attrs ~dtenv ~attr_name:"annot_MB"
                               case.c_lhs.pat_attributes,
                             find_val_attrs ~dtenv ~attr_name:"annot"
                               case.c_lhs.pat_attributes )
                         with
                         | None, None -> (sarg, Set.Poly.empty, Set.Poly.empty)
                         | Some t, _ | None, Some t ->
                             let sort_annot = Ast.Rtype.sort_of_val t in
                             if print_log then
                               print_endline
                               @@ sprintf "annot: %s = %s"
                                    (Term.str_of_sort sort_annot)
                                    (Term.str_of_sort sarg);
                             let eqtype s1 s2 =
                               let _map (*ToDo*), econstrs, oconstrs =
                                 Ast.Typeinf.subtype Map.Poly.empty s1 s2
                               in
                               let _map (*ToDo*), econstrs', oconstrs' =
                                 Ast.Typeinf.subtype Map.Poly.empty s2 s1
                               in
                               ( Set.union econstrs econstrs',
                                 Set.union oconstrs oconstrs' )
                             in
                             let econstrs, oconstrs = eqtype sarg sort_annot in
                             (sort_annot, econstrs, oconstrs)
                       in
                       let pat =
                         pattern_of dtenv ~sort:(Some sarg) case.c_lhs
                       in
                       let econstrs, oconstrs, next =
                         call_fold
                           (let pat_senv = Ast.Pattern.senv_of pat sarg in
                            if print_log then (
                              print_endline @@ Term.str_of_sort sarg;
                              print_endline
                              @@ str_of_sort_env_map Term.str_of_sort pat_senv);
                            Map.update_with (*shadowing*) senv pat_senv)
                           case.c_rhs sret
                       in
                       ( pat,
                         Set.union econstrs_annot econstrs,
                         Set.union oconstrs_annot oconstrs,
                         next,
                         sret.cont_eff ))
              in
              let t_annot_rty_opt =
                (* refinement type annotations on arguments *)
                match func.cases with
                | [ case ] -> (
                    match
                      ( find_val_attrs ~dtenv ~attr_name:"annot_rty"
                          case.c_lhs.pat_attributes,
                        find_val_attrs ~dtenv ~attr_name:"annot"
                          case.c_lhs.pat_attributes )
                    with
                    | None, None -> None
                    | Some t, _ | None, Some t -> Some t)
                | _ -> None (*todo*)
              in
              ( Set.Poly.union_list
                  (Set.Poly.singleton ([ Sort.Pure ], c0.cont_eff) :: econstrss),
                Set.Poly.union_list
                @@ Set.Poly.singleton (c0.op_sig, Sort.empty_closed_opsig)
                   (*ToDo*)
                   :: oconstrss,
                f#f_function pats t_annot_rty_opt (nexts, evars) )
          | Texp_construct (_, cd, args) -> (
              match cd.cstr_name with
              | "true" | "false" ->
                  assert (List.is_empty args);
                  ( Set.Poly.singleton ([ Sort.Pure ], c0.cont_eff),
                    Set.Poly.singleton (c0.op_sig, Sort.empty_closed_opsig)
                    (*ToDo*),
                    f#f_const @@ T_bool.make @@ Bool.of_string cd.cstr_name )
              | name -> (
                  let econstrss, oconstrss, nexts_either =
                    List.unzip3 @@ List.map args ~f:(mk_either senv)
                  in
                  let oconstrs_args =
                    Set.Poly.of_list
                    @@ List.map ~f:(Pair.make c0.op_sig)
                    @@ List.filter_map nexts_either ~f:ovar_of_either
                  in
                  let econstrs_args =
                    Set.Poly.singleton
                      ( List.rev (List.filter_map nexts_either ~f:evar_of_either),
                        c0.cont_eff )
                  in
                  let sort_args = List.map nexts_either ~f:sort_of_either in
                  let sort_fun =
                    (*assume its application never causes a temporal effect*)
                    Sort.mk_fun @@ sort_args @ [ c0.val_type ]
                  in
                  let dt_of = function
                    | T_dt.SDT dt -> Some (dt, Datatype.params_of dt)
                    | T_dt.SUS (*ToDo*) (name, params)
                      when Map.Poly.mem dtenv name -> (
                        match DTEnv.look_up_dt dtenv name with
                        | None -> failwith ""
                        | Some dt -> Some (dt, params))
                    | T_dt.SUS _ -> None
                    | _ -> failwith @@ "unknown construct: " ^ name
                  in
                  match
                    dt_of
                      (match c0.val_type with
                      | Sort.SVar _ ->
                          sort_of_type_expr ~lift:true dtenv ~env:expr.exp_env
                            expr.exp_type
                      | s -> s)
                  with
                  | Some (dt, params) ->
                      let sort_cons =
                        let svs =
                          Set.Poly.of_list
                          @@ List.filter_map params ~f:(function
                               | Sort.SVar svar -> Some svar
                               | _ -> None)
                        in
                        Sort.mk_poly svs @@ Sort.mk_fun
                        @@ Datatype.sorts_of_cons_name dt name
                        @ [ c0.val_type ]
                      in
                      if print_log then
                        print_endline
                        @@ sprintf "SDT/SUS: %s <: %s"
                             (Term.str_of_sort sort_cons)
                             (Term.str_of_sort sort_fun);
                      let _map (*ToDo*), econstrs, oconstrs =
                        Ast.Typeinf.subtype Map.Poly.empty (*ToDo*) sort_cons
                          sort_fun
                      in
                      ( Set.Poly.union_list
                          (econstrs_args :: econstrs :: econstrss),
                        Set.Poly.union_list
                          (oconstrs_args :: oconstrs :: oconstrss),
                        f#f_construct dt name nexts_either )
                  | None ->
                      (* reachable here? *)
                      let res =
                        (*ToDo*)
                        ( true,
                          f#f_var (Tvar name, sort_fun),
                          List.map sort_args
                            ~f:(Fn.const Sort.empty_closed_opsig),
                          Sort.empty_closed_opsig,
                          List.map sort_args ~f:(Fn.const Sort.Pure),
                          Sort.Pure )
                      in
                      ( Set.Poly.union_list (econstrs_args :: econstrss),
                        Set.Poly.union_list (oconstrs_args :: oconstrss),
                        f#f_apply false res nexts_either )))
          | Texp_tuple es ->
              let econstrss, oconstrss, nexts_either =
                List.unzip3 @@ List.map es ~f:(mk_either senv)
              in
              let maps, econstrss', oconstrss' =
                let sort_args = List.map nexts_either ~f:sort_of_either in
                let svs =
                  Set.Poly.union_list @@ List.map sort_args ~f:Term.svs_of_sort
                in
                List.unzip3
                @@ List.map2_exn sort_args
                     (T_tuple.let_stuple @@ c0.val_type)
                     ~f:
                       (Ast.Typeinf.subtype
                          (Map.of_set_exn
                          @@ Set.Poly.map svs ~f:(Fn.flip Pair.make None)))
              in
              (ref_id :=
                 let stheta =
                   Map.Poly.map ~f:(Term.subst_sorts_sort !ref_id)
                   @@ Map.Poly.filter_map (Map.force_merge_list maps) ~f:Fn.id
                 in
                 let ref_id =
                   Map.Poly.map ~f:(Term.subst_sorts_sort stheta) !ref_id
                 in
                 Map.force_merge ref_id stheta);
              ( Set.Poly.union_list
                @@ Set.Poly.singleton
                     ( List.rev (List.filter_map nexts_either ~f:evar_of_either),
                       c0.cont_eff )
                   :: (econstrss @ econstrss'),
                Set.Poly.union_list
                @@ (Set.Poly.of_list
                   @@ List.map ~f:(Pair.make c0.op_sig)
                   @@ List.filter_map nexts_either ~f:ovar_of_either)
                   :: (oconstrss @ oconstrss'),
                f#f_tuple nexts_either )
          | Texp_match (e1, cases, _, _) ->
              let econstrs, oconstrs, matched = mk_either senv e1 in
              let ovar1 = ovar_of_either matched in
              let sort1 = sort_of_either matched in
              let evar1 = evar_of_either matched in
              let pats, econstrss, oconstrss, nexts, evars =
                List.unzip5
                @@ List.map ~f:(fun case ->
                       let evar = Sort.mk_fresh_evar () in
                       let pat =
                         pattern_of dtenv ~sort:(Some sort1) case.c_lhs
                       in
                       let econstrs, oconstrs, next =
                         call_fold
                           (Map.update_with (*shadowing*) senv
                           @@ Ast.Pattern.senv_of pat sort1)
                           case.c_rhs
                           { c0 with cont_eff = evar }
                       in
                       (pat, econstrs, oconstrs, next, evar))
                @@ List.concat_map cases ~f:(fun case ->
                       value_case_of case case.c_lhs)
              in
              ( Set.Poly.union_list
                @@ (Set.Poly.of_list
                   @@ List.map evars ~f:(fun evar ->
                          (Option.to_list evar1 @ [ evar ], c0.cont_eff)))
                   :: econstrs :: econstrss,
                Set.Poly.union_list
                @@ (Set.Poly.of_list
                   @@ List.map (Option.to_list ovar1) ~f:(Pair.make c0.op_sig))
                   :: oconstrs :: oconstrss,
                f#f_match matched pats (nexts, evars) )
          | Texp_sequence (e1, e2) ->
              let sort1 = sort_of_expr ~lift:true dtenv e1 in
              let evar1 = Sort.mk_fresh_evar () in
              let econstrs1, oconstrs1, next1 =
                call_fold senv e1
                  { op_sig = c0.op_sig; val_type = sort1; cont_eff = evar1 }
              in
              let evar2 = Sort.mk_fresh_evar () in
              let econstrs2, oconstrs2, next2 =
                call_fold senv e2 { c0 with cont_eff = evar2 }
              in
              ( Set.Poly.union_list
                  [
                    Set.Poly.singleton ([ evar1; evar2 ], c0.cont_eff);
                    econstrs1;
                    econstrs2;
                  ],
                Set.Poly.union_list [ oconstrs1; oconstrs2 ],
                f#f_sequence (next1, sort1, evar1) (next2, evar2) )
          | Texp_unreachable
          | Texp_try (_, _, _)
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
          | Texp_pack _ | Texp_letop _
          | Texp_extension_constructor (_, _)
          | Texp_open (_, _) ->
              failwith @@ "[fold_expr] unsupported expr: " ^ str_of_expr expr)

  let subst_all_opt maps = function
    | Some (next, cont) -> Some (next, Term.subst_cont maps cont)
    | None -> None

  let sel_of dtenv datatypes cons i (ct : core_type) =
    let sel_name = Datatype.mk_name_of_sel cons.cd_name.txt i in
    match ct.ctyp_desc with
    | Ttyp_constr (ret_name, _, arg_cts) -> (
        match
          List.find datatypes
            ~f:(Datatype.name_of_dt >> String.( = ) @@ Path.name ret_name)
        with
        | Some dt ->
            Datatype.mk_insel sel_name (Datatype.name_of_dt dt)
            @@ List.map arg_cts ~f:(sort_of_core_type dtenv)
        | None ->
            Datatype.mk_sel sel_name
            @@ sort_of_core_type ~rectyps:(Some datatypes) dtenv ct)
    | _ ->
        Datatype.mk_sel sel_name
        @@ sort_of_core_type ~rectyps:(Some datatypes) dtenv ct

  let cons_of dtenv datatypes (cons : Typedtree.constructor_declaration) =
    match cons.cd_args with
    | Cstr_tuple cts ->
        let sels = List.mapi cts ~f:(sel_of dtenv datatypes cons) in
        let cons = Datatype.mk_cons cons.cd_name.txt ~sels in
        Debug.print @@ lazy ("[cons_of] " ^ Datatype.str_of_cons cons);
        cons
    | Cstr_record _ ->
        failwith
          "[cons_of] Cstr_record is not supported as an argument of a \
           constructor"
end
