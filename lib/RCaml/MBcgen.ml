(* Simple-type, operation-signature and control-effect inference for OCaml
   programs with algebraic effects, shared by RCaml and EffCaml.

   [Make(..).fold_expr ~f dtenv is_handled senv expr c0] traverses a typed
   expression against an expected computation type [c0] and returns the
   effect and operation-signature constraints it generates (solved by
   [MBcsol.solve]) together with a continuation built from the object [f] --
   one method per construct ([f_ite], [f_assert], [f_annot], ...) -- which the
   caller runs once they are solved, so that RCaml generates refinement
   constraints and EffCaml a CPS translation over the same traversal.  With
   [for_cps_trans] the subeffecting rule also records an operation-signature
   constraint the CPS translation needs.  The module also converts OCaml types
   and patterns to the tree's sorts and patterns, recognises the effect
   primitives by name ([perform], [match_with], [shift], [reset], ...), and
   reads attribute payloads ([find_val_attrs], [find_comp_attrs]).

   Impure [&&]/[||] conditions of [if] and [assert] are distributed over the
   branches rather than typed against a fresh predicate (see [fold_ite]), so
   the continuation of a branch may be invoked several times and must be
   re-entrant. *)

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
  | Tpat_tuple pats ->
      List.fold_left ~init:acc pats ~f:(fun a (_, p) -> bvs p a)
  | Tpat_array (_, pats) ->
      List.fold_left ~init:acc pats ~f:(fun a p -> bvs p a)
  | Tpat_construct (_, _, pats, _) ->
      List.fold_left ~init:acc pats ~f:(fun a p -> bvs p a)
  | Tpat_record (fields, _) ->
      List.fold_left ~init:acc fields ~f:(fun a (_, _, p) -> bvs p a)
  | Tpat_alias (p, id, _, _, _) -> bvs p (id :: acc)
  | Tpat_or (p1, p2, _) -> bvs p1 (bvs p2 acc)
  | _ -> acc

(* Alias patterns [p as y] in match, function and try cases are removed before
   translation: the case [P[q as y] -> e] (guard included) becomes
   [P[q'] -> let y = q'' in e], where [q'] is [q] with each wildcard replaced by
   a fresh variable and [q''] is [q'] read as an expression.  This preserves the
   meaning because the values matched here are immutable: the value [q'] matched
   is structurally equal to the expression rebuilt from its parts.  The pattern
   translation has no alias form, and reading [q as y] as the bare variable [y]
   would make the case match every value.  A case whose alias covers a pattern
   that cannot be rebuilt as an expression (a constant, an or-pattern, a
   record, ...) is left as it is, and the pattern translation refuses it. *)
let alias_part_count = ref 0

let desugar_case_aliases (ts : structure) : structure =
  let mk_var_pat (p : pattern) =
    incr alias_part_count;
    let name = sprintf "alias_part%d" !alias_part_count in
    let id = Ident.create_local name in
    ( {
        p with
        pat_desc =
          Tpat_var
            ( id,
              Location.mknoloc name,
              Types.Uid.internal_not_actually_unique );
      },
      id )
  in
  let ident_expr (p : pattern) env id =
    let name = Ident.name id in
    {
      exp_desc =
        Texp_ident
          ( Path.Pident id,
            Location.mkloc (Longident.Lident name) p.pat_loc,
            {
              Types.val_type = p.pat_type;
              val_kind = Types.Val_reg;
              val_loc = p.pat_loc;
              val_attributes = [];
              val_uid = Types.Uid.internal_not_actually_unique;
            } );
      exp_loc = p.pat_loc;
      exp_extra = [];
      exp_type = p.pat_type;
      exp_env = env;
      exp_attributes = [];
    }
  in
  let exception Unsupported in
  (* [strip in_alias env p] is [p] without aliases, wildcards under an alias
     replaced by fresh variables, together with the bindings [(y, q'')] the
     removed aliases stand for; [expr_of] rebuilds a stripped pattern under an
     alias as an expression *)
  let rec expr_of env (p : pattern) =
    let desc =
      match p.pat_desc with
      | Tpat_var (id, _, _) -> (ident_expr p env id).exp_desc
      | Tpat_construct (lid, cd, ps, _) ->
          Texp_construct (lid, cd, List.map ps ~f:(expr_of env))
      | Tpat_tuple ps ->
          Texp_tuple (List.map ps ~f:(fun (l, p) -> (l, expr_of env p)))
      | _ -> raise Unsupported
    in
    {
      exp_desc = desc;
      exp_loc = p.pat_loc;
      exp_extra = [];
      exp_type = p.pat_type;
      exp_env = env;
      exp_attributes = [];
    }
  in
  let rec strip in_alias env (p : pattern) =
    match p.pat_desc with
    | Tpat_any when in_alias -> (fst (mk_var_pat p), [])
    | Tpat_alias (q, y, _, _, _) ->
        let q', binds = strip true env q in
        (q', binds @ [ (y, q', expr_of env q') ])
    | Tpat_construct (lid, cd, ps, ann) ->
        let ps', bindss = List.unzip @@ List.map ps ~f:(strip in_alias env) in
        ( { p with pat_desc = Tpat_construct (lid, cd, ps', ann) },
          List.concat bindss )
    | Tpat_tuple ps ->
        let ps', bindss =
          List.unzip
          @@ List.map ps ~f:(fun (l, p) ->
              let p', binds = strip in_alias env p in
              ((l, p'), binds))
        in
        ({ p with pat_desc = Tpat_tuple ps' }, List.concat bindss)
    | Tpat_var _ | Tpat_any -> (p, [])
    | _ -> if in_alias then raise Unsupported else (p, [])
  in
  let wrap binds (body : expression) =
    List.fold_right binds ~init:body ~f:(fun (y, (q' : pattern), e) body ->
        let vb =
          {
            vb_pat =
              {
                q' with
                pat_desc =
                  Tpat_var
                    ( y,
                      Location.mknoloc (Ident.name y),
                      Types.Uid.internal_not_actually_unique );
                pat_extra = [];
                pat_attributes = [];
              };
            vb_expr = e;
            vb_rec_kind = Value_rec_types.Dynamic;
            vb_attributes = [];
            vb_loc = body.exp_loc;
          }
        in
        { body with exp_desc = Texp_let (Nonrecursive, [ vb ], body) })
  in
  let has_alias (p : pattern) =
    let found = ref false in
    let it =
      {
        Tast_iterator.default_iterator with
        pat =
          (fun (type k) sub (p : k general_pattern) ->
            (match p.pat_desc with Tpat_alias _ -> found := true | _ -> ());
            Tast_iterator.default_iterator.pat sub p);
      }
    in
    it.pat it p;
    !found
  in
  let value_case (c : value case) : value case =
    if not (has_alias c.c_lhs) then c
    else
      try
        let env = c.c_rhs.exp_env in
        let lhs, binds = strip false env c.c_lhs in
        {
          c with
          c_lhs = lhs;
          c_guard = Option.map c.c_guard ~f:(wrap binds);
          c_rhs = wrap binds c.c_rhs;
        }
      with Unsupported -> c
  in
  let computation_case (c : computation case) : computation case =
    match c.c_lhs.pat_desc with
    | Tpat_value arg ->
        let c' = value_case { c with c_lhs = (arg :> pattern) } in
        if phys_equal c'.c_lhs (arg :> pattern) then c
        else { c' with c_lhs = as_computation_pattern c'.c_lhs }
    | _ -> c
  in
  let expr sub e =
    let e = Tast_mapper.default.expr sub e in
    match e.exp_desc with
    | Texp_match (e1, cases, eff_cases, partial) ->
        {
          e with
          exp_desc =
            Texp_match
              (e1, List.map cases ~f:computation_case, eff_cases, partial);
        }
    | Texp_function (params, Tfunction_cases fc) ->
        {
          e with
          exp_desc =
            Texp_function
              ( params,
                Tfunction_cases
                  { fc with cases = List.map fc.cases ~f:value_case } );
        }
    | Texp_try (e1, cases, eff_cases) ->
        {
          e with
          exp_desc = Texp_try (e1, List.map cases ~f:value_case, eff_cases);
        }
    | _ -> e
  in
  let m = { Tast_mapper.default with expr } in
  m.structure m ts

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
        List.iter ~f:(function _, Arg a -> expr a | _ -> ()) args
    | Texp_ifthenelse (cond, then_expr, else_expr) ->
        expr cond;
        expr then_expr;
        Option.iter else_expr ~f:expr
    | _ -> ()
  in

  expr e;
  !found

module Config = struct
  (* Which operations are answer-type polymorphic (ATP): called like a
     function, with no answer types, and handled only by tail-resumptive
     clauses ([fun k -> let x = N in continue k x], [k] not free in [N]),
     whose body [N] is typed under the handling construct's signature
     (Sekiyama, Dal Lago, Unno, "On Higher-Order Model Checking of Effectful
     Answer-Type-Polymorphic Programs", OOPSLA 2025).  [Off]: none, as in
     Kawamata et al., POPL 2024; EffCaml decides its own with
     [for_cps_trans].  [Annotated]: an operation is ATP iff every [perform] of
     it in the file is written [perform_atp], so a file with no [perform_atp]
     is generated exactly as under [Off].  The per-operation decision is
     [Make(..).is_atp_operation]; an inferring mode would fill the same
     decision from the constraints instead of from the annotation. *)
  type atp_operations = Off | Annotated [@@deriving yojson]

  type t = {
    verbose : bool; [@default false]
    for_cps_trans : bool; [@default false]
    atp_operations : atp_operations; [@default Off]
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "MBcgen"

    (* a leaf: no nested config to load *)
    let instantiate = Or_error.return
  end)
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
           :: List.map es ~f:(function _, Arg e -> str_of_expr e | _ -> "")
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
    | Texp_atomic_loc _ -> "Texp_atomic_loc"

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
        T_tuple.STuple
          (List.map elems ~f:(snd >> sort_of_core_type ~rectyps dtenv))
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
        T_tuple.STuple
          (List.map elems ~f:(snd >> sort_of_type_expr ~lift ~env dtenv))
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
               snd >> pattern_of dtenv ~sort:(Some s)))
    | Tpat_tuple _, _ ->
        failwith
        @@ sprintf "[pattern_of] %s needs to be a tuple type"
        @@ Term.str_of_sort sort
    | Tpat_alias ({ pat_desc = Tpat_any; _ }, name, _, _, _), _ ->
        Ast.Pattern.PVar (Tvar (Ident.name name), sort)
    | Tpat_alias (_, name, _, _, _), _ ->
        (* the pattern language has no alias form, and reading [p as y] as the
           variable [y] would match values [p] rejects; the aliases of match,
           function and try cases are removed by [desugar_case_aliases], so
           only an alias elsewhere (a let or parameter pattern) or over a
           pattern that cannot be rebuilt as an expression reaches here *)
        failwith
        @@ sprintf
             "[pattern_of] unsupported pattern: an alias (... as %s) over a \
              pattern other than _ in this position"
             (Ident.name name)
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
    Ast.Rtype.(
      is_fsym name || is_psym name || is_unop name || is_binop name
      || is_stdlib_model name)

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

  (* [is_total_pure_expr e] holds only if evaluating [e] can neither fail,
     diverge, nor perform an effect: variables, constants, nullary
     constructors and total primitives (comparisons, [+], [-], [*], [not],
     [&&], [||], ...) applied to such expressions.  Division and [mod] are
     excluded because they can raise.  Used to keep the strict typing of
     [&&]/[||] (see [Ast.Rtype.of_binop]) when short-circuiting cannot be
     observed, since the [if]-desugaring is much more expensive to solve. *)
  let rec is_total_pure_expr e =
    match e.exp_desc with
    | Texp_ident _ | Texp_constant _ | Texp_function _ -> true
    | Texp_construct (_, _, args) -> List.for_all args ~f:is_total_pure_expr
    | Texp_apply (e, args) ->
        is_
          (fun s ->
            Ast.Rtype.is_psym s || Ast.Rtype.is_unop s || Ast.Rtype.is_binop s
            ||
            match s with
            | "Stdlib.+" | "Stdlib.-" | "Stdlib.*" | "Stdlib.~-" | "Stdlib.abs"
            | "Stdlib.+." | "Stdlib.-." | "Stdlib.*." | "Stdlib.float_of_int" ->
                true
            | _ -> false)
          e
        && List.for_all args ~f:(function
          | _, Arg e -> is_total_pure_expr e
          | _ -> false)
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

  (* [atp_ops str] reads the annotated ATP reading off a typed structure: it
     returns the constructors that occur as the argument of [perform_atp] and
     never as the argument of [perform] or [raise] anywhere in [str]
     (functor bodies and local modules included).  A constructor performed
     both ways is not ATP; each such constructor is reported once through
     [Debug.print].  It depends on [str] only. *)
  let atp_ops (str : structure) : string Set.Poly.t =
    let atp = ref Set.Poly.empty and atm = ref Set.Poly.empty in
    let iterator =
      {
        Tast_iterator.default_iterator with
        expr =
          (fun self e ->
            (match e.exp_desc with
            | Texp_apply
                (e_fun, [ (_, Arg { exp_desc = Texp_construct (_, cd, _); _ }) ])
              ->
                if is_ is_perform_atp e_fun then atp := Set.add !atp cd.cstr_name
                else if is_ (fun x -> is_perform x || is_raise x) e_fun then
                  atm := Set.add !atm cd.cstr_name
            | _ -> ());
            Tast_iterator.default_iterator.expr self e);
      }
    in
    iterator.structure iterator str;
    let mixed = Set.inter !atp !atm in
    Set.iter mixed ~f:(fun name ->
        Debug.print
        @@ lazy
             (sprintf
                "operation %s is performed both by perform_atp and by \
                 perform or raise: it is read as answer-type modifying"
                name));
    Set.diff !atp mixed

  (* The operations the current file reads as ATP: empty under [Off] and
     under [for_cps_trans] (EffCaml's own reading), else set by
     [set_atp_operations] once per file before its first item. *)
  let atp_operation_names : string Set.Poly.t ref = ref Set.Poly.empty

  let set_atp_operations (str : structure) =
    atp_operation_names :=
      match config.atp_operations with
      | Off -> Set.Poly.empty
      | Annotated -> atp_ops str

  (* The per-operation ATP decision every rule of the generator reads.  An
     operation it calls ATP has every perform generated as a call with a pure
     control effect and every clause handling it required to be
     tail-resumptive; one it calls ATM is generated exactly as under [Off]. *)
  let is_atp_operation name = Set.mem !atp_operation_names name

  (* [mentions id e]: the identifier [id] occurs anywhere in [e].  Typed-tree
     identifiers are unique (by stamp), so an occurrence is a free occurrence
     of the binding [id] names; no binder can shadow it. *)
  let mentions (id : Ident.t) (e : expression) =
    let found = ref false in
    let iterator =
      {
        Tast_iterator.default_iterator with
        expr =
          (fun self e ->
            (match e.exp_desc with
            | Texp_ident (Path.Pident id', _, _) when Ident.same id id' ->
                found := true
            | _ -> ());
            if not !found then Tast_iterator.default_iterator.expr self e);
      }
    in
    iterator.expr iterator e;
    !found

  (* [tail_resumptive_body k body]: [Some n] when the clause body [body] is
     [continue k e] with [k] not in [e], possibly under [let]s and sequences
     whose bound expressions do not mention [k], and [n] is [body] with that
     [continue k e] replaced by [e]; so [body] behaves as
     [let x = n in continue k x] with [k] not free in [n].  [None] otherwise.
     The test is syntactic and sound: a [k] anywhere but in that one tail
     position makes it fail. *)
  let rec tail_resumptive_body (k : Ident.t) (body : expression) =
    match body.exp_desc with
    | Texp_apply (e_cont, [ (_, Arg e_k); (_, Arg e_arg) ])
      when is_ is_continue e_cont
           && (match e_k.exp_desc with
              | Texp_ident (Path.Pident k', _, _) -> Ident.same k k'
              | _ -> false)
           && not (mentions k e_arg) ->
        Some e_arg
    | Texp_let (flag, vbs, e) ->
        if List.exists vbs ~f:(fun vb -> mentions k vb.vb_expr) then None
        else
          Option.map (tail_resumptive_body k e) ~f:(fun n ->
              { body with exp_desc = Texp_let (flag, vbs, n); exp_type = n.exp_type })
    | Texp_sequence (e1, e2) ->
        if mentions k e1 then None
        else
          Option.map (tail_resumptive_body k e2) ~f:(fun n ->
              { body with exp_desc = Texp_sequence (e1, n); exp_type = n.exp_type })
    | _ -> None

  (* The label of a call written [(f a1 ... an [@copy lbl])]: [Some lbl] when
     [attrs] carry a [copy] attribute whose payload is one identifier.  The
     label names the copy of [f]'s refinement predicates this call makes, for
     the lemmas and properties that speak about it; whether the attribute
     stands on a call of a top-level function, and whether the label is
     unique, is the constraint generator's to check and report. *)
  let copy_label_of_attrs (attrs : Parsetree.attributes) =
    List.find_map attrs ~f:(fun attr ->
        if String.(attr.attr_name.txt = "copy") then
          match attr.attr_payload with
          | PStr
              [
                {
                  pstr_desc =
                    Pstr_eval
                      ({ pexp_desc = Pexp_ident { txt = Lident l; _ }; _ }, _);
                  _;
                };
              ] ->
              Some l
          | _ -> None
        else None)

  let rec fold_expr ~f dtenv is_handled senv expr c0 =
    let call_fold = fold_expr ~f dtenv is_handled in
    let call_fold_handled = fold_expr ~f dtenv true in
    let mk_either senv e =
      let sort = sort_of_expr ~lift:true dtenv e in
      match e.exp_desc with
      | Texp_ident (p, _, _)
        when (Fn.non is_interpreted @@ Path.name p)
             && (Fn.non is_keyword @@ Path.name p)
             && not (f#has_scheme p) ->
          (* if [Path.name p] is a variable; a variable with an effect scheme
             is typed as an expression, so that its occurrence is an
             instance with its own continuation (the [Texp_ident] arm) *)
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
    (* Conditions of [if] and [assert] that are impure [&&]/[||] applications
       are distributed over the branches instead of being typed against a
       fresh predicate:
         if (a && b) then t else f  =  if a then (if b then t else f) else f
         if (a || b) then t else f  =  if a then t else (if b then t else f)
         assert (a && b)            =  if a then assert b else assert false
         assert (a || b)            =  if a then () else assert b
       Eliminating the condition's predicate afterwards copies the nested
       conditions' predicates and is exponential in the nesting depth.
       A branch's [next] may therefore be
       invoked in several branches. *)
    let is_and_op op =
      is_ (function "Stdlib.&&" | "Stdlib.&" -> true | _ -> false) op
    in
    let rec fold_ite senv e1 ((_, evar2) as then_) else_opt cont =
      match e1.exp_desc with
      | Texp_apply (op, [ (_, Arg e11); (_, Arg e12) ])
        when is_ Ast.Rtype.is_binop op && not (is_total_pure_expr e12) ->
          let evar = Sort.mk_fresh_evar () in
          let econstrs, oconstrs, next =
            fold_ite senv e12 then_ else_opt evar
          in
          let econstrs', oconstrs', next' =
            if is_and_op op then fold_ite senv e11 (next, evar) else_opt cont
            else fold_ite senv e11 then_ (Some (next, evar)) cont
          in
          (Set.union econstrs econstrs', Set.union oconstrs oconstrs', next')
      | _ ->
          let evar1 = Sort.mk_fresh_evar () in
          let econstrs1, oconstrs1, next1 =
            call_fold senv e1
              {
                op_sig = c0.op_sig;
                val_type = sort_of_expr ~lift:true dtenv e1;
                cont_eff = evar1;
              }
          in
          let econstrs_seq =
            match else_opt with
            | None -> Set.Poly.singleton ([ evar1; evar2 ], cont)
            | Some (_, evar3) ->
                Set.Poly.of_list
                  [ ([ evar1; evar2 ], cont); ([ evar1; evar3 ], cont) ]
          in
          ( Set.union econstrs1 econstrs_seq,
            oconstrs1,
            f#f_ite (next1, evar1) then_ else_opt )
    in
    let rec fold_assert senv e cont =
      match e.exp_desc with
      | Texp_construct (_, cd, []) when String.(cd.cstr_name = "false") ->
          let evar1 = Sort.mk_fresh_evar () in
          ( Set.Poly.singleton ([ evar1 ], cont),
            Set.Poly.empty,
            f#f_assert (None, evar1) )
      | Texp_apply (op, [ (_, Arg e1); (_, Arg e2) ])
        when is_ Ast.Rtype.is_binop op && not (is_total_pure_expr e2) ->
          let evar2 = Sort.mk_fresh_evar () in
          let econstrs2, oconstrs2, next2 = fold_assert senv e2 evar2 in
          let evar3 = Sort.mk_fresh_evar () in
          let econstrs1, oconstrs1, next =
            if is_and_op op then
              fold_ite senv e1 (next2, evar2)
                (Some (f#f_assert (None, evar3), evar3))
                cont
            else
              fold_ite senv e1
                (f#f_const (Datatype.mk_unit ()), evar3)
                (Some (next2, evar2))
                cont
          in
          ( Set.Poly.union_list
              [
                Set.Poly.singleton ([ Sort.Pure ], evar3); econstrs1; econstrs2;
              ],
            Set.Poly.union_list
              [
                Set.Poly.singleton (c0.op_sig, Sort.empty_closed_opsig);
                oconstrs1;
                oconstrs2;
              ],
            next )
      | _ ->
          let evar1 = Sort.mk_fresh_evar () in
          let econstrs, oconstrs, next =
            call_fold senv e
              {
                op_sig = c0.op_sig;
                val_type = sort_of_expr ~lift:true dtenv e;
                cont_eff = evar1;
              }
          in
          ( Set.add econstrs ([ evar1 ], cont),
            oconstrs,
            f#f_assert (Some next, evar1) )
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
          | Texp_ident (p, _, _) when f#has_scheme p ->
              (* An occurrence of a binding that has an effect scheme: [f]
                 copies the scheme's constraints under fresh variables and
                 returns the copy's sort for the bound name, the copied
                 constraints, and the continuation that types this instance.
                 The occurrence is then related to [c0] as an ordinary
                 variable's instantiated sort is, its sort variables being
                 the instance's unknowns. *)
              let x_sort, econstrs0, oconstrs0, next =
                f#f_scheme_instance p
              in
              let map, econstrs, oconstrs =
                subeff
                  (Map.of_set_exn
                  @@ Set.Poly.map ~f:(Fn.flip Tuple2.create None)
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
              (* the instance's sort variables bound here are recorded in
                 [ref_id] only, as an ordinary occurrence's are: they are
                 substituted into the copied constraints, so that the
                 solver does not bind them a second time *)
              let sub = Map.Poly.filter_map map ~f:Fn.id in
              let econstrs0 =
                Set.Poly.map econstrs0 ~f:(fun (effs, eff) ->
                    ( List.map effs ~f:(Term.subst_sorts_cont sub),
                      Term.subst_sorts_cont sub eff ))
              in
              let oconstrs0 =
                Set.Poly.map oconstrs0 ~f:(fun (o1, o2) ->
                    (Term.subst_sorts_opsig sub o1, Term.subst_sorts_opsig sub o2))
              in
              ( Set.union econstrs0 econstrs,
                Set.union oconstrs0 oconstrs,
                next )
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
                  @@ Set.Poly.map ~f:(Fn.flip Tuple2.create None)
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
                else
                  let next =
                    f#f_var (is_handled, !rec_vars)
                      (Ast.Ident.Tvar name, x_sort (*c0.val_type*))
                  in
                  (* the head of a labelled call: its instantiation is the
                     labelled copy *)
                  match copy_label_of_attrs expr.exp_attributes with
                  | Some lbl -> f#f_copy_label lbl next
                  | None -> next )
          | Texp_apply (e, [ (_, Arg e') ]) when is_ is_shift0 e -> (
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
          | Texp_apply (e, [ (_, Arg e') ]) when is_ is_shift e -> (
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
          | Texp_apply (e, [ (_, Arg e') ]) when is_ is_reset e -> (
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
          | Texp_apply (e, [ (_, Arg e') ])
            when is_ (fun x -> is_perform x || is_perform_atp x || is_raise x) e
            -> (
              match e'.exp_desc with
              | Texp_construct (_, cd, args) ->
                  let econstrss, oconstrss, nexts_either =
                    List.unzip3 @@ List.map args ~f:(mk_either senv)
                  in
                  let is_atp =
                    match config.atp_operations with
                    | Off ->
                        (* EffCaml reads each [perform_atp] call as ATP *)
                        config.for_cps_trans && is_ is_perform_atp e
                    | Annotated ->
                        (* the file's per-operation decision: every perform
                           of an ATP operation is a [perform_atp] *)
                        is_atp_operation cd.cstr_name
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
                       @@ List.map ~f:(Tuple2.create c0.op_sig)
                       @@ opsig_op
                          :: List.filter_map nexts_either ~f:ovar_of_either)
                       :: oconstrss,
                    f#f_perform is_atp e.exp_attributes
                      (cd.cstr_name, c0.val_type, op_cont)
                      nexts_either )
              | _ -> failwith "perform")
          | Texp_apply
              ( e,
                [ (_, Arg e_body_fun); (_, Arg e_body_arg); (_, Arg e_handler) ]
              )
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
                    (* the third component, the effect cases, is empty here:
                       [EffectSyntax.desugar] rewrites every match with effect
                       cases into a handler application before typing, so an
                       [effc] body that had one is no longer a match *)
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
                                (* A [_] parameter gets a prefixed fresh
                                   binder, which is not fresh against the
                                   program's own names: it must avoid the
                                   variables in scope and its sibling
                                   parameters, or it would shadow one. *)
                                let taken v =
                                  Map.Poly.mem senv' v
                                  || List.exists pat_params ~f:(function
                                    | Ast.Pattern.PVar (x, _) ->
                                        Ast.Ident.tvar_equal x v
                                    | _ -> false)
                                in
                                List.unzip
                                @@ List.map pat_params ~f:(function
                                  | Ast.Pattern.PAny sort ->
                                      ( Ast.Ident.mk_fresh_tvar_avoiding
                                          ~prefix:"dummy" ~taken ()
                                        (*dummy*),
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
                                        ~attr_name:"annot_MB" pat.pat_attributes,
                                      find_val_attrs ~dtenv ~attr_name:"annot"
                                        pat.pat_attributes )
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
                                Option.map s_opt ~f:(Tuple2.create x))
                            @@ List.zip_exn x_op_params s_annot_opts
                          in
                          Map.update_with (*shadowing*) senv' pat_senv
                        in
                        match case.c_rhs.exp_desc with
                        | Texp_construct
                            ( _,
                              { cstr_name = "Some"; _ },
                              [
                                {
                                   exp_desc = Texp_function (k_arg :: args, body);
                                   _;
                                 };
                              ] )
                          when (match config.atp_operations with
                               | Off -> false
                               | Annotated -> is_atp_operation op_name) -> (
                            (* A clause for an ATP operation (the annotated
                               reading).  It must be tail-resumptive; its
                               resumed continuation is then not typed: the
                               clause steps to [let x = N in] the handled
                               computation resumed with [x], which is what
                               resuming does, so only [N] is generated,
                               typed pure under a signature contained in the
                               handling construct's, and the operation's
                               entry is the function sort from its
                               parameters to [N]'s value sort.  A clause that
                               discards, stores or re-enters [k] has no
                               typing here: the operation is refused. *)
                            let n_opt =
                              match (args, body) with
                              | [], Tfunction_body e ->
                                  tail_resumptive_body k_arg.fp_param e
                              | _ -> None
                            in
                            match n_opt with
                            | None ->
                                Common.Refusal.refuse
                                  "RCaml does not support an \
                                   answer-type-polymorphic operation handled \
                                   by a clause that does not resume its \
                                   continuation in tail position: every \
                                   perform of %s is perform_atp, and its \
                                   clause is not of the form [fun k -> let x \
                                   = N in continue k x] with k not in N"
                                  op_name
                            | Some e_n ->
                                let k_pat =
                                  match k_arg.fp_kind with
                                  | Tparam_pat k_pat -> k_pat
                                  | _ -> failwith "handling @ atp1"
                                in
                                let s_arity =
                                  match
                                    sort_of_type_expr ~lift:true
                                      ~env:k_pat.pat_env dtenv k_pat.pat_type
                                  with
                                  | T_dt.SDT dt
                                    when String.(
                                           Datatype.name_of dt = "continuation")
                                    -> (
                                      match Datatype.params_of dt with
                                      | [ s_arity; _s_ans ] -> s_arity
                                      | _ -> failwith "handling @ atp2")
                                  | _ -> failwith "handling @ atp3"
                                in
                                Debug.print
                                @@ lazy
                                     (sprintf "ATP clause for %s"
                                        (Ast.Pattern.str_of pat));
                                let op_sig_gen =
                                  Sort.mk_fresh_empty_open_opsig ()
                                in
                                let c_n =
                                  Sort.
                                    {
                                      op_sig = op_sig_gen;
                                      val_type = s_arity;
                                      cont_eff = Sort.Pure;
                                    }
                                in
                                let econstrs, oconstrs, next =
                                  call_fold senv'' e_n c_n
                                in
                                let op_sort =
                                  (Sort.mk_eff_fun s_op_params
                                     Sort.
                                       {
                                         op_sig = Sort.empty_closed_opsig;
                                         val_type = s_arity;
                                         cont_eff = Sort.Pure;
                                       })
                                    .val_type
                                in
                                ( econstrs,
                                  (* [N]'s operations are the handling
                                     construct's *)
                                  Set.add oconstrs (c0.op_sig, op_sig_gen),
                                  next,
                                  op_name,
                                  ATPHandler,
                                  op_sort,
                                  ( x_op_params,
                                    s_op_params,
                                    None,
                                    Sort.SArrow (s_arity, c_n) (* not read *),
                                    c_n ) ))
                        | Texp_construct
                            ( _,
                              { cstr_name = "Some"; _ },
                              [
                                ({
                                   exp_desc = Texp_function (k_arg :: args, body);
                                   _;
                                 } as exp0);
                              ] ) ->
                            let is_atp =
                              let is_cont_app e =
                                match e.exp_desc with
                                | Texp_apply
                                    (e, [ (_, Arg k); (_, Arg arg) (*ToDo*) ])
                                  ->
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
                              && List.is_empty args (* no handler parameters *)
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
                              | Tfunction_cases _ -> failwith "handling @ eff6"
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
                                sort_of_type_expr ~lift:true ~env:k_pat.pat_env
                                  dtenv k_pat.pat_type
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
                                                 Sort.mk_fresh_empty_open_opsig
                                                   ());
                                            val_type = s_ans;
                                            cont_eff =
                                              (if is_atp then Sort.Pure
                                               else if true then
                                                 Sort.mk_fresh_evar ()
                                               else
                                                 Sort.Eff
                                                   ( Sort.mk_fresh_triple (),
                                                     Sort.mk_fresh_triple () ));
                                          }
                                      in
                                      (s_arity, c_ini)
                                  | _ -> failwith "handling @ eff8")
                              | _ -> failwith "handling @ eff9"
                            in
                            let s_cont = Sort.SArrow (s_arity, c_ini) in
                            if false then
                              print_endline
                              @@ sprintf "s_cont: %s" (Term.str_of_sort s_cont);
                            let k_cont_opt, senv_clause =
                              match
                                pattern_of dtenv k_pat ~sort:(Some s_cont)
                              with
                              | PAny _ -> (None, senv'')
                              | PVar (k, _) ->
                                  ( Some k,
                                    Map.Poly.add_exn ~key:k ~data:s_cont senv''
                                  )
                              | _ -> failwith "handling @ eff10"
                            in
                            let e_clause =
                              {
                                exp0 with
                                exp_desc = Texp_function (args, body);
                                exp_type =
                                  (match Types.get_desc exp0.exp_type with
                                  | Types.Tarrow (_, _, ty_body, _) -> ty_body
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
                                       op_sig = Sort.empty_closed_opsig (*ToDo*);
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
                                    (* as for an operation's parameters: a
                                       [_] binder avoids the variables in
                                       scope and its siblings *)
                                    let taken v =
                                      Map.Poly.mem senv v
                                      || List.exists pat_params ~f:(function
                                        | Ast.Pattern.PVar (x, _) ->
                                            Ast.Ident.tvar_equal x v
                                        | _ -> false)
                                    in
                                    List.unzip
                                    @@ List.map pat_params ~f:(function
                                      | Ast.Pattern.PAny sort ->
                                          ( Ast.Ident.mk_fresh_tvar_avoiding
                                              ~prefix:"dummy" ~taken ()
                                            (*dummy*),
                                            sort )
                                      | Ast.Pattern.PVar b -> b
                                      | _ -> failwith "handling @ exn3") )
                              | Ast.Pattern.(PAny _ | PVar _) ->
                                  failwith
                                    "write out all exception clauses explicitly"
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
                              (x_exn_params, s_exn_params, None, s_cont, c_fin)
                            ))
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
                    ( econstrs,
                      oconstrs,
                      f#f_var (false, Set.Poly.empty) (x_r, s_body),
                      x_r,
                      c_r )
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
                          (* the return clause's binder must not shadow a
                             variable its body may mention *)
                          Ast.Ident.mk_fresh_tvar_avoiding ~prefix:"dummy"
                            ~taken:(Map.Poly.mem senv) () (*dummy*)
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
                      Texp_apply (e_body_fun, [ (Nolabel, Arg e_body_arg) ]);
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
                       (Bool.to_string !is_hrec)
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
          | Texp_apply (e, [ (_, Arg e') ]) when is_ is_continue e -> (
              match sort_of_expr ~lift:true dtenv e' with
              | T_dt.SDT dt when String.(Datatype.name_of dt = "continuation")
                ->
                  call_fold senv e' c0
              | _ -> failwith "continue")
          | Texp_apply (e, [ (_, Arg e') ]) when is_ is_unif e ->
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
          | Texp_apply (e, [ (_, Arg e1); (_, Arg e2) ])
            when is_ Ast.Rtype.is_binop e && not (is_total_pure_expr e2) ->
              (* short-circuit: e1 && e2 = if e1 then e2 else false,
                 e1 || e2 = if e1 then true else e2 *)
              (* OCaml's [&&] and [||] short-circuit: type [e1 && e2] as
                 [if e1 then e2 else false] and [e1 || e2] as
                 [if e1 then true else e2], mirroring the Texp_ifthenelse arm
                 below, instead of as a strict binary function *)
              let is_and =
                is_ (function "Stdlib.&&" | "Stdlib.&" -> true | _ -> false) e
              in
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
              (* the constant branch, typed as the Texp_construct arm does *)
              let evar3 = Sort.mk_fresh_evar () in
              let econstrs3 = Set.Poly.singleton ([ Sort.Pure ], evar3) in
              let oconstrs3 =
                Set.Poly.singleton (c0.op_sig, Sort.empty_closed_opsig)
              in
              let next3 = f#f_const @@ T_bool.make (not is_and) in
              let then_, else_ =
                if is_and then ((next2, evar2), (next3, evar3))
                else ((next3, evar3), (next2, evar2))
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
                f#f_ite (next1, evar1) then_ @@ Some else_ )
          | Texp_apply (e1, es) ->
              assert (not @@ is_ is_keyword e1);
              let econstrss, oconstrss, nexts_either =
                List.unzip3
                @@ List.map es ~f:(function
                  | _label, Arg e -> mk_either senv e
                  | _label, _ -> failwith "default arg not supported")
              in
              let ovars', evars', sort_fun =
                Sort.of_args_ret
                  (List.map nexts_either ~f:sort_of_either)
                  c0.val_type
                (*sort_of_expr dtenv e1*)
              in
              let ovar1 = Sort.mk_fresh_empty_open_opsig () in
              let evar1 = Sort.mk_fresh_evar () in
              (* a call's [copy] label goes to its head, whose instantiation
                 makes the copy the label names *)
              let e1 =
                match (e1.exp_desc, copy_label_of_attrs expr.exp_attributes) with
                | Texp_ident _, Some _ ->
                    {
                      e1 with
                      exp_attributes =
                        List.filter expr.exp_attributes ~f:(fun attr ->
                            String.(attr.attr_name.txt = "copy"))
                        @ e1.exp_attributes;
                    }
                | _ -> e1
              in
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
                   @@ List.map ~f:(Tuple2.create c0.op_sig)
                   @@ (ovar1 :: ovars')
                   @ List.filter_map nexts_either ~f:ovar_of_either)
                   :: oconstrs1 :: oconstrss,
                f#f_apply
                  (is_pure e1.exp_desc, next1, ovars', ovar1, evars', evar1)
                  nexts_either )
          | Texp_ifthenelse (e1, e2, e3_opt) ->
              let evar2 = Sort.mk_fresh_evar () in
              let econstrs2, oconstrs2, next2 =
                call_fold senv e2 { c0 with cont_eff = evar2 }
              in
              let econstrs3, oconstrs3, else_opt =
                match e3_opt with
                | None -> (Set.Poly.empty, Set.Poly.empty, None)
                | Some e3 ->
                    let evar3 = Sort.mk_fresh_evar () in
                    let econstrs3, oconstrs3, next3 =
                      call_fold senv e3 { c0 with cont_eff = evar3 }
                    in
                    (econstrs3, oconstrs3, Some (next3, evar3))
              in
              let econstrs1, oconstrs1, next =
                fold_ite senv e1 (next2, evar2) else_opt c0.cont_eff
              in
              ( Set.Poly.union_list [ econstrs1; econstrs2; econstrs3 ],
                Set.Poly.union_list [ oconstrs1; oconstrs2; oconstrs3 ],
                next )
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
          | Texp_assert (e, _) -> fold_assert senv e c0.cont_eff
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
                        { op_sig = c0.op_sig; val_type = sort; cont_eff = evar }
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
                    let pat = pattern_of dtenv ~sort:(Some sarg) case.c_lhs in
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
                    @@ List.map ~f:(Tuple2.create c0.op_sig)
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
                      when Option.is_some (DTEnv.look_up_dt dtenv name) -> (
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
                          f#f_var (false, Set.Poly.empty) (Tvar name, sort_fun),
                          List.map sort_args
                            ~f:(Fn.const Sort.empty_closed_opsig),
                          Sort.empty_closed_opsig,
                          List.map sort_args ~f:(Fn.const Sort.Pure),
                          Sort.Pure )
                      in
                      ( Set.Poly.union_list (econstrs_args :: econstrss),
                        Set.Poly.union_list (oconstrs_args :: oconstrss),
                        f#f_apply res nexts_either )))
          | Texp_tuple es ->
              let econstrss, oconstrss, nexts_either =
                List.unzip3 @@ List.map es ~f:(snd >> mk_either senv)
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
                          @@ Set.Poly.map svs ~f:(Fn.flip Tuple2.create None)))
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
                   @@ List.map ~f:(Tuple2.create c0.op_sig)
                   @@ List.filter_map nexts_either ~f:ovar_of_either)
                   :: (oconstrss @ oconstrss'),
                f#f_tuple nexts_either )
          | Texp_match (_, _, _ :: _, _) ->
              (* effect cases ([effect P, k -> e], OCaml 5.3) handle what the
                 scrutinee performs; the arm below types the scrutinee as a
                 plain computation, so reading such a match there would
                 translate it as if its handler were absent *)
              failwith
              @@ "[fold_expr] a match with effect cases is not supported here: "
              ^ str_of_expr expr
          | Texp_try (_, _, _ :: _) ->
              failwith
              @@ "[fold_expr] a try with effect cases is not supported here: "
              ^ str_of_expr expr
          | Texp_match (e1, cases, [], _) ->
              let econstrs, oconstrs, matched = mk_either senv e1 in
              let ovar1 = ovar_of_either matched in
              let sort1 = sort_of_either matched in
              let evar1 = evar_of_either matched in
              let pats, econstrss, oconstrss, nexts, evars =
                List.unzip5
                @@ List.map ~f:(fun case ->
                    (* a case is read by its pattern alone, so a guard would
                       be dropped and its case read as taken whenever the
                       pattern matches *)
                    if Option.is_some case.c_guard then
                      failwith
                      @@ "[fold_expr] a guard on a match case is not supported \
                          here: "
                      ^ str_of_expr expr;
                    let evar = Sort.mk_fresh_evar () in
                    let pat = pattern_of dtenv ~sort:(Some sort1) case.c_lhs in
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
                   @@ List.map (Option.to_list ovar1)
                        ~f:(Tuple2.create c0.op_sig))
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
          | Texp_open (_, _)
          | Texp_atomic_loc (_, _, _) ->
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
