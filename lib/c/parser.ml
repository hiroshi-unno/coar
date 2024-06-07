open Core
open Common.Ext
open Common.Combinator
open Common.Util.LexingHelper
open CSyntax
open Ast
open Ast.LogicOld

let rec sub_inits_rep subst res = function
  | [] -> List.rev res
  | init :: tail ->
      if Init.is_assign init then
        let varname, term = Init.let_assign init in
        let term = Term.subst subst term in
        let tvar = Ident.Tvar varname in
        let subst = Map.Poly.update subst tvar ~f:(fun _ -> term) in
        let init = Init.mk_assign varname term in
        sub_inits_rep subst (init :: res) tail
      else if Init.is_assume init then
        let init =
          Init.let_assume init |> Formula.subst subst |> Init.mk_assume
        in
        sub_inits_rep subst (init :: res) tail
      else if Init.is_nondet_assign init then
        let varname = Init.let_nondet_assign init in
        let subst = Map.Poly.remove subst (Ident.Tvar varname) in
        sub_inits_rep subst (init :: res) tail
      else assert false

let sub_inits inits = sub_inits_rep Map.Poly.empty [] inits

module ReturnReplacer : sig
  (* val replace_return_int: f:(Term.t -> Statement.t) -> Statement.t -> Statement.t
     val replace_return_nondet: replace_to:Statement.t -> Statement.t -> Statement.t
     val replace_return_void: replace_to:Statement.t -> Statement.t -> Statement.t *)
  val replace_return :
    f:(Statement.t -> Statement.t) -> Statement.t -> Statement.t
end = struct
  let rec replace_return ~f stmt =
    if
      Statement.is_return_int stmt
      || Statement.is_return_void stmt
      || Statement.is_return_nondet stmt
    then f stmt
    else if Statement.is_compound stmt then
      let stmt1, stmt2 = Statement.let_compound stmt in
      Statement.mk_compound (replace_return ~f stmt1) (replace_return ~f stmt2)
    else if Statement.is_if stmt then
      let cond_fml, t_stmt, f_stmt = Statement.let_if stmt in
      Statement.mk_if cond_fml (replace_return ~f t_stmt)
        (replace_return ~f f_stmt)
    else if Statement.is_nondet stmt then
      let stmt1, stmt2 = Statement.let_nondet stmt in
      Statement.mk_nondet (replace_return ~f stmt1) (replace_return ~f stmt2)
    else if Statement.is_loop stmt then
      let stmt' = Statement.let_loop stmt in
      Statement.mk_loop (replace_return ~f stmt')
    else if
      Statement.is_assign stmt
      || Statement.is_unref_assign stmt
      || Statement.is_vardecl stmt
      || Statement.is_call_assign stmt
      || Statement.is_call_voidfun stmt
      || Statement.is_goto stmt || Statement.is_label stmt
      || Statement.is_nondet_assign stmt
      || Statement.is_assume stmt || Statement.is_break stmt
      || Statement.is_exit stmt || Statement.is_nop stmt
    then stmt
    else assert false
  (* let replace_return_void ~replace_to query =
     replace_return
      ~f:(fun stmt -> if Statement.is_return_void stmt then replace_to else stmt)
      query
     let replace_return_nondet ~replace_to query =
     replace_return
      ~f:(fun stmt -> if Statement.is_return_nondet stmt then replace_to else stmt)
      query
     let replace_return_int ~f query =
     replace_return
      ~f:(fun stmt ->
          if Statement.is_return_int stmt then
            let term = Statement.let_return_int stmt in
            f term
          else stmt)
      query *)
end

module ElimFuncall : sig
  val elim_funcall : FunDecl.t list -> Statement.t -> Statement.t
end = struct
  let mk_labelname funname nxt_label_id =
    (sprintf "%s#%d" funname nxt_label_id, nxt_label_id + 1)

  let subst_terms subst terms = List.map ~f:(Term.subst subst) terms

  (* TODO: *p = &hoge; *p = q; (elim by optimization) *)
  (* *p = q -> p' = q *)
  let rec unref_ref_stmt_rep from_varname to_varname subst stmt =
    if Statement.is_unref_assign stmt then
      let varname, term = Statement.let_unref_assign stmt in
      let term = Term.subst subst term in
      if String.equal varname from_varname then
        Statement.mk_assign to_varname term
      else Statement.mk_unref_assign varname term
    else if Statement.is_assign stmt then
      let varname, term = Statement.let_assign stmt in
      Statement.mk_assign varname (Term.subst subst term)
    else if Statement.is_assume stmt then
      let fml = Statement.let_assume stmt in
      Statement.mk_assume (Formula.subst subst fml)
    else if Statement.is_call_assign stmt then
      let varname, funname, args = Statement.let_call_assign stmt in
      Statement.mk_call_assign varname funname (subst_terms subst args)
    else if Statement.is_call_voidfun stmt then
      let funname, args = Statement.let_call_voidfun stmt in
      Statement.mk_call_voidfun funname (subst_terms subst args)
    else if Statement.is_compound stmt then
      let stmt1, stmt2 = Statement.let_compound stmt in
      Statement.mk_compound
        (unref_ref_stmt_rep from_varname to_varname subst stmt1)
        (unref_ref_stmt_rep from_varname to_varname subst stmt2)
    else if Statement.is_if stmt then
      let cond_fml, tstmt, fstmt = Statement.let_if stmt in
      Statement.mk_if
        (Formula.subst subst cond_fml)
        (unref_ref_stmt_rep from_varname to_varname subst tstmt)
        (unref_ref_stmt_rep from_varname to_varname subst fstmt)
    else if Statement.is_loop stmt then
      let stmt = Statement.let_loop stmt in
      Statement.mk_loop (unref_ref_stmt_rep from_varname to_varname subst stmt)
    else if Statement.is_nondet stmt then
      let stmt1, stmt2 = Statement.let_nondet stmt in
      Statement.mk_nondet
        (unref_ref_stmt_rep from_varname to_varname subst stmt1)
        (unref_ref_stmt_rep from_varname to_varname subst stmt2)
    else if Statement.is_return_int stmt then
      let term = Statement.let_return_int stmt in
      Statement.mk_return_int (Term.subst subst term)
    else if
      Statement.is_break stmt || Statement.is_exit stmt || Statement.is_nop stmt
      || Statement.is_goto stmt || Statement.is_label stmt
      || Statement.is_return_nondet stmt
      || Statement.is_return_void stmt
      || Statement.is_vardecl stmt
      || Statement.is_nondet_assign stmt
    then stmt
    else
      failwith
      @@ sprintf "move_funcall_rep: not implemented: %s"
           (Statement.string_of stmt)

  (*
    void f(int a, int b) { P; }
    f(x, y);

    ->

    while (1) {
      int a = x, b = y;
      P;
      break;
    }
    f#0:
  *)
  let rec mk_inline_funcall nxt_label_id fundecls params args labelname
      return_replaced_funbody =
    let body, nxt_label_id =
      elim_funcall_rep nxt_label_id fundecls return_replaced_funbody
    in
    let zipped = List.zip_exn params args in
    let pa_int =
      List.filter ~f:(fun ((_, sort), _) -> Term.is_int_sort sort) zipped
    in
    let pa_unref =
      List.filter ~f:(fun ((_, sort), _) -> Term.is_int_ref_sort sort) zipped
    in
    assert (List.length pa_int + List.length pa_unref = List.length zipped);
    (* replace "*&p" with "p" *)
    let body =
      List.fold_left ~init:body pa_unref ~f:(fun body ((varname, _), arg) ->
          (* arg = Term.Var (_, T_int.SRefInt, _) *)
          let (tvar, _), _ = Term.let_var arg in
          (* if sort <> T_int.SRefInt then
             failwith @@ sprintf "sort of (param, arg) = (%s, %s) is not T_int.SRefInt" varname (Term.str_of arg); *)
          let subst =
            Map.Poly.of_alist_exn
              [ (Ident.Tvar varname, Term.mk_var tvar T_int.SInt ~info:Dummy) ]
          in
          unref_ref_stmt_rep varname (Ident.name_of_tvar tvar) subst body)
    in
    ( Statement.mk_compound
        (List.map
           ~f:(fun ((varname, _), _) -> Statement.mk_vardecl varname T_int.SInt)
           pa_int
         @ List.map
             ~f:(fun ((varname, _), arg) -> Statement.mk_assign varname arg)
             pa_int
         @ [ body; Statement.mk_break () ]
        |> Statement.of_statements |> Statement.mk_loop)
        (Statement.mk_label labelname),
      nxt_label_id )

  and elim_funcall_rep nxt_label_id fundecls stmt =
    if Statement.is_call_assign stmt then
      let varname, funname, args = Statement.let_call_assign stmt in
      let fundecl = FunDecl.find_fundecl funname fundecls in
      if FunDecl.is_fun_nondet fundecl then
        (Statement.mk_nondet_assign varname, nxt_label_id)
      else if FunDecl.is_fun_int fundecl then
        let _, params, body = FunDecl.let_fun_int fundecl in
        let labelname, nxt_label_id = mk_labelname funname nxt_label_id in
        if FunDecl.is_non_recursive fundecls fundecl then
          ReturnReplacer.replace_return
            ~f:(fun stmt ->
              if Statement.is_return_int stmt then
                let term = Statement.let_return_int stmt in
                Statement.mk_compound
                  (Statement.mk_assign varname term)
                  (Statement.mk_goto labelname)
              else if Statement.is_return_nondet stmt then
                Statement.mk_compound
                  (Statement.mk_nondet_assign varname)
                  (Statement.mk_goto labelname)
              else assert false)
            (* append 'return nondet();' if it's missing *)
            (Statement.mk_compound body (Statement.mk_return_nondet ()))
          |> mk_inline_funcall nxt_label_id fundecls params args labelname
        else assert false
      else assert false
    else if Statement.is_call_voidfun stmt then
      let funname, args = Statement.let_call_voidfun stmt in
      let fundecl = FunDecl.find_fundecl funname fundecls in
      let _, params, body = FunDecl.let_fun fundecl in
      if Statement.is_nop body then (body, nxt_label_id)
      else
        let labelname, nxt_label_id = mk_labelname funname nxt_label_id in
        if FunDecl.is_non_recursive fundecls fundecl then
          ReturnReplacer.replace_return
            ~f:(fun _ -> Statement.mk_goto labelname)
            body
          |> mk_inline_funcall nxt_label_id fundecls params args labelname
        else assert false
    else if Statement.is_if stmt then
      let cond_fml, t_stmt, f_stmt = Statement.let_if stmt in
      let t_stmt, nxt_label_id =
        elim_funcall_rep nxt_label_id fundecls t_stmt
      in
      let f_stmt, nxt_label_id =
        elim_funcall_rep nxt_label_id fundecls f_stmt
      in
      (Statement.mk_if cond_fml t_stmt f_stmt, nxt_label_id)
    else if Statement.is_nondet stmt then
      let stmt1, stmt2 = Statement.let_nondet stmt in
      let stmt1, nxt_label_id = elim_funcall_rep nxt_label_id fundecls stmt1 in
      let stmt2, nxt_label_id = elim_funcall_rep nxt_label_id fundecls stmt2 in
      (Statement.mk_nondet stmt1 stmt2, nxt_label_id)
    else if Statement.is_compound stmt then
      let stmt1, stmt2 = Statement.let_compound stmt in
      let stmt1, nxt_label_id = elim_funcall_rep nxt_label_id fundecls stmt1 in
      let stmt2, nxt_label_id = elim_funcall_rep nxt_label_id fundecls stmt2 in
      (Statement.mk_compound stmt1 stmt2, nxt_label_id)
    else if Statement.is_loop stmt then
      let stmt' = Statement.let_loop stmt in
      let stmt', nxt_label_id = elim_funcall_rep nxt_label_id fundecls stmt' in
      (Statement.mk_loop stmt', nxt_label_id)
    else if
      Statement.is_assign stmt
      || Statement.is_unref_assign stmt
      || Statement.is_vardecl stmt || Statement.is_goto stmt
      || Statement.is_label stmt
      || Statement.is_nondet_assign stmt
      || Statement.is_assume stmt || Statement.is_break stmt
      || Statement.is_exit stmt || Statement.is_nop stmt
      || Statement.is_return_int stmt
      || Statement.is_return_nondet stmt
      || Statement.is_return_void stmt
    then (stmt, nxt_label_id)
    else
      failwith
      @@ sprintf "elim_funcall_rep: not implemented for: %s"
           (Statement.string_of stmt)

  let move_funcall_tvar_of_count count =
    (Ident.Tvar (sprintf "#result%d" count), count + 1)

  let rec move_funcall_term_rep ?(gen = Fn.id) count term :
      Term.t * (Statement.t -> Statement.t) * int =
    if Term.is_app term then
      let fsym, args, info = Term.let_app term in
      let args, gen, count = move_funcall_terms ~gen count args in
      match fsym with
      | FunCall funname ->
          let tvar, count = move_funcall_tvar_of_count count in
          let gen stmt =
            Statement.mk_compound
              (Statement.mk_call_assign (Ident.name_of_tvar tvar) funname args)
              (gen stmt)
          in
          (Term.mk_var tvar T_int.SInt ~info:Dummy, gen, count)
      | fsym -> (Term.mk_fsym_app fsym args ~info, gen, count)
    else if Term.is_var term then (term, gen, count)
    else
      failwith
      @@ sprintf "move_funcall_term_rep: not implemented: %s" (Term.str_of term)

  and move_funcall_terms ?(gen = Fn.id) count terms =
    List.fold_left ~init:([], gen, count) (List.rev terms)
      ~f:(fun (terms, gen, count) term ->
        let term, gen, count = move_funcall_term_rep ~gen count term in
        (term :: terms, gen, count))

  let move_funcall_atom_rep ?(gen = Fn.id) count atom :
      Atom.t * (Statement.t -> Statement.t) * int =
    if Atom.is_psym_app atom then
      let psym, args, info = Atom.let_psym_app atom in
      let args, gen, count = move_funcall_terms ~gen count args in
      (Atom.mk_app (Predicate.mk_psym psym) args ~info, gen, count)
    else if Atom.is_true atom || Atom.is_false atom then (atom, gen, count)
    else
      failwith
      @@ sprintf "move_funcall_atom_rep: not implemented: %s" (Atom.str_of atom)

  let rec move_funcall_formula_rep ?(gen = Fn.id) count fml :
      Formula.t * (Statement.t -> Statement.t) * int =
    if Formula.is_atom fml then
      let atom, info = Formula.let_atom fml in
      let atom, gen, count = move_funcall_atom_rep ~gen count atom in
      (Formula.mk_atom atom ~info, gen, count)
    else if Formula.is_binop fml then
      let binop, fml1, fml2, info = Formula.let_binop fml in
      let fml1, gen, count = move_funcall_formula_rep ~gen count fml1 in
      let fml2, gen, count = move_funcall_formula_rep ~gen count fml2 in
      (Formula.mk_binop binop fml1 fml2 ~info, gen, count)
    else if Formula.is_unop fml then
      let unop, fml, info = Formula.let_unop fml in
      let fml, gen, count = move_funcall_formula_rep ~gen count fml in
      (Formula.mk_unop unop fml ~info, gen, count)
    else
      failwith
      @@ sprintf "move_funcall_formula_rep: not implemented %s"
           (Formula.str_of fml)

  let rec move_funcall_rep stmt =
    if Statement.is_assign stmt then
      let varname, term = Statement.let_assign stmt in
      let term, gen, _ = move_funcall_term_rep 0 term in
      Statement.mk_assign varname term |> gen
    else if Statement.is_unref_assign stmt then
      let varname, term = Statement.let_unref_assign stmt in
      let term, gen, _ = move_funcall_term_rep 0 term in
      Statement.mk_unref_assign varname term |> gen
    else if Statement.is_assume stmt then
      let fml = Statement.let_assume stmt in
      let fml, gen, _ = move_funcall_formula_rep 0 fml in
      Statement.mk_assume fml |> gen
    else if Statement.is_call_assign stmt then
      let varname, funname, args = Statement.let_call_assign stmt in
      let args, gen, _ = move_funcall_terms 0 args in
      Statement.mk_call_assign varname funname args |> gen
    else if Statement.is_call_voidfun stmt then
      let funname, args = Statement.let_call_voidfun stmt in
      let args, gen, _ = move_funcall_terms 0 args in
      Statement.mk_call_voidfun funname args |> gen
    else if Statement.is_compound stmt then
      let stmt1, stmt2 = Statement.let_compound stmt in
      Statement.mk_compound (move_funcall_rep stmt1) (move_funcall_rep stmt2)
    else if Statement.is_if stmt then
      let cond_fml, tstmt, fstmt = Statement.let_if stmt in
      let cond_fml, gen, _ = move_funcall_formula_rep 0 cond_fml in
      Statement.mk_if cond_fml (move_funcall_rep tstmt) (move_funcall_rep fstmt)
      |> gen
    else if Statement.is_loop stmt then
      let stmt = Statement.let_loop stmt in
      Statement.mk_loop (move_funcall_rep stmt)
    else if Statement.is_nondet stmt then
      let stmt1, stmt2 = Statement.let_nondet stmt in
      Statement.mk_nondet (move_funcall_rep stmt1) (move_funcall_rep stmt2)
    else if Statement.is_return_int stmt then
      let term = Statement.let_return_int stmt in
      let term, gen, _ = move_funcall_term_rep 0 term in
      Statement.mk_return_int term |> gen
    else if
      Statement.is_break stmt || Statement.is_exit stmt || Statement.is_nop stmt
      || Statement.is_goto stmt || Statement.is_label stmt
      || Statement.is_return_nondet stmt
      || Statement.is_return_void stmt
      || Statement.is_vardecl stmt
      || Statement.is_nondet_assign stmt
    then stmt
    else
      failwith
      @@ sprintf "move_funcall_rep: not implemented: %s"
           (Statement.string_of stmt)

  let move_funcall_fundecl fundecl =
    if FunDecl.is_fun_int fundecl then
      let funname, args, body = FunDecl.let_fun_int fundecl in
      FunDecl.mk_fun_int funname args (move_funcall_rep body)
    else if FunDecl.is_fun_void fundecl then
      let funname, args, body = FunDecl.let_fun_void fundecl in
      FunDecl.mk_fun_void funname args (move_funcall_rep body)
    else if FunDecl.is_fun_nondet fundecl then fundecl
    else failwith "unknown fundecl"

  let elim_funcall fundecls stmt =
    let stmt = move_funcall_rep stmt in
    let fundecls = List.map ~f:move_funcall_fundecl fundecls in
    let res, _ = elim_funcall_rep 0 fundecls stmt in
    res
end

module ElimVardecl : sig
  val elim_vardecl : Statement.t -> Statement.t
end = struct
  let rename renamed_vars varname =
    match Map.Poly.find renamed_vars (Ident.Tvar varname) with
    | Some term ->
        let (tvar, _), _ = Term.let_var term in
        Ident.name_of_tvar tvar
    | None -> varname

  let rename_term renamed_vars term = Term.subst renamed_vars term
  let rename_formula renamed_vars formula = Formula.subst renamed_vars formula

  let rec elim_vardecl_rep renamed_vars stmt =
    if Statement.is_call_assign stmt then
      let varname, funname, args = Statement.let_call_assign stmt in
      ( Statement.mk_call_assign
          (rename renamed_vars varname)
          funname
          (List.map args ~f:(rename_term renamed_vars)),
        renamed_vars )
    else if Statement.is_call_voidfun stmt then
      let funname, args = Statement.let_call_voidfun stmt in
      ( Statement.mk_call_voidfun funname
          (List.map args ~f:(rename_term renamed_vars)),
        renamed_vars )
    else if Statement.is_if stmt then
      let cond_fml, t_stmt, f_stmt = Statement.let_if stmt in
      let t_stmt', _ = elim_vardecl_rep renamed_vars t_stmt in
      let f_stmt', _ = elim_vardecl_rep renamed_vars f_stmt in
      ( Statement.mk_if (rename_formula renamed_vars cond_fml) t_stmt' f_stmt',
        renamed_vars )
    else if Statement.is_nondet stmt then
      let stmt1, stmt2 = Statement.let_nondet stmt in
      let stmt1', _ = elim_vardecl_rep renamed_vars stmt1 in
      let stmt2', _ = elim_vardecl_rep renamed_vars stmt2 in
      (Statement.mk_nondet stmt1' stmt2', renamed_vars)
    else if Statement.is_compound stmt then
      let stmt1, stmt2 = Statement.let_compound stmt in
      let stmt1', renamed_vars = elim_vardecl_rep renamed_vars stmt1 in
      let stmt2', renamed_vars = elim_vardecl_rep renamed_vars stmt2 in
      (Statement.mk_compound stmt1' stmt2', renamed_vars)
    else if Statement.is_loop stmt then
      let inner_stmt = Statement.let_loop stmt in
      let inner_stmt', _ = elim_vardecl_rep renamed_vars inner_stmt in
      (Statement.mk_loop inner_stmt', renamed_vars)
    else if Statement.is_assign stmt then
      let varname, term = Statement.let_assign stmt in
      ( Statement.mk_assign
          (rename renamed_vars varname)
          (rename_term renamed_vars term),
        renamed_vars )
    else if Statement.is_nondet_assign stmt then
      let varname = Statement.let_nondet_assign stmt in
      (Statement.mk_nondet_assign (rename renamed_vars varname), renamed_vars)
    else if Statement.is_assume stmt then
      let fml = Statement.let_assume stmt in
      (Statement.mk_assume (rename_formula renamed_vars fml), renamed_vars)
    else if Statement.is_vardecl stmt then
      let varname, sort = Statement.let_vardecl stmt in
      let new_varname =
        sprintf "%s#%d" varname (Map.Poly.length renamed_vars)
      in
      ( Statement.mk_nondet_assign new_varname,
        Map.Poly.update renamed_vars (Ident.Tvar varname) ~f:(fun _ ->
            Term.mk_var (Ident.Tvar new_varname) sort ~info:Dummy) )
    else if Statement.is_return_int stmt then
      let term = Statement.let_return_int stmt in
      (Statement.mk_return_int (rename_term renamed_vars term), renamed_vars)
    else if
      Statement.is_goto stmt || Statement.is_label stmt
      || Statement.is_break stmt || Statement.is_exit stmt
      || Statement.is_nop stmt
    then (stmt, renamed_vars)
    else
      failwith
      @@ sprintf "elim_vardecl_rep: not implemented: %s"
           (Statement.string_of stmt)

  let elim_vardecl stmt = fst @@ elim_vardecl_rep Map.Poly.empty stmt
end

let parse_cctl_from_lexbuf ~print lexbuf =
  try
    let (phi, decls, inits, body), defs, fundecls =
      CCtlParser.toplevel CCtlLexer.main lexbuf
    in
    (* a = 3; b = a; -> a = 3; b = 3; *)
    let inits = sub_inits inits in
    let def_subst = Define.subst_of_defines defs in
    (* dispose #define for inits *)
    let inits = List.map ~f:(Init.subst def_subst) inits in
    (* dispose #define for body *)
    let body = Statement.subst def_subst body in
    (* elim all fun callings *)
    let body = ElimFuncall.elim_funcall fundecls body in
    print @@ lazy "vvvvvvvvvvvvv Input C Program vvvvvvvvvvvvv";
    print @@ lazy (sprintf "[phi]\n%s\n" (Ctl.string_of phi));
    print
    @@ lazy
         (sprintf "[decls]\n%s\n"
            (String.concat_map_list ~sep:"\n" decls ~f:Declare.string_of));
    print
    @@ lazy
         (sprintf "[inits]\n%s\n"
            (String.concat_map_list ~sep:"\n" inits ~f:Init.string_of));
    print @@ lazy (sprintf "[body]\n%s\n" (Statement.string_of body));
    print @@ lazy "";
    Ok (HesOf.hes_of_cctl ~print (phi, decls, inits, body))
  with
  | CSyntax.SemanticError error ->
      Result.fail (Error.of_string (sprintf "semantic error: %s" error))
  | CSyntax.SyntaxError error ->
      Result.fail
        (Error.of_string
           (sprintf "%s: syntax error: %s" (get_position_string lexbuf) error))
  | CCtlParser.Error ->
      Result.fail
        (Error.of_string
           (sprintf "%s: syntax error" (get_position_string lexbuf)))
  | CCtlLexer.SyntaxError error ->
      Result.fail
        (Error.of_string
           (sprintf "%s: syntax error: %s" (get_position_string lexbuf) error))
  | CCtlLexer.ErrorFormatted error -> Result.fail (Error.of_string error)

let parse_cltl_from_lexbuf ~print lexbuf =
  try
    let (ltl, decls, inits, body), defs, fundecls =
      CLtlParser.toplevel CLtlLexer.main lexbuf
    in
    let fundecls =
      [
        FunDecl.mk_fun_int "#dec"
          [ ("x", T_int.SRefInt) ]
          (let tvar = Ident.Tvar "x" in
           Statement.of_statements
             [
               (* *x = x-1 *)
               Statement.mk_unref_assign "x"
                 (T_int.mk_sub
                    (Term.mk_var tvar T_int.SUnrefInt ~info:Dummy)
                    (T_int.mk_int Z.one ~info:Dummy)
                    ~info:Dummy);
               (* return *x *)
               Statement.mk_return_int
                 (Term.mk_var tvar T_int.SUnrefInt ~info:Dummy);
             ]);
        FunDecl.mk_fun_int "#inc"
          [ ("x", T_int.SRefInt) ]
          (let tvar = Ident.Tvar "x" in
           Statement.of_statements
             [
               (* *x = x+1 *)
               Statement.mk_unref_assign "x"
                 (T_int.mk_add
                    (Term.mk_var tvar T_int.SUnrefInt ~info:Dummy)
                    (T_int.mk_int Z.one ~info:Dummy)
                    ~info:Dummy);
               (* return *x *)
               Statement.mk_return_int
                 (Term.mk_var tvar T_int.SUnrefInt ~info:Dummy);
             ]);
        FunDecl.mk_fun_int "__VERIFIER_nondet_int" []
          (Statement.mk_return_nondet ());
      ]
      @ fundecls
    in
    let def_subst = Define.subst_of_defines defs in
    (* elim all fun callings *)
    let body = ElimFuncall.elim_funcall fundecls body in
    (* rename local variables to elim Statement.VARDECL *)
    let body = ElimVardecl.elim_vardecl body in
    (* dispose #define for body *)
    (* let body = Statement.subst def_subst body in *)
    (* replace all return in main *)
    let body =
      ReturnReplacer.replace_return ~f:(fun _ -> Statement.mk_exit ()) body
    in
    (* a = 3; b = 4; if ... -> inits: a=3;b=4; body: if ... *)
    let inits, body_opt = Init.of_stmt inits body in
    let body =
      match body_opt with None -> Statement.mk_exit () | Some body -> body
    in
    (* a = 3; b = a; -> a = 3; b = 3; *)
    let inits = sub_inits inits in
    (* dispose #define for inits *)
    let inits = List.map ~f:(Init.subst def_subst) inits in
    print @@ lazy "vvvvvvvvvvvvv Input C Program vvvvvvvvvvvvv";
    print @@ lazy (sprintf "[ltl]\n%s\n" (Ltl.string_of ltl));
    (* Debug.print @@ lazy
       (sprintf "[decls]\n%s\n"
         (String.concat_map_list ~sep:"\n" decls ~f:Declare.string_of)); *)
    print
    @@ lazy
         (sprintf "[inits]\n%s\n"
            (String.concat_map_list ~sep:"\n" inits ~f:Init.string_of));
    print @@ lazy (sprintf "[body]\n%s\n" (Statement.string_of body));
    print @@ lazy "";
    (* convert the given specification *)
    let ltl = Ltl.simplify_neg ltl in
    print @@ lazy (sprintf "[ltl(neg)]\n%s\n" (Ltl.string_of ltl));
    let ba = LogicConverter.ba_of_ltl ~print ltl in
    print
    @@ lazy
         (sprintf "[ba]\n%s\n"
            (BuchiAutomaton.string_of ~printer:Formula.str_of ba));
    let hmes = LogicConverter.hmes_of_ba ba in
    print @@ lazy (sprintf "[hmes]\n%s\n" (HMES.string_of hmes));
    Ok (HesOf.hes_of_chmes ~print (hmes, decls, inits, body))
  with
  | CSyntax.SemanticError error ->
      Result.fail (Error.of_string (sprintf "semantic error: %s" error))
  | CSyntax.SyntaxError error ->
      Result.fail
        (Error.of_string
           (sprintf "%s: syntax error: %s" (get_position_string lexbuf) error))
  | CLtlParser.Error ->
      Result.fail
        (Error.of_string
           (sprintf "%s: syntax error" (get_position_string lexbuf)))
  | CLtlLexer.SyntaxError error ->
      Result.fail
        (Error.of_string
           (sprintf "%s: syntax error: %s" (get_position_string lexbuf) error))
  | CLtlLexer.ErrorFormatted error -> Result.fail (Error.of_string error)

let read_file file =
  let ic = In_channel.create file in
  let res = ref "" in
  try
    while true do
      res := !res ^ In_channel.input_line_exn ic ^ "\n"
    done;
    assert false
  with End_of_file ->
    In_channel.close ic;
    !res

module Preprocess : sig
  val preprocess : string -> string
end = struct
  let is_preprocess line = String.is_prefix ~prefix:"#" line

  (* let reg_include = Str.regexp "#include[ \t]+\\(\"[^\"]+\"|<[^>]+>\\)[ \t\r\n]+$" *)
  (* let let_include_preprocess line = assert (is_include_preprocess line); Str.matched_group 1 line *)

  let reg_type_of = Str.regexp "#\\([^ <\"\t\n]*\\)"

  let type_of_preprocess line =
    assert (Str.string_match reg_type_of line 0);
    Str.matched_group 1 line

  let reg_define_macro =
    Str.regexp
      "#define[ \
       \t]+\\([a-zA-Z_][a-zA-Z_0-9]*\\)(\\(\\|[a-zA-Z_][a-zA-Z_0-9]*\\(,[a-zA-Z_][a-zA-Z_0-9]*\\)*\\))[ \
       \t]+\\(.*\\)$"

  let is_define_macro line = Str.string_match reg_define_macro line 0

  let rec string_repeat str times =
    if times = 0 then "" else str ^ string_repeat str (times - 1)

  let subst_identifier id subst_to str =
    Str.global_replace
      (Str.regexp @@ "\\(^\\|[^a-zA-Z_0-9]\\)" ^ id ^ "\\($\\|[^a-zA-Z_0-9]\\)")
      ("\\1" ^ subst_to ^ "\\2")
      str

  let subst_macro id params subst_to program =
    let regstr_args =
      if List.is_empty params then ""
      else string_repeat "[^,]+," (List.length params - 1) ^ "[^)]+"
    in
    let reg =
      Str.regexp @@ "\\(^\\|[^a-zA-Z_0-9]\\)" ^ id ^ "[ \t]*(\\(" ^ regstr_args
      ^ "\\))"
    in
    Str.global_substitute reg
      (fun program ->
        let head = Str.matched_group 1 program in
        let args = Str.matched_group 2 program in
        let args =
          if String.equal args "" then []
          else String.split_on_chars ~on:[ ',' ] args
        in
        head
        ^ List.fold_left ~init:subst_to (List.zip_exn params args)
            ~f:(fun subst_to (param, arg) ->
              subst_identifier param arg subst_to))
      program

  let reg_define_const =
    Str.regexp "#define[ \t]+\\([a-zA-Z_][a-zA-Z_0-9]*\\)[ \t]+\\(.*\\)$"

  let is_define_const line = Str.string_match reg_define_const line 0

  (* TODO: for comments *)
  let preprocess program =
    let lines = program |> String.split_on_chars ~on:[ '\n' ] in
    let program, _ =
      List.fold_left
        ~f:(fun (program, line_number) line ->
          let line_number = line_number + 1 in
          if Fn.non is_preprocess line then (program, line_number)
          else if String.equal (type_of_preprocess line) "include" then
            (program, line_number (* TODO? *))
          else if String.equal (type_of_preprocess line) "define" then
            if is_define_macro line then
              let id = Str.matched_group 1 line in
              let params =
                Str.matched_group 2 line |> fun params ->
                if String.equal params "" then []
                else String.split_on_chars ~on:[ ',' ] params
              in
              let subst_to = Str.matched_group 4 line in
              (subst_macro id params subst_to program, line_number)
            else if is_define_const line then
              let id = Str.matched_group 1 line in
              let subst_to = Str.matched_group 2 line in
              (subst_identifier id subst_to program, line_number)
            else failwith @@ sprintf "%d: syntax error: %s" line_number line
          else
            failwith
            @@ sprintf "unknown preprocess: %s" (type_of_preprocess line))
        ~init:
          ( String.concat_map_list lines ~sep:"\n" ~f:(fun line ->
                if is_preprocess line then "" else line),
            0 )
        lines
    in
    program
end

let parse_cltl ~print program =
  let program = Preprocess.preprocess program in
  (*print @@ lazy "=============== Preprocessed ===============";
    print @@ lazy (program ^ "\n");*)
  program |> Lexing.from_string |> parse_cltl_from_lexbuf ~print

let parse_cctl ~print = Lexing.from_string >> parse_cctl_from_lexbuf ~print
let from_cltl_file ~print file = parse_cltl ~print @@ read_file file
let from_cctl_file ~print file = parse_cctl ~print @@ read_file file
