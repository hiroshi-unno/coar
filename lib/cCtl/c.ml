open Core
open Common
open CSyntax
open Ast.LogicOld
open Ast

let verbose = false
module Debug = Debug.Make (val (Debug.Config.(if verbose then enable else disable)))

let get_position_string (lexbuf: Lexing.lexbuf) =
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%d:%d"
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let rec sub_inits_rep subst res = function
  | [] -> List.rev res
  | init :: tail ->
    if Init.is_assign init then
      let varname, term = Init.let_assign init in
      let term = Term.subst subst term in
      let subst = Core.Map.Poly.add_exn subst ~key:(Ident.Tvar varname) ~data:term in
      let init = Init.mk_assign varname term in
      sub_inits_rep subst (init :: res) tail
    else if Init.is_assume init then
      let init =
        Init.let_assume init
        |> Formula.subst subst
        |> Init.mk_assume
      in
      sub_inits_rep subst (init :: res) tail
    else
      assert false

let sub_inits inits = sub_inits_rep Core.Map.Poly.empty [] inits

let rec elim_assigns_to_args param_vars stmt =
  if Statement.is_nondet_assign stmt then
    let varname = Statement.let_nondet_assign stmt in
    if Variables.is_mem varname param_vars then
      Statement.mk_nop ()
    else
      stmt
  else if Statement.is_assign stmt then
    let varname, _ = Statement.let_assign stmt in
    if Variables.is_mem varname param_vars then
      Statement.mk_nop ()
    else
      stmt
  else if Statement.is_nondet stmt then
    let stmt1, stmt2 = Statement.let_nondet stmt in
    Statement.mk_nondet (elim_assigns_to_args param_vars stmt1) (elim_assigns_to_args param_vars stmt2)
  else if Statement.is_compound stmt then
    let stmt1, stmt2 = Statement.let_compound stmt in
    Statement.mk_compound (elim_assigns_to_args param_vars stmt1) (elim_assigns_to_args param_vars stmt2)
  else if Statement.is_loop stmt then
    let stmt' = Statement.let_loop stmt in
    Statement.mk_loop (elim_assigns_to_args param_vars stmt')
  else if
    Statement.is_call_voidfun stmt
    || Statement.is_assign stmt
    || Statement.is_assume stmt
    || Statement.is_break stmt
    || Statement.is_exit stmt
    || Statement.is_nop stmt then
    stmt
  else
    assert false

let rec elim_funcall fundecls stmt =
  if Statement.is_call_assign stmt then
    let varname, funname, _ = Statement.let_call_assign stmt in
    let fundecl = FunDecl.find_fundecl funname fundecls in
    assert(FunDecl.is_fun_nondet fundecl);
    Statement.mk_nondet_assign varname
  else if Statement.is_call_voidfun stmt then
    let funname, _ = Statement.let_call_voidfun stmt in
    let fundecl = FunDecl.find_fundecl funname fundecls in
    let _, params, body = FunDecl.let_fun_void fundecl in
    let param_vars = Variables.of_list params in
    let inter =
      Variables.inter
        (Statement.get_read_vars body)
        param_vars
    in
    if Variables.is_empty inter then
      elim_assigns_to_args param_vars body
    else
      assert false
  else if Statement.is_if stmt then
    let cond_fml, t_stmt, f_stmt = Statement.let_if stmt in
    Statement.mk_if cond_fml
      (elim_funcall fundecls t_stmt)
      (elim_funcall fundecls f_stmt)
  else if Statement.is_nondet stmt then
    let stmt1, stmt2 = Statement.let_nondet stmt in
    Statement.mk_nondet (elim_funcall fundecls stmt1) (elim_funcall fundecls stmt2)
  else if Statement.is_compound stmt then
    let stmt1, stmt2 = Statement.let_compound stmt in
    Statement.mk_compound (elim_funcall fundecls stmt1) (elim_funcall fundecls stmt2)
  else if Statement.is_loop stmt then
    let stmt' = Statement.let_loop stmt in
    Statement.mk_loop (elim_funcall fundecls stmt')
  else if
    Statement.is_assign stmt
    || Statement.is_nondet_assign stmt
    || Statement.is_assume stmt
    || Statement.is_break stmt
    || Statement.is_exit stmt
    || Statement.is_nop stmt then
    stmt
  else
    assert false

let parse_from_lexbuf lexbuf =
  try
    let (phi, decls, inits, body), defs, fundecls = CParser.toplevel CLexer.main lexbuf in
    (* a = 3; b = a; -> a = 3; b = 3; *)
    let inits = sub_inits inits in
    let def_subst = Define.subst_of_defines defs in
    (* dispose #define for inits *)
    let inits = List.map ~f:(Init.subst def_subst) inits in
    (* dispose #define for body *)
    let body = Statement.subst def_subst body in
    (* elim all fun callings *)
    let body = elim_funcall fundecls body in
    Debug.print @@ lazy "vvvvvvvvvvvvv Input C Program vvvvvvvvvvvvv";
    Debug.print @@ lazy (Printf.sprintf "[phi]\n%s\n" (Ctl.string_of phi));
    Debug.print @@ lazy (Printf.sprintf "[decls]\n%s\n"
                           ((List.map ~f:(fun decl -> Declare.string_of decl) decls) |> String.concat ~sep:"\n"));
    Debug.print @@ lazy (Printf.sprintf "[inits]\n%s\n"
                           (inits |> List.map ~f:Init.string_of |> String.concat ~sep:"\n"));
    Debug.print @@ lazy (Printf.sprintf "[body]\n%s\n" (Statement.string_of body));
    Debug.print @@ lazy "";
    Ok (HesOf.hes_of_c (phi, decls, inits, body))
  with
  | CSyntax.SemanticError error ->
    Result.fail (Error.of_string (Printf.sprintf "semantic error: %s" error))
  | CSyntax.SyntaxError error ->
    Result.fail (Error.of_string (Printf.sprintf "%s: syntax error: %s" (get_position_string lexbuf) error))
  | CParser.Error ->
    Result.fail (Error.of_string (Printf.sprintf "%s: syntax error" (get_position_string lexbuf)))
  | CLexer.SyntaxError error ->
    Result.fail (Error.of_string (Printf.sprintf "%s: syntax error: %s" (get_position_string lexbuf) error))
  | CLexer.ErrorFormatted error ->
    Result.fail (Error.of_string error)

let from_file file =
  file
  |> In_channel.create
  |> Lexing.from_channel
  |> parse_from_lexbuf

let from_string str =
  str
  |> Lexing.from_string
  |> parse_from_lexbuf
