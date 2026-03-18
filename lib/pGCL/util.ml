open Core
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open PgclSyntax

(* 
let rec typeinf_stmt ~print stmts =
    stmts = Typeinf.typeinf_term ~print ~default:None
                ~senv_opt:(Map.Poly.of_alist_exn stmt.args)
                stmt.body *)

let typeinf_eqs ~print (pgcl : Program.t) (eqs : EquationSystem.t) :
    EquationSystem.t =
  {
    qf =
      Typeinf.typeinf_term ~print ~default:(Some T_real.SReal)
        ~senv:(Map.Poly.of_alist_exn @@ Program.sort_env_list_of_decls pgcl)
        eqs.qf;
    equations =
      PredSet.map
        (fun pred ->
          {
            pred with
            body =
              Typeinf.typeinf_term ~print ~default:(Some T_real.SReal)
                ~senv:
                  (Map.Poly.of_alist_exn @@ Program.sort_env_list_of_decls pgcl)
                pred.body;
          })
        eqs.equations;
  }

let str_of_all_vars = str_of_sort_env_list Term.str_of_sort

(* parse toplevel *)
let parse_from_lexbuf ~print lexbuf =
  try
    print @@ lazy "Parsing pGCL...";
    let pgcl =
      Parser.toplevel Lexer.main lexbuf |> fun pgcl ->
      { pgcl with consts = Program.typeinf_consts ~print pgcl }
    in
    print
    @@ lazy
         (sprintf "*********** pGCL Parsing Result ************\n%s"
            (Program.str_of pgcl));
    Ok pgcl
  with
  | Parser.Error ->
      print_endline
      @@ sprintf "%s: syntax error" (LexingHelper.get_position_string lexbuf);
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error"
              (LexingHelper.get_position_string lexbuf))
  | Lexer.SyntaxError error ->
      print_endline
      @@ sprintf "%s: syntax error" (LexingHelper.get_position_string lexbuf);
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error: %s"
              (LexingHelper.get_position_string lexbuf)
              error)

let from_file ~print =
  In_channel.create >> Lexing.from_channel >> parse_from_lexbuf ~print

let from_string ~print = Lexing.from_string >> parse_from_lexbuf ~print

(* parse expr *)
let parse_expr_from_lexbuf ~print lexbuf =
  try
    print @@ lazy "Parsing expression...";
    let pgcl = Parser.expr Lexer.main lexbuf in
    Ok pgcl
  with
  | Parser.Error ->
      print_endline
      @@ sprintf "%s: syntax error" (LexingHelper.get_position_string lexbuf);
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error"
              (LexingHelper.get_position_string lexbuf))
  | Lexer.SyntaxError error ->
      print_endline
      @@ sprintf "%s: syntax error" (LexingHelper.get_position_string lexbuf);
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error: %s"
              (LexingHelper.get_position_string lexbuf)
              error)

let expr_from_string ~print =
  Lexing.from_string >> parse_expr_from_lexbuf ~print

let expr_from_file ~print =
  In_channel.create >> Lexing.from_channel >> parse_expr_from_lexbuf ~print

let rec first_decl_var (pgcl : Program.t) =
  match pgcl.vars with
  | [] -> failwith "No declared variables in the pGCL program."
  | (var, T_real.SReal) :: _ -> Term.mk_var var T_real.SReal
  | _ :: rest -> first_decl_var { pgcl with vars = rest }

let wpt_of ~print ?f (pgcl : Program.t) =
  let result = Program.wpt ~print:(fun _ -> ()) ?f pgcl in
  print
  @@ lazy
       (sprintf "*********** Weakest Precondition Transformer ************\n%s"
          (EquationSystem.str_of result));
  result

let problem_of ~print ?f pgcl =
  let open QFL in
  let wpt = wpt_of ~print ?f pgcl in
  let name', args' =
    match wpt.qf with
    | FunApp (FVar (fvar, _, _), args, _) -> (fvar, args)
    | _ -> failwith "problem_of: missing predicate for query"
  in
  let query =
    Problem.Check
      {
        params = Program.sort_env_list_of_decls pgcl;
        left = None;
        kind = Problem.LB;
        name = name';
        args = args';
        bound = T_real.rzero ();
        strict = false;
      }
  in
  Problem.{ preds = PredSet.to_list wpt.equations; query }
