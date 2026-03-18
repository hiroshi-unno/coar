open Core
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open SgclSyntax

(* 
let rec typeinf_stmt ~print stmts =
    stmts = Typeinf.typeinf_term ~print ~default:None
                ~senv_opt:(Map.Poly.of_alist_exn stmt.args)
                stmt.body *)

let typeinf_eqs ~print (sgcl : Program.t) (eqs : EquationSystem.t) :
    EquationSystem.t =
  {
    qf =
      Typeinf.typeinf_term ~print ~default:(Some T_real.SReal)
        ~senv:(Map.Poly.of_alist_exn sgcl.vars)
        eqs.qf;
    equations =
      PredSet.map
        (fun pred ->
          {
            pred with
            body =
              Typeinf.typeinf_term ~print ~default:(Some T_real.SReal)
                ~senv:(Map.Poly.of_alist_exn sgcl.vars)
                pred.body;
          })
        eqs.equations;
  }

let str_of_all_vars = str_of_sort_env_list Term.str_of_sort

(* parse toplevel *)
let parse_from_lexbuf ~print lexbuf =
  try
    print @@ lazy "Parsing SGCL...";
    let sgcl = Parser.toplevel Lexer.main lexbuf in
    print
    @@ lazy
         (sprintf "*********** SGCL Parsing Result ************\n%s"
            (Program.str_of sgcl));
    Ok sgcl
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
    let sgcl = Parser.expr Lexer.main lexbuf in
    Ok sgcl
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

let rec first_decl_var (sgcl : Program.t) =
  match sgcl.vars with
  | [] -> failwith "No declared variables in the SGCL program."
  | (var, T_real.SReal) :: _ -> Term.mk_var var T_real.SReal
  | _ :: rest -> first_decl_var { sgcl with vars = rest }

let wpt_of ~print (sgcl : Program.t) =
  let result = Program.wpt ~print sgcl in
  print
  @@ lazy
       (sprintf "*********** Weakest Precondition Transformer ************\n%s"
          (EquationSystem.str_of result));
  result

let problem_of ~print sgcl =
  let wpt = wpt_of ~print sgcl in
  let query =
    QFL.Problem.Check
      {
        params = sgcl.vars;
        left = None;
        kind = QFL.Problem.LB;
        name =
          (wpt.equations |> PredSet.to_list |> List.hd_exn |> fun p -> p.name);
        args = List.map sgcl.vars ~f:(fun _ -> T_real.rone ());
        bound = T_real.rone ();
        strict = false;
      }
  in
  QFL.Problem.{ preds = PredSet.to_list wpt.equations; query }
