open Core
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open PgclSyntax

(*
let rec typeinf_stmt ~print stmts =
  stmts
  = Typeinf.typeinf_term ~print ~default:None
      ~senv_opt:(Map.Poly.of_alist_exn stmt.args)
      stmt.body *)

let typeinf_eqs ~print (pgcl : Program.t) (eqs : EquationSystem.t) :
    EquationSystem.t =
  let senv = Map.Poly.of_alist_exn @@ Program.sort_env_list_of_decls pgcl in
  {
    qf =
      Typeinf.typeinf_term ~print ~default:(Some T_real.SReal)
        ~senv eqs.qf;
    equations =
      PredSet.map
        (fun pred ->
          {
            pred with
            body =
              Typeinf.typeinf_term ~print ~default:(Some T_real.SReal)
                ~senv pred.body;
          })
        eqs.equations;
  }

let typeinf_term ~print (pgcl : Program.t) term =
  Typeinf.typeinf_term ~print ~default:(Some T_real.SReal)
    ~senv:(Map.Poly.of_alist_exn @@ Program.sort_env_list_of_decls pgcl)
    term

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

let from_file ~print filename =
  In_channel.with_file filename ~f:(fun channel ->
      parse_from_lexbuf ~print (Lexing.from_channel channel))

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

let expr_from_file ~print filename =
  In_channel.with_file filename ~f:(fun channel ->
      parse_expr_from_lexbuf ~print (Lexing.from_channel channel))

let rec first_decl_var (pgcl : Program.t) =
  match pgcl.vars with
  | [] -> failwith "No declared variables in the pGCL program."
  | (var, T_real.SReal) :: _ -> Term.mk_var var T_real.SReal
  | _ :: rest -> first_decl_var { pgcl with vars = rest }

let wpt_of ~print ?f (pgcl : Program.t) =
  let result = Program.wpt ~print:(fun _ -> ()) ?f pgcl |> typeinf_eqs ~print pgcl in
  print
  @@ lazy
       (sprintf "*********** Weakest Precondition Transformer ************\n%s"
          (EquationSystem.str_of result));
  result

let qfl_kind_of_pgcl_bound_kind = function
  | Query.Upper -> QFL.Problem.UB
  | Query.Lower -> QFL.Problem.LB

let is_nat_var pgcl var = List.mem pgcl.Program.nat_vars var ~equal:Ident.tvar_equal

let nonnegative_formula_of_var (var, sort) =
  Formula.geq (Term.mk_var var sort) (T_real.rzero ())

let nonnegative_formulas_of_nat_senv pgcl vars =
  vars |> List.filter ~f:(fun (var, _) -> is_nat_var pgcl var)
  |> List.map ~f:nonnegative_formula_of_var

let used_query_vars vars query_args bound =
  let fvs =
    Set.Poly.union_list (Term.fvs_of bound :: List.map query_args ~f:Term.fvs_of)
  in
  List.filter vars ~f:(fun (var, _) -> Set.mem fvs var)

let nonnegative_query_domain pgcl vars =
  match nonnegative_formulas_of_nat_senv pgcl vars with
  | [] -> None
  | constrs -> Some (Formula.and_of constrs)

let add_nat_arg_constrs pgcl (pred : QFL.Pred.t) =
  {
    pred with
    arg_constrs = nonnegative_formulas_of_nat_senv pgcl pred.args @ pred.arg_constrs;
  }

let post_predicate_of_query pgcl post =
  let open QFL in
  let name = Ident.mk_fresh_tvar () in
  let params = Program.sort_env_list_of_decls pgcl in
  let args = List.map params ~f:(fun (var, sort) -> Term.mk_var var sort) in
  let app = Term.mk_fvar_app name (List.map params ~f:snd) T_real.SReal args in
  let pred =
    Pred.make Predicate.Mu name params (typeinf_term ~print:(fun _ -> ()) pgcl post)
  in
  (pred, app)

let problem_of_bound ~print (pgcl : Program.t) (bound : Query.bound) =
  let open QFL in
  let post_pred, post_app = post_predicate_of_query pgcl bound.post in
  let wpt = wpt_of ~print ~f:post_app pgcl in
  let name', args' =
    match wpt.qf with
    | FunApp (FVar (fvar, _, _), args, _) -> (fvar, args)
    | _ -> failwith "problem_of: missing predicate for query"
  in
  let query =
    let query_params =
      used_query_vars (Program.sort_env_list_of_decls pgcl) args' bound.value
    in
    Problem.Check
      {
        params = query_params;
        left = nonnegative_query_domain pgcl query_params;
        kind = qfl_kind_of_pgcl_bound_kind bound.kind;
        name = name';
        args = args';
        bound = typeinf_term ~print pgcl bound.value;
        strict = bound.strict;
      }
  in
  Problem.
    {
      preds = List.map (post_pred :: PredSet.to_list wpt.equations) ~f:(add_nat_arg_constrs pgcl);
      query;
    }

let problem_of ~print (pgcl : Program.t) =
  match Query.bound_of pgcl.query with
  | Some bound -> Some (problem_of_bound ~print pgcl bound)
  | None ->
      let (_ : EquationSystem.t) = wpt_of ~print pgcl in
      None
