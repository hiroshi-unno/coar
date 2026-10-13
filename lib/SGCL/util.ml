open Core
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open SgclSyntax

(*
let rec typeinf_stmt ~print stmts =
  stmts
  = Typeinf.typeinf_term ~print ~default:None
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

let from_file ~print filename =
  In_channel.with_file filename ~f:(fun channel ->
      parse_from_lexbuf ~print (Lexing.from_channel channel))

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

let expr_from_file ~print filename =
  In_channel.with_file filename ~f:(fun channel ->
      parse_expr_from_lexbuf ~print (Lexing.from_channel channel))

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

let qfl_kind_of_sgcl_bound_kind = function
  | Program.UB -> QFL.Problem.UB
  | Program.LB -> QFL.Problem.LB

let nonnegative_formula_of_var (var, sort) =
  Formula.geq (Term.mk_var var sort) (T_real.rzero ())

let nonnegative_formulas_of_senv vars = List.map vars ~f:nonnegative_formula_of_var

let nonnegative_domain_of_senv vars =
  Formula.and_of (nonnegative_formulas_of_senv vars)

let used_query_vars vars query_args bound =
  let fvs =
    Set.Poly.union_list (Term.fvs_of bound :: List.map query_args ~f:Term.fvs_of)
  in
  List.filter vars ~f:(fun (var, _) -> Set.mem fvs var)

let nonnegative_query_domain = function
  | [] -> None
  | vars -> Some (nonnegative_domain_of_senv vars)

let str_of_bound_kind kind strict =
  match (kind, strict) with
  | Program.UB, false -> "<="
  | Program.UB, true -> "<"
  | Program.LB, false -> ">="
  | Program.LB, true -> ">"

let str_of_bound (bound : Program.bound option) =
  match bound with
  | None -> "(no explicit expectation bound)"
  | Some bound ->
      sprintf "?Ex[%s] %s %s" (Term.str_of bound.post)
        (str_of_bound_kind bound.kind bound.strict)
        (Term.str_of bound.value)

let str_of_arg_constrs (pred : QFL.Pred.t) =
  sprintf "%s:\n%s" (Ident.name_of_tvar pred.name)
    (match pred.arg_constrs with
    | [] -> "  (none)"
    | constrs ->
        String.concat ~sep:"\n"
        @@ List.map constrs ~f:(fun fml -> sprintf "  %s" (Formula.str_of fml)))

let add_nonnegative_arg_constrs (pred : QFL.Pred.t) =
  {
    pred with
    arg_constrs = nonnegative_formulas_of_senv pred.args @ pred.arg_constrs;
  }

let problem_of ?filename ~print (sgcl : Program.t) =
  let sgcl_for_wpt =
    match sgcl.bound with
    | Some bound -> { sgcl with f = bound.post }
    | None -> sgcl
  in
  let wpt = wpt_of ~print sgcl_for_wpt in
  (* The query form below asks about ONE predicate applied to arguments, and the
     expectation this program computes need not have that shape: a branch gives a
     weighted sum, and a straight-line program gives an expression with no
     predicate in it at all.  What used to happen then was that the first loop
     equation was picked and handed one for every program variable, and the
     expression actually computed was discarded -- so a different question was
     answered and its answer reported as this one's.  A program whose expectation
     is exactly 5 was certified as bounded by 2, because what was proved was
     [L 1 <= 2] for the loop [L x = x] rather than [0.5 * L 0 + 0.5 * 10 <= 2].
     With no loop at all there was no equation to pick and it raised [Failure hd].

     An expression is given a predicate of its own instead, defined to be it, and
     the query asks about that.  The definition is not recursive, so its least
     fixpoint is the expression; the program's variables are its parameters, which
     is what lets a query mention them. *)
  let query_pred, query_name, query_args =
    match wpt.qf with
    | FunApp (FVar (fvar, _, _), args, _) -> (None, fvar, args)
    | qf ->
        let name = Ident.mk_fresh_tvar () in
        (* the parameters are the program variables the expression actually
           mentions, which for a program whose inputs are all assigned is none:
           a query over variables the expression does not use would put them in
           the exported problem for nothing, and a generated name among them is
           not one every backend's reader accepts *)
        let params =
          let fvs = Term.fvs_of qf in
          List.filter sgcl.vars ~f:(fun (x, _) -> Set.mem fvs x)
        in
        ( Some (QFL.Pred.make Predicate.Mu name params qf),
          name,
          List.map params ~f:(fun (x, s) -> Term.mk_var x s) )
  in
  let query =
    match sgcl.bound with
    | Some bound ->
        let query_params = used_query_vars sgcl.vars query_args bound.value in
        QFL.Problem.Check
          {
            params = query_params;
            left = nonnegative_query_domain query_params;
            kind = qfl_kind_of_sgcl_bound_kind bound.kind;
            name = query_name;
            args = query_args;
            bound = bound.value;
            strict = bound.strict;
          }
    | None ->
        let bound = T_real.rone () in
        let query_params = used_query_vars sgcl.vars query_args bound in
        QFL.Problem.Check
          {
            params = query_params;
            left = nonnegative_query_domain query_params;
            kind = QFL.Problem.LB;
            name = query_name;
            args = query_args;
            bound;
            strict = false;
          }
  in
  let qfl =
    QFL.Problem.
      {
        preds =
          List.map
            (Option.to_list query_pred @ PredSet.to_list wpt.equations)
            ~f:add_nonnegative_arg_constrs;
        query;
      }
  in
  print
  @@ lazy
       (sprintf
          "[1. Source]\n\
           benchmark:\n\
           \  %s\n\n\
           program:\n\
           %s\n\n\
           query:\n\
           \  %s\n"
          (Option.value filename ~default:"(unknown)")
          (Program.str_of sgcl) (str_of_bound sgcl.bound));
  print
  @@ lazy
       (sprintf
          "[2. QFL before acceleration]\n\
           query:\n\
           \  %s\n\n\
           predicates:\n\
           %s\n\n\
           entry domain / predicate arg constraints:\n\
           %s\n"
          (QFL.Problem.str_of_query qfl.query)
          (QFL.Pred.str_of_list qfl.preds)
          (String.concat ~sep:"\n" @@ List.map qfl.preds ~f:str_of_arg_constrs));
  qfl
