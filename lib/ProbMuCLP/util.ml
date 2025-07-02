open Core
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open Problem

let typeinf_query ~print query =
  let senv =
    let vs = Set.Poly.union_list @@ List.map query.args ~f:Term.fvs_of in
    Map.of_set_exn (Set.Poly.map vs ~f:(fun v -> (v, T_real.SReal (*ToDo*))))
  in
  let args =
    List.map query.args
      ~f:
        (Typeinf.typeinf_term ~print ~default:None ~senv_opt:senv
           ~sort_opt:(Some T_real.SReal (*ToDo*)))
  in
  let bound =
    Typeinf.typeinf_term ~print ~default:None ~senv_opt:senv
      ~sort_opt:(Some T_real.SReal (*ToDo*)) query.bound
  in
  { query with args; bound }

let typeinf ~print prob_muclp =
  (* ToDo: infer types of mutually recursive predicates *)
  {
    preds =
      List.map prob_muclp.preds ~f:(fun pred ->
          {
            pred with
            body =
              Typeinf.typeinf_term ~print ~default:(Some T_real.SReal (*ToDo*))
                ~senv_opt:(Map.Poly.of_alist_exn pred.args)
                pred.body;
          });
    query = typeinf_query ~print prob_muclp.query;
  }

let parse_from_lexbuf ~print lexbuf =
  try Ok (typeinf ~print @@ Parser.toplevel Lexer.main lexbuf) with
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

let parse_query_from_lexbuf ~print lexbuf =
  try Ok (typeinf_query ~print @@ Parser.query Lexer.main lexbuf) with
  | Parser.Error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error"
              (LexingHelper.get_position_string lexbuf))
  | Lexer.SyntaxError error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error: %s"
              (LexingHelper.get_position_string lexbuf)
              error)

let from_file ~print =
  In_channel.create >> Lexing.from_channel >> parse_from_lexbuf ~print

let from_string ~print = Lexing.from_string >> parse_from_lexbuf ~print

let query_from_string ~print =
  Lexing.from_string >> parse_query_from_lexbuf ~print

let get_dual _prob_muclp = assert false
(*let pvars = List.map prob_muclp.preds ~f:(fun pred -> pred.name) in
  let subst formula =
    List.fold ~init:formula pvars ~f:(Fn.flip Formula.subst_neg)
  in
  make
    (List.map prob_muclp.preds ~f:(fun pred ->
         {
           pred with
           kind = Predicate.flip_fop pred.kind;
           body = Evaluator.simplify_neg (subst pred.body);
         }))
    (Evaluator.simplify_neg (subst prob_muclp.query))*)

let get_greatest_approx prob_muclp =
  make
    (List.map prob_muclp.preds ~f:(fun pred ->
         { pred with kind = Predicate.Nu }))
    prob_muclp.query
