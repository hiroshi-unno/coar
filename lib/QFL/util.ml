open Core
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open Problem

let typeinf_query ~print = function
  | ASAT (init, param_senv, param_constr) ->
      let senv = Map.Poly.of_alist_exn param_senv in
      ASAT
        ( Option.map init ~f:(fun (var, args) ->
              ( var,
                List.map
                  ~f:(Typeinf.typeinf_term ~print ~default:None ~senv)
                  args )),
          param_senv,
          Typeinf.typeinf_formula ~print ~default:None ~senv param_constr )
  | Check query ->
      let senv =
        let vs = Set.Poly.union_list @@ List.map query.args ~f:Term.fvs_of in
        Map.of_set_exn
          (Set.Poly.map vs ~f:(fun v -> (v, T_real.SReal (*ToDo*))))
      in
      let args =
        List.map query.args
          ~f:
            (Typeinf.typeinf_term ~print ~default:None ~senv
               ~sort_opt:(Some T_real.SReal (*ToDo*)))
      in
      let bound =
        Typeinf.typeinf_term ~print ~default:None ~senv
          ~sort_opt:(Some T_real.SReal (*ToDo*)) query.bound
      in
      if Term.is_real_sort @@ Term.sort_of bound then
        Check { query with args; bound }
      else failwith "Query bound is not of real sort"
  | DistCheck query ->
      let args =
        List.map query.args ~f:(Typeinf.typeinf_term ~print ~default:None)
      in
      let params = query.params in
      let bound =
        Typeinf.typeinf_formula ~print ~default:None
          ~senv:(Map.Poly.of_alist_exn params)
          query.bound
      in
      DistCheck { name = query.name; args; params; bound }

let typeinf ~print qfl =
  (* ToDo: infer types of mutually recursive predicates *)
  {
    preds =
      List.map qfl.preds ~f:(fun pred ->
          let senv = Map.Poly.of_alist_exn pred.args in
          {
            pred with
            body =
              Typeinf.typeinf_term ~print ~default:(Some T_real.SReal (*ToDo*))
                ~senv pred.body;
            annots =
              List.map pred.annots
                ~f:
                  (Typeinf.typeinf_formula ~print
                     ~default:(Some T_real.SReal (*ToDo*)) ~senv);
          });
    query = typeinf_query ~print qfl.query;
  }

let parse_from_lexbuf ~print lexbuf =
  try
    let qfl = Parser.toplevel Lexer.main lexbuf in
    try Ok [ typeinf ~print qfl ]
    with _ ->
      let rec loop i =
        match nth i qfl with None -> [] | Some ith -> ith :: loop (i + 1)
      in
      let res = loop 0 in
      Ok
        (List.map ~f:(typeinf ~print)
        @@ if List.is_empty res then [ qfl ] else res)
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

let get_dual _qfl = assert false
(*let pvars = List.map qfl.preds ~f:(fun pred -> pred.name) in
  let subst formula =
    List.fold ~init:formula pvars ~f:(Fn.flip Formula.subst_neg)
  in
  make
    (List.map qfl.preds ~f:(fun pred ->
         {
           pred with
           kind = Predicate.flip_fop pred.kind;
           body = Evaluator.simplify_neg (subst pred.body);
         }))
    (Evaluator.simplify_neg (subst qfl.query))*)

let get_greatest_approx qfl =
  make
    (List.map qfl.preds ~f:(fun pred -> { pred with kind = Predicate.Nu }))
    qfl.query

let lower_bound_by_unroll qfl n ~print =
  let unrolled = Problem.unroll qfl n in
  print
  @@ lazy
       (sprintf "Lower bound by unrolling %d times:\n %s" n
          (Term.str_of unrolled));
  let qfl' = Problem.replace_bound_with qfl unrolled in
  qfl'
