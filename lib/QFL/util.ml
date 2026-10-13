(* Reading and type inference for QFL problems (the [.qhes] format): the reader
   parses, rejects ill-formed inputs (a function applied to the wrong number of
   arguments, or a parameter named like a function) with a message naming the
   culprit, and infers sorts, defaulting to [Real].  Beside it are two
   transformations used by the solver: [get_greatest_approx], which reads every
   equation as a greatest fixpoint, and [lower_bound_by_unroll], which replaces
   the query's bound by a finite unrolling of the equations.  A problem whose
   functions are tuple-valued, and so does not type as it is, is split into one
   problem per tuple component. *)
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

(* Two mistakes in an input that the type inference below does not report and
   that the solver then trips over far from their cause: a function applied to
   fewer or more arguments than it declares -- the grammar is curried, so
   [F (x - 1.0)] parses for a two-parameter [F] -- and a parameter given the
   name of a function, which the unfolding then reads as that function used
   without its arguments.  The first ended in a list-length mismatch inside a
   substitution, the second in an assertion inside another; both are the
   input's fault, so they are reported as such, naming the function and what
   is wrong with it.  [None] when neither occurs.

   A variable that is not a parameter is NOT one of them: the corpus uses
   such variables on purpose (a nullary function written without arguments,
   the components [@1], [@2] of a tuple-valued bound, symbolic constants), so
   only the two shapes above are refused. *)
let ill_formed qfl =
  let arity =
    Map.Poly.of_alist_reduce ~f:(fun n _ -> n)
    @@ List.map qfl.preds ~f:(fun (pred : Pred.t) ->
        (pred.name, List.length pred.args))
  in
  let arity_error ~where t =
    Set.find_map (Term.fvar_apps_of t) ~f:(function
      | Term.FunApp (FVar (name, _, _), args, _) -> (
          let given = List.length args in
          match Map.Poly.find arity name with
          | Some declared when declared <> given ->
              Some
                (sprintf
                   "%s applies %s to %d argument(s), but %s is declared with \
                    %d parameter(s)"
                   where (Ident.name_of_tvar name) given
                   (Ident.name_of_tvar name) declared)
          | _ -> None)
      | _ -> None)
  in
  let pred_error (pred : Pred.t) =
    let fname = Ident.name_of_tvar pred.name in
    match
      List.find pred.args ~f:(fun (x, _) ->
          match Map.Poly.find arity x with Some n -> n > 0 | None -> false)
    with
    | Some (x, _) ->
        Some
          (sprintf
             "%s has a parameter named %s, which is also the name of a \
              function with parameters; rename one of them"
             fname (Ident.name_of_tvar x))
    | None -> arity_error ~where:(sprintf "the body of %s" fname) pred.body
  in
  match List.find_map qfl.preds ~f:pred_error with
  | Some _ as err -> err
  | None -> (
      let where = "the query" in
      match qfl.query with
      | Check { name; args; _ }
      | DistCheck { name; args; _ }
      | ASAT (Some (name, args), _, _) ->
          arity_error ~where
            (Term.mk_fvar_app name
               (List.map args ~f:(fun _ -> T_real.SReal))
               T_real.SReal args)
      | ASAT (None, _, _) -> None)

let parse_from_lexbuf ~print lexbuf =
  try
    let qfl = Parser.toplevel Lexer.main lexbuf in
    match ill_formed qfl with
    | Some msg -> Or_error.error_string msg
    | None -> (
        try Ok [ typeinf ~print qfl ]
        with exn_ when not (Common.Timer.is_async exn_) ->
          let rec loop i =
            match nth i qfl with None -> [] | Some ith -> ith :: loop (i + 1)
          in
          let res = loop 0 in
          Ok
            (List.map ~f:(typeinf ~print)
            @@ if List.is_empty res then [ qfl ] else res))
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

let from_file ~print filename =
  In_channel.with_file filename ~f:(fun channel ->
      parse_from_lexbuf ~print (Lexing.from_channel channel))

let from_string ~print = Lexing.from_string >> parse_from_lexbuf ~print

let query_from_string ~print =
  Lexing.from_string >> parse_query_from_lexbuf ~print

let get_dual _qfl = assert false
(*let pvars = List.map qfl.preds ~f:(fun pred -> pred.name) in
  let subst formula =
    Formula.subst_negs (Set.Poly.of_list pvars) formula
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
