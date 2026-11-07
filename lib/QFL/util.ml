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

(* [arg_sorts]: the parameter sorts of the function a bound query applies, when
   the problem declares it; an argument of an undeclared one is [real] *)
let typeinf_query ~print ?(arg_sorts = []) = function
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
      (* a variable the query quantifies has the sort it is declared with, and
         any other is [real]: reading every variable as [real] typed [x] in
         [forall (x : int). x >= 0 => F x >= 1.0] as an [int] in the
         antecedent and a [real] in the argument, one variable at two sorts *)
      let senv =
        let vs =
          Set.Poly.union_list
          @@ List.map (query.bound :: query.args) ~f:Term.fvs_of
        in
        Map.of_set_exn
          (Set.Poly.map vs ~f:(fun v ->
               ( v,
                 match List.Assoc.find query.params ~equal:Ident.tvar_equal v with
                 | Some s -> s
                 | None -> T_real.SReal (*ToDo*) )))
      in
      let args =
        List.mapi query.args ~f:(fun i arg ->
            Typeinf.typeinf_term ~print ~default:None ~senv
              ~sort_opt:
                (Some
                   (Option.value ~default:T_real.SReal (List.nth arg_sorts i)))
              arg)
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

(* [refuse_ill_sorted what f] is [f ()], with a sort mismatch the type
   inference reports as a [Failure] (an [int] argument used where the body is
   [real], for instance: the language has no implicit conversion) turned into
   a refusal naming [what]; uncaught, it reached the user as a backtrace *)
let refuse_ill_sorted what f =
  try f ()
  with Failure msg when String.is_prefix msg ~prefix:"unification failure" ->
    Common.Refusal.refuse "%s is ill-sorted (%s)" what msg

(* [call_constrs params t] equates the sort of every argument of an application
   of a declared function in [t] with the sort that function declares for that
   parameter.  Bodies are typed one at a time, and the reader gives an
   application's argument the sort of the argument term, so without these a
   variable that is not a parameter and is used only as an argument of another
   function (as [x] in [Z (y : real) : real =mu X x y]) kept an open sort
   variable, which reached Z3 as an unknown sort and crashed the solver; with
   them it takes the declared sort, and an argument of another sort (an [int]
   literal for a [real] parameter) is refused as ill-sorted. *)
let call_constrs params t =
  Set.Poly.union_list
  @@ List.map (Set.to_list @@ Term.fvar_apps_of t) ~f:(function
    | Term.FunApp (FVar (name, sargs, _), _, _) -> (
        match Map.Poly.find params name with
        | Some declared when List.length declared = List.length sargs ->
            Set.Poly.of_list
            @@ List.map2_exn sargs declared ~f:(fun s d -> Typeinf.CEq (s, d))
        | _ -> Set.Poly.empty)
    | _ -> Set.Poly.empty)

let typeinf ~print qfl =
  (* ToDo: infer types of mutually recursive predicates *)
  let params =
    Map.Poly.of_alist_reduce ~f:(fun s _ -> s)
    @@ List.map qfl.preds ~f:(fun (pred : Pred.t) ->
        (pred.name, List.map pred.args ~f:snd))
  in
  {
    preds =
      List.map qfl.preds ~f:(fun pred ->
          let senv = Map.Poly.of_alist_exn pred.args in
          refuse_ill_sorted
            (sprintf "the body of %s" (Ident.name_of_tvar pred.name))
          @@ fun () ->
          {
            pred with
            body =
              Typeinf.typeinf_term ~print ~default:(Some T_real.SReal (*ToDo*))
                ~senv
                ~constrs_opt:(Some (call_constrs params pred.body))
                pred.body;
            annots =
              List.map pred.annots
                ~f:
                  (Typeinf.typeinf_formula ~print
                     ~default:(Some T_real.SReal (*ToDo*)) ~senv);
            arg_constrs =
              List.map pred.arg_constrs
                ~f:
                  (Typeinf.typeinf_formula ~print
                     ~default:(Some T_real.SReal (*ToDo*)) ~senv);
          });
    query =
      (let arg_sorts =
         match qfl.query with
         | Check { name; args; _ } -> (
             match Map.Poly.find params name with
             | Some sorts when List.length sorts = List.length args -> sorts
             | _ -> [])
         | _ -> []
       in
       refuse_ill_sorted "the query" (fun () ->
           typeinf_query ~print ~arg_sorts qfl.query));
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

(* [orient_query qfl] makes the head of a bound query a function of the
   problem.  The reader takes the left side of a comparison as the head when it
   can be one, so [y <= F] for a parameter [y] arrives as a bound on [y] by
   [F]; that is the lower bound [F >= y], and it is turned round.  A query whose
   head names no function of the problem on either side is refused: it used to
   be handed to the solver as a bound on the parameter, which could only fail.
   Returns [qfl] unchanged when its head is a function. *)
let orient_query qfl =
  let is_fun name =
    List.exists qfl.preds ~f:(fun (pred : Pred.t) ->
        Ident.tvar_equal pred.name name)
  in
  match qfl.query with
  | Check ({ name; args; bound; kind; _ } as check) when not (is_fun name) -> (
      let old_head =
        if List.is_empty args then Term.mk_var name (Sort.mk_fresh_svar ())
        else
          Term.mk_fvar_app name
            (List.map args ~f:(fun _ -> T_real.SReal))
            T_real.SReal args
      in
      let swap name' args' =
        let kind = match kind with UB -> LB | LB -> UB in
        { qfl with query = Check { check with name = name'; args = args'; bound = old_head; kind } }
      in
      match bound with
      | Term.Var (name', _, _) when is_fun name' -> swap name' []
      | FunApp (FVar (name', _, _), args', _) when is_fun name' -> swap name' args'
      | _ ->
          Common.Refusal.refuse
            "the query bounds %s, which is not a function of the problem"
            (Ident.name_of_tvar name))
  | _ -> qfl

(* A bound may compare the head with another function application
   ([F 1 <= G 1]); the reader accepts it, and whether the bound checker can
   certify it is the checker's question: it refuses a recursive function in
   the bound and a head not monotone in the ones it applies. *)
let parse_from_lexbuf ~print lexbuf =
  try
    let qfl = orient_query @@ Parser.toplevel Lexer.main lexbuf in
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
