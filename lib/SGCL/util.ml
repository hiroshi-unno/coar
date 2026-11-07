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

(* [infer_sorts ~print sgcl] decides which variables are integers and gives
   every expression of the program its sort.

   SGCL declares no variables.  The language is that of Diabolo (Zaiser,
   Murawski and Ong, POPL 2025), whose programs are discrete: its
   distributions -- [UniformDisc(a, b)], [Geometric(p)], [Bernoulli(p)] -- are
   supported on the naturals and its literals in assignments are integers.  So
   a variable is an integer unless the program makes it real: it is real when
   it is assigned, incremented by or compared with something real -- a decimal
   literal such as [0.5], an exact division [a / b], or another real variable.
   This is one type inference over the whole program, in which every numeral
   and every [+] or [-] is sort-polymorphic, [/] is real, and whatever remains
   undetermined is an integer.  A probability is a real.  The return variable
   and the expectation in a bound are real-valued: an integer one is converted
   to a real.

   Real is always a safe reading of an SGCL variable, since the language has
   no operation that differs between the integers and the reals (no integer
   division, no remainder); what the integer reading adds is that the bound
   is asked about integer states only, and that a guard [x < 1] excludes the
   states between 0 and 1, which no run of the program visits.  Before this,
   every variable was read as a real. *)
let infer_sorts ~print (sgcl : Program.t) : Program.t =
  let attempt f =
    try Some (f ()) with exn_ when not (Common.Timer.is_async exn_) -> None
  in
  let fail what x =
    Common.Refusal.refuse "%s %s does not have a consistent sort" what x
  in
  let real_constraint p = Formula.eq p (T_real.rzero ()) in
  let rec constraints : Statement.t -> Formula.t list = function
    | IF (c, s1, s2) -> (c :: constraints s1) @ constraints s2
    | WHILE (c, s) -> c :: constraints s
    | WHILE_FLIP (p, s) -> real_constraint p :: constraints s
    | ASSIGN (x, t) -> [ Formula.eq (Term.mk_var x (Sort.mk_fresh_svar ())) t ]
    | PLUSASSIGN (x, t) | MINUSASSIGN (x, t) ->
        let v = Term.mk_var x (Sort.mk_fresh_svar ()) in
        [ Formula.eq v (T_num.mk_nadd v t) ]
    | COMPOUND (s1, s2) -> constraints s1 @ constraints s2
    | CHOICE (p, s1, s2) ->
        (real_constraint p :: constraints s1) @ constraints s2
    | OBSERVE c -> [ c ]
    | SKIP -> []
  in
  let bound_terms =
    match sgcl.bound with None -> [] | Some b -> [ b.post; b.value ]
  in
  let whole =
    Formula.and_of
    @@ constraints sgcl.stmts
    @ List.map (sgcl.f :: bound_terms) ~f:(fun t -> Formula.eq t t)
  in
  let senv =
    match
      attempt (fun () ->
          Typeinf.typeinf_formula ~print ~default:(Some T_int.SInt) whole)
    with
    | None -> fail "the program" "(a variable or an expression)"
    | Some typed ->
        Formula.term_sort_env_of typed
        |> Set.to_list
        |> List.map ~f:(fun (x, s) ->
               (x, match s with Sort.SVar _ -> T_int.SInt | s -> s))
        |> Map.Poly.of_alist_reduce ~f:(fun s _ -> s)
  in
  let infer ?(default = T_int.SInt) ?sort_opt t =
    match
      attempt (fun () ->
          Typeinf.typeinf_term ~print ~default:(Some default) ~senv ~sort_opt t)
    with
    | Some t -> t
    | None -> fail "the expression" (Term.str_of t)
  in
  let formula c =
    match
      attempt (fun () ->
          Typeinf.typeinf_formula ~print ~default:(Some T_int.SInt) ~senv c)
    with
    | Some c -> c
    | None -> fail "the condition" (Formula.str_of c)
  in
  let real_valued t =
    let t = infer ~default:T_real.SReal t in
    if Term.is_int_sort (Term.sort_of t) then T_irb.mk_int_to_real t
    else if Term.is_real_sort (Term.sort_of t) then t
    else infer ~sort_opt:T_real.SReal t
  in
  let sort_of x =
    Option.value (Map.Poly.find senv x) ~default:T_int.SInt
  in
  let rec stmt : Statement.t -> Statement.t = function
    | IF (c, s1, s2) -> IF (formula c, stmt s1, stmt s2)
    | WHILE (c, s) -> WHILE (formula c, stmt s)
    | WHILE_FLIP (p, s) -> WHILE_FLIP (infer ~sort_opt:T_real.SReal p, stmt s)
    | ASSIGN (x, t) -> ASSIGN (x, infer ~sort_opt:(sort_of x) t)
    | PLUSASSIGN (x, t) -> PLUSASSIGN (x, infer ~sort_opt:(sort_of x) t)
    | MINUSASSIGN (x, t) -> MINUSASSIGN (x, infer ~sort_opt:(sort_of x) t)
    | COMPOUND (s1, s2) -> COMPOUND (stmt s1, stmt s2)
    | CHOICE (p, s1, s2) ->
        CHOICE (infer ~sort_opt:T_real.SReal p, stmt s1, stmt s2)
    | OBSERVE c -> OBSERVE (formula c)
    | SKIP -> SKIP
  in
  {
    vars =
      List.map sgcl.vars ~f:(fun (x, _) -> (x, sort_of x))
      |> List.dedup_and_sort ~compare:(fun (x, _) (y, _) ->
             Ident.tvar_compare x y);
    stmts = stmt sgcl.stmts;
    f = real_valued sgcl.f;
    bound =
      Option.map sgcl.bound ~f:(fun b ->
          { b with post = real_valued b.post; value = real_valued b.value });
  }

(* [truncate_subtractions sgcl] makes every subtraction on integers truncated
   at 0 (monus, [a -. b = max(a - b, 0)]); it expects the sorts given by
   [infer_sorts].

   Semantics.  In Diabolo's language (Zaiser, Murawski and Ong, "Guaranteed
   Bounds on Posterior Distributions of Discrete Probabilistic Programs with
   Loops", POPL 2025, Section 2.2) every program variable ranges over the
   natural numbers and decrement is truncated: [X -= 1] is
   [X := max(X - 1, 0)].  Diabolo's programs subtract only in [x -= c] with
   [c] a numeral; this reader also accepts a binary [-], which on integers is
   read the same way:
   - [x -= t] on an integer [x] is [x := x -. t];
   - [a - b] whose operands are integers is [a -. b] when an operand mentions a
     variable, or, between numerals, in a value assigned to (or added to) an
     integer variable; elsewhere a subtraction of numerals is ordinary;
   - a subtraction on a real variable (one [infer_sorts] made real; Diabolo has
     none) stays the real one.  The two are told apart by the sort: after
     typing an integer subtraction is [T_int.Sub], a real one [T_real.RSub].
   Since numerals are natural and [+], [*] and monus keep the naturals, every
   integer variable stays non-negative along every run, which is what the
   reduction's non-negativity constraint on the equations' arguments assumes.

   Encoding.  [a -. b] becomes [ite(a >= b, a - b, 0)], equal to
   [max(a - b, 0)] on all integers.  An assignment whose value then contains
   such an [ite] is split into an [if] over the cases of [Term.elim_ite]
   (disjoint, exhaustive, each assigning an [ite]-free value), so the weakest
   preexpectation applies a loop function to arithmetic arguments only; a
   guard or an observed condition has its [ite]s lifted ([Formula.elim_ite]);
   in an expectation, a bound or a weight the [ite] stays a term.  Every
   operation used ([-], [>=], [ite]) is one the bound checker relaxes from the
   integers to the reals soundly.  The [ite] is not built when [a >= b] is
   known at that point: [b] is the numeral 0, or [a] is a variable that a
   known atom bounds below by at least the numeral [b] -- so the body of
   [while x > 0 { x -= 1; }] stays [x := x - 1].  The known atoms
   under-approximate what holds at a point: a guard's atoms (its negation's,
   in an [else] and after a loop) enter its branches, an observed condition's
   follow it, and an assignment, or a statement whose branches or body
   assign, removes every atom over the variables it assigns. *)
let truncate_subtractions (sgcl : Program.t) : Program.t =
  let int_vars =
    List.filter_map sgcl.vars ~f:(fun (x, s) ->
        if Term.is_int_sort s then Some x else None)
  in
  let is_int_var x = List.mem int_vars x ~equal:Ident.tvar_equal in
  let int_literal = function
    | Term.FunApp (T_int.Int n, [], _) -> Some n
    | _ -> None
  in
  (* the greatest lower bound on [x] that one of [facts] states, if any *)
  let lower_bound facts x =
    List.filter_map facts ~f:(function
      | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) -> (
          let is_x = function
            | Term.Var (y, _, _) -> Ident.tvar_equal x y
            | _ -> false
          in
          match (psym, int_literal t1, int_literal t2) with
          | (T_int.Geq | T_bool.Eq), None, Some m when is_x t1 -> Some m
          | T_int.Gt, None, Some m when is_x t1 -> Some Z.(m + one)
          | (T_int.Leq | T_bool.Eq), Some m, None when is_x t2 -> Some m
          | T_int.Lt, Some m, None when is_x t2 -> Some Z.(m + one)
          (* every integer variable is non-negative (see above), so
             [x != 0] means [x >= 1] *)
          | T_bool.Neq, None, Some m when is_x t1 && Z.(equal m zero) ->
              Some Z.one
          | T_bool.Neq, Some m, None when is_x t2 && Z.(equal m zero) ->
              Some Z.one
          | _ -> None)
      | _ -> None)
    |> List.max_elt ~compare:Z.compare
  in
  let known_geq ~facts a b =
    match (int_literal b, a) with
    | Some k, _ when Z.(equal k zero) -> true
    | Some k, Term.Var (x, _, _) -> (
        match lower_bound facts x with Some m -> Z.geq m k | None -> false)
    | _ -> false
  in
  (* rewrites one integer subtraction, whose operands have already been
     rewritten (the traversal is bottom-up), counting the [ite]s in [built] *)
  let monus_node ~built ~ctx ~facts = function
    | Term.FunApp (T_int.Sub, [ a; b ], _) as t
      when ctx
           || not (Set.is_empty (Set.union (Term.fvs_of a) (Term.fvs_of b))) ->
        if known_geq ~facts a b then t
        else (
          incr built;
          T_bool.mk_if_then_else
            (T_bool.of_atom (T_int.mk_geq a b))
            t (T_int.zero ()))
    | t -> t
  in
  let monus ~built ~ctx ~facts = Term.map_term true ~f:(monus_node ~built ~ctx ~facts) in
  let cond ~facts phi =
    let built = ref 0 in
    let phi = Formula.map_term phi ~f:(monus_node ~built ~ctx:false ~facts) in
    if !built > 0 then Formula.elim_ite phi else phi
  in
  let weight t = monus ~built:(ref 0) ~ctx:false ~facts:[] t in
  (* [x := t] on an integer [x], with [t] still to be truncated *)
  let assign ~facts x t : Statement.t =
    let built = ref 0 in
    let t = monus ~built ~ctx:true ~facts t in
    if !built = 0 then ASSIGN (x, t)
    else
      match List.rev (Term.elim_ite t) with
      | [] -> ASSIGN (x, t)
      | (_, t_last) :: cases ->
          List.fold cases ~init:(Statement.ASSIGN (x, t_last))
            ~f:(fun rest (c, t) ->
              Statement.IF (Evaluator.simplify c, ASSIGN (x, t), rest))
  in
  let rec assigned_vars : Statement.t -> Ident.tvar Set.Poly.t = function
    | ASSIGN (x, _) | PLUSASSIGN (x, _) | MINUSASSIGN (x, _) ->
        Set.Poly.singleton x
    | s ->
        Set.Poly.union_list
          (List.map (Statement.get_inner_statements s) ~f:assigned_vars)
  in
  let kill vars facts =
    List.filter facts ~f:(fun phi ->
        Set.is_empty (Set.inter (Formula.fvs_of phi) vars))
  in
  let atoms_of phi = Set.to_list (Formula.conjuncts_of phi) in
  let rec stmt facts : Statement.t -> Statement.t * Formula.t list = function
    | IF (c, s1, s2) as s ->
        let c = cond ~facts c in
        let s1, _ = stmt (facts @ atoms_of c) s1 in
        let s2, _ = stmt (facts @ atoms_of (Formula.negate c)) s2 in
        (IF (c, s1, s2), kill (assigned_vars s) facts)
    | WHILE (c, body) as s ->
        let outside = kill (assigned_vars s) facts in
        let c = cond ~facts:outside c in
        let body, _ = stmt (outside @ atoms_of c) body in
        (WHILE (c, body), outside @ atoms_of (Formula.negate c))
    | WHILE_FLIP (p, body) as s ->
        let outside = kill (assigned_vars s) facts in
        let body, _ = stmt outside body in
        (WHILE_FLIP (weight p, body), outside)
    | CHOICE (p, s1, s2) as s ->
        let s1, _ = stmt facts s1 in
        let s2, _ = stmt facts s2 in
        (CHOICE (weight p, s1, s2), kill (assigned_vars s) facts)
    | ASSIGN (x, t) when is_int_var x ->
        (assign ~facts x t, kill (Set.Poly.singleton x) facts)
    | PLUSASSIGN (x, t) when is_int_var x ->
        let built = ref 0 in
        let t' = monus ~built ~ctx:true ~facts t in
        ( (if !built = 0 then PLUSASSIGN (x, t')
           else assign ~facts x (T_int.mk_add (Term.mk_var x T_int.SInt) t)),
          kill (Set.Poly.singleton x) facts )
    | MINUSASSIGN (x, t) when is_int_var x ->
        ( assign ~facts x (T_int.mk_sub (Term.mk_var x T_int.SInt) t),
          kill (Set.Poly.singleton x) facts )
    | (ASSIGN (x, _) | PLUSASSIGN (x, _) | MINUSASSIGN (x, _)) as s ->
        (s, kill (Set.Poly.singleton x) facts)
    | COMPOUND (s1, s2) ->
        let s1, facts = stmt facts s1 in
        let s2, facts = stmt facts s2 in
        (COMPOUND (s1, s2), facts)
    | OBSERVE c ->
        let c = cond ~facts c in
        (OBSERVE c, facts @ atoms_of c)
    | SKIP -> (SKIP, facts)
  in
  {
    sgcl with
    stmts = fst (stmt [] sgcl.stmts);
    f = weight sgcl.f;
    bound =
      Option.map sgcl.bound ~f:(fun b ->
          { b with post = weight b.post; value = weight b.value });
  }

(* [validate sgcl] refuses, through [Common.Refusal], a program the reduction
   would give a meaning other than its own; it returns [()] otherwise.

   A probability that is a closed expression must lie in [0, 1]: the
   weakest-preexpectation rules [p * wp(S1, f) + (1 - p) * wp(S2, f)] for a
   choice and [p * wp(S; loop, f) + (1 - p) * f] for [while flip(p)] are
   expectation transformers only there, and outside it a branch is weighted
   negatively.  A probability that mentions a program variable is not
   checked here: a run that reaches it outside [0, 1] is an error, resolved
   against the bound by [Program.wpt] and [problem_of].  What a
   bound on a program with [observe] requires is checked by
   [reduce_conditional]. *)
let validate (sgcl : Program.t) =
  let check_probability ~what p =
    if Set.is_empty (Term.fvs_of p) then
      match Evaluator.simplify_term p with
      | t when T_real.is_real t ->
          let q = T_real.let_real t in
          if Q.(lt q zero || gt q one) then
            Common.Refusal.refuse "the probability %s of %s is outside [0, 1]"
              (Q.to_string q) what
      | _ -> ()
  in
  let rec walk = function
    | Statement.CHOICE (p, s1, s2) ->
        check_probability ~what:"a probabilistic choice" p;
        walk s1;
        walk s2
    | WHILE_FLIP (p, s) ->
        check_probability ~what:"a `while flip` loop" p;
        walk s
    | stmt -> List.iter (Statement.get_inner_statements stmt) ~f:walk
  in
  walk sgcl.stmts

(* parse toplevel *)
let parse_from_lexbuf ~print lexbuf =
  try
    print @@ lazy "Parsing SGCL...";
    let sgcl =
      truncate_subtractions @@ infer_sorts ~print
      @@ Parser.toplevel Lexer.main lexbuf
    in
    validate sgcl;
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
    (* an expression read alone is inferred as [infer_sorts] infers a
       program: whatever nothing makes real is an integer *)
    let expr =
      Parser.expr Lexer.main lexbuf
      |> Typeinf.typeinf_term ~print ~default:(Some T_int.SInt)
    in
    Ok expr
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

let wpt_of ~print ?fail ?err (sgcl : Program.t) =
  let result = Program.wpt ~print ?fail ?err sgcl in
  print
  @@ lazy
       (sprintf "*********** Weakest Precondition Transformer ************\n%s"
          (EquationSystem.str_of result));
  result

let qfl_kind_of_sgcl_bound_kind = function
  | Program.UB -> QFL.Problem.UB
  | Program.LB -> QFL.Problem.LB

let nonnegative_formula_of_var (var, sort) =
  Formula.geq (Term.mk_var var sort)
    (if Term.is_int_sort sort then T_int.zero () else T_real.rzero ())

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

let rec has_observe stmt =
  Statement.is_observe stmt
  || List.exists (Statement.get_inner_statements stmt) ~f:has_observe

let rec has_loop stmt =
  Statement.is_while stmt || Statement.is_while_flip stmt
  || List.exists (Statement.get_inner_statements stmt) ~f:has_loop

(* [has_state_weight stmt]: [stmt] contains a choice or a [while flip(p)]
   whose weight mentions a variable, the only kinds [Program.wpt] guards with
   an error value (a closed weight is checked to be a probability before the
   reduction). *)
let rec has_state_weight stmt =
  (match stmt with
  | Statement.CHOICE (p, _, _) | Statement.WHILE_FLIP (p, _) ->
      not (Set.is_empty (Term.fvs_of p))
  | _ -> false)
  || List.exists (Statement.get_inner_statements stmt) ~f:has_state_weight

let real_value_of t =
  if Set.is_empty (Term.fvs_of t) then
    match Evaluator.simplify_term t with
    | t when T_real.is_real t -> Some (T_real.let_real t)
    | _ -> None
  else None

(* [bounded_by_one t]: every value of [t] lies in [0, 1], seen syntactically:
   each leaf of its if-then-else tree is a constant in [0, 1] (an indicator
   [[b]] is [if b then 1 else 0]).  A sufficient check, not a decision. *)
let rec bounded_by_one = function
  | Term.FunApp (T_bool.IfThenElse, [ _; t1; t2 ], _) ->
      bounded_by_one t1 && bounded_by_one t2
  | t -> (
      match real_value_of t with
      | Some v -> Q.(geq v zero && leq v one)
      | None -> false)

(* [feasibility ~print ~strict sgcl] is the condition, over the initial
   state, under which the normaliser [wlp(S, 1)] -- the probability that a
   run is not blocked by an observation -- is positive, as [None] when it
   holds everywhere the reduction can see; it refuses an infeasible program.
   The reduction [num ⋈ q * den] is sound only where [den > 0]: where every
   run is blocked the conditional expectation is undefined (Olmedo et al.,
   TOPLAS 2018, call the program infeasible there), while the reduced query
   [0 + q * 1 ⋈ q] holds vacuously (non-strict) or fails (strict).  A
   loop-free program's blocking probability [wp(S, 0)] with a failed
   observation worth 1 is an expression, so [den = 1 - wp(S, 0)] is too: a
   closed one that is 0 makes the program infeasible, and one over the inputs
   becomes the query's antecedent [den > 0], which is said on stderr.  With a
   loop [den] is a fixpoint, which the antecedent cannot state soundly (the
   checker approximates a recursive function in the antecedent the wrong way
   round), so a strict bound is refused and a non-strict one is reduced with
   the note that its verdict speaks of the feasible initial states only. *)
let feasibility ~print ~strict (sgcl : Program.t) =
  if has_loop sgcl.stmts then (
    if strict then
      Common.Refusal.refuse
        "a strict bound on a program with observe and a loop is not reduced: \
         it holds only where some run passes the observations, which is a \
         fixpoint the query cannot assume";
    eprintf
      "note: on a program with observe and a loop the bound is checked at the \
       feasible initial states only: where every run is blocked the \
       conditional expectation is undefined and the reduced query holds \
       vacuously\n%!";
    None)
  else
    let blocked =
      (wpt_of ~print ~fail:(T_real.rone ()) { sgcl with f = T_real.rzero () })
        .qf
    in
    let den = Evaluator.simplify_term (T_real.mk_rsub (T_real.rone ()) blocked) in
    match real_value_of den with
    | Some d when Q.(leq d zero) ->
        Common.Refusal.refuse
          "infeasible: every run of the program is blocked by an observation, \
           so its conditional expectation is undefined"
    | Some _ -> None
    | None ->
        let feasible = Formula.gt den (T_real.rzero ()) in
        eprintf
          "note: the bound is checked at the initial states where %s; the \
           program is infeasible at the others\n%!"
          (Formula.str_of feasible);
        Some feasible

(* [reduce_conditional ~print sgcl bound] reduces a bound on the conditional
   expectation [bound.transformer] names to a bound on one least fixpoint: it
   returns [(post, fail, kind, value, antecedent)] such that, at every initial
   state satisfying [antecedent], the bound holds iff
   [wp_fail(S, post) kind value], where [wp_fail] is [Program.wpt] with a
   failed observation worth [fail] (0 when [None]).  With [N] the numerator,
   [D] the normaliser and [q] the bound, [N / D ⋈ q] iff [N ⋈ q * D] where
   [D > 0], and the two sides are combined into one fixpoint rather than
   compared as two, because the bound checker certifies one direction per
   query (an upper bound by a pre-fixpoint, a lower one by a post-fixpoint
   with a ranking function) and [N ⋈ q * D] needs opposite directions on the
   two sides.  Each run terminates having passed the observations, is
   blocked, or diverges, with probabilities summing to 1 (every choice weight
   is a probability):
   - [cwp]: [N = wp(S, f)], [D = wlp(S, 1) = 1 - P(blocked)], so
     [N ⋈ q * D] iff [wp(S, f) + q * P(blocked) ⋈ q] iff [wp_q(S, f) ⋈ q].
   - [cwlp], for [g] in [0, 1] and [q] in [0, 1]: [N = wlp(S, g) = wp(S, g) +
     P(diverges)], and one minus [N + q * P(blocked)] is
     [wp(S, 1 - g) + (1 - q) * P(blocked) = wp_(1-q)(S, 1 - g)], so
     [N ⋈ q * D] iff [wp_(1-q)(S, 1 - g) ⋈' 1 - q] with [⋈'] the mirrored
     comparison.
   - [r2]: [D = wp(S, 1)].  On a loop-free program every run terminates, so
     [wp(S, 1) = wlp(S, 1)] and [r2] is [cwp].  With a loop, [N ⋈ q * D]
     compares a least fixpoint with [q] times another, which no single least
     fixpoint expresses, and the query is refused.
   Without [observe], [cwp] is [wp(S, f)] and the bound is returned exactly as
   it was given, so such a program reduces as it always has.  The bound must
   be a constant when it enters the program as [fail] (it is the value at
   the initial state, while the program changes the variables), and
   nonnegative, since an expectation is. *)
let reduce_conditional ~print (sgcl : Program.t) (bound : Program.bound) =
  let observes = has_observe sgcl.stmts in
  let constant_bound ~hi ~what =
    match real_value_of bound.value with
    | Some q when Q.(geq q zero) && Option.for_all hi ~f:(fun hi -> Q.(leq q hi))
      ->
        q
    | _ ->
        Common.Refusal.refuse
          "the bound %s of a %s query on a program with observe must be a \
           constant in %s"
          (Term.str_of bound.value) what
          (match hi with None -> "[0, oo)" | Some _ -> "[0, 1]")
  in
  let transformer : Program.transformer =
    match bound.transformer with
    | R2 when has_loop sgcl.stmts ->
        Common.Refusal.refuse
          "an r2 bound on a program with a loop is not reduced: wp(S, f) / \
           wp(S, 1) compares a least fixpoint with a multiple of another, \
           which one certificate of one direction does not bound"
    | R2 -> Cwp
    | t -> t
  in
  match transformer with
  | Cwp when not observes -> (bound.post, None, bound.kind, bound.value, None)
  | Cwp ->
      let q = constant_bound ~hi:None ~what:"cwp" in
      let antecedent = feasibility ~print ~strict:bound.strict sgcl in
      (bound.post, Some (T_real.mk_real q), bound.kind, bound.value, antecedent)
  | Cwlp ->
      if not (bounded_by_one (Evaluator.simplify_term bound.post)) then
        Common.Refusal.refuse
          "the post-expectation %s of a cwlp query must be bounded by 1, and \
           could not be seen to be (write it as a constant or an indicator \
           [b])"
          (Term.str_of bound.post);
      let q = constant_bound ~hi:(Some Q.one) ~what:"cwlp" in
      let antecedent =
        if observes then feasibility ~print ~strict:bound.strict sgcl else None
      in
      ( T_real.mk_rsub (T_real.rone ()) bound.post,
        Some (T_real.mk_real Q.(one - q)),
        (match bound.kind with UB -> LB | LB -> UB),
        T_real.mk_real Q.(one - q),
        antecedent )
  | R2 -> assert false (* turned into [Cwp] above *)

(* [error_value ~transformer kind] is what a run that reaches a probability
   outside [0, 1] is worth in the query [reduce_conditional] returns for a
   bound of [kind] on [transformer].  Such a run is an error from which no
   bound may be proved: it is worth 0 against a lower bound and +oo against an
   upper one, the value that makes the claim hardest.  A [cwp] bound (and an
   [r2] one, reduced as [cwp]) keeps its direction and so its value.  A [cwlp]
   bound is mirrored: the reduced post-expectation is [1 - g], and a run worth
   [v] in [wlp(S, g)] is worth [1 - v] in the reduced [wp], so 0 becomes 1
   (finite, so it is passed to [Program.wpt] as it is) and +oo becomes -oo
   against the reduced lower bound. *)
let error_value ~(transformer : Program.transformer) (kind : Program.kind) =
  match (transformer, kind) with
  | Cwlp, LB -> `Finite (T_real.rone ())
  | Cwlp, UB -> `Minus_infinity
  | (Cwp | R2), LB -> `Finite (T_real.rzero ())
  | (Cwp | R2), UB -> `Plus_infinity

(* [against_infinite_error ~print sgcl ~above ~value qf]: the pair
   [(qf', value')] of a preexpectation and a bound such that [qf' ⋈ value']
   holds exactly where [qf ⋈ value] holds and no run reaching an
   out-of-range probability has positive probability.  [qf] is computed with
   such a run worth 0; the run is worth +oo against an upper bound ([above])
   or -oo against a lower one (the lower bound a cwlp upper bound becomes), so
   [wp] is that infinity wherever [P(error) > 0] and [qf] elsewhere.  No term
   is infinite, and every term of a QFL input must lie in [0, oo] (the checker
   refuses one negative at every state of its guard), so:
   - above: [qf' = ite(P(error) > 0, value + 1, qf)], [value' = value];
     [value + 1 > value] fails [<=] and [<], and [value + 1 >= 0].
   - below: [qf' = ite(P(error) > 0, 0, qf + 1)], [value' = value + 1].
     Where [P(error) = 0] this is [qf + 1 ⋈ value + 1], i.e. [qf ⋈ value].
     Where [P(error) > 0] it is [0 ⋈ value + 1], false for [>=] and [>]
     because [value >= 0] (the only lower bound reaching here is a cwlp upper
     bound [q] in [0, 1] reduced to [1 - q]).  The shift is needed: the error
     arm must lie strictly below the bound, and against a non-strict lower
     bound 0 (a cwlp upper bound 1 becomes one) no value in [0, oo] does;
     [value - 1] is negative there and the whole input was refused.
   Requires a program without a loop: [P(error)] is then an expression over
   the initial state ([wp] with [f = 0], a blocked run worth 0 and an error
   worth 1).  With a loop it is a least fixpoint, and "it is positive" is a
   bound on it in the direction the query's one certificate does not give;
   nor can a finite pre-fixpoint be infinite at an error state, so the query
   is refused rather than answered with an error worth 0, under which an
   upper bound would hold at the error states. *)
let against_infinite_error ~print (sgcl : Program.t) ~above ~value qf =
  if not (has_state_weight sgcl.stmts) then (qf, value)
  else if has_loop sgcl.stmts then
    Common.Refusal.refuse
      "this bound on a program with a loop and a probability over program \
       variables is not reduced: a run reaching a probability outside [0, 1] \
       is worth +oo against an upper bound (-oo against the lower bound a \
       cwlp upper bound becomes), which a certificate of one direction cannot \
       express"
  else
    let p_err =
      Evaluator.simplify_term
        (wpt_of ~print ~fail:(T_real.rzero ()) ~err:(T_real.rone ())
           { sgcl with f = T_real.rzero () })
          .qf
    in
    match real_value_of p_err with
    | Some p when Q.(leq p zero) -> (qf, value)
    | _ ->
        let erroneous =
          T_bool.of_formula (Formula.gt p_err (T_real.rzero ()))
        in
        let plus_one t = T_real.mk_radd t (T_real.rone ()) in
        if above then
          (T_bool.mk_if_then_else erroneous (plus_one value) qf, value)
        else
          ( T_bool.mk_if_then_else erroneous (T_real.rzero ()) (plus_one qf),
            plus_one value )

let problem_of ?filename ~print (sgcl : Program.t) =
  let post, fail, kind, value, antecedent =
    match sgcl.bound with
    | Some bound ->
        let post, fail, kind, value, antecedent =
          reduce_conditional ~print sgcl bound
        in
        (Some post, fail, kind, value, antecedent)
    | None -> (None, None, Program.LB, T_real.rone (), None)
  in
  let sgcl_for_wpt =
    match post with Some post -> { sgcl with f = post } | None -> sgcl
  in
  let error =
    match sgcl.bound with
    | Some bound -> error_value ~transformer:bound.transformer bound.kind
    | None -> `Finite (T_real.rzero ())
  in
  let err = match error with `Finite v -> Some v | _ -> None in
  let wpt = wpt_of ~print ?fail ?err sgcl_for_wpt in
  let (wpt : EquationSystem.t), value =
    let shifted ~above =
      let qf, value = against_infinite_error ~print sgcl ~above ~value wpt.qf in
      ({ wpt with qf }, value)
    in
    match error with
    | `Finite _ -> (wpt, value)
    | `Plus_infinity -> shifted ~above:true
    | `Minus_infinity -> shifted ~above:false
  in
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
    (* without a bound the query is [>= 1]; the antecedent's variables are
       quantified with the rest, and it has none unless the program has
       [observe] *)
    let query_params =
      used_query_vars sgcl.vars
        (Option.value_map antecedent ~default:query_args ~f:(fun fml ->
             T_bool.of_formula fml :: query_args))
        value
    in
    QFL.Problem.Check
      {
        params = query_params;
        left =
          (match (nonnegative_query_domain query_params, antecedent) with
          | None, None -> None
          | Some fml, None | None, Some fml -> Some fml
          | Some domain, Some feasible ->
              Some (Formula.and_of [ domain; feasible ]));
        kind = qfl_kind_of_sgcl_bound_kind kind;
        name = query_name;
        args = query_args;
        bound = value;
        strict =
          Option.value_map sgcl.bound ~default:false ~f:(fun bound ->
              bound.strict);
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
