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

(* [inline_consts pgcl] replaces every occurrence of a [const] in the
   statements and the query by its defining expression and leaves no
   constants: a constant is a name for a value, not a program variable.
   Before, the definitions were kept beside the program and never used, so a
   constant entered the reduction as one more parameter of every loop
   equation and as a universally quantified variable of the query -- [const p
   := 1/2] followed by [{..}[p]{..}] asked for the bound at every real [p],
   negative weights included, and lost the answer.  A definition may mention
   the constants declared before it, so the definitions are first closed
   under each other; there are no cycles, since a constant is only in scope
   after its declaration.  Assumes the constants are not assigned to (the
   grammar has no such check; an assignment to one keeps its name as a free
   variable). *)
let inline_consts (pgcl : Program.t) : Program.t =
  if List.is_empty pgcl.consts then pgcl
  else
    let defs =
      Map.Poly.of_alist_exn
      @@ List.map pgcl.consts ~f:(fun (var, _, term) -> (var, term))
    in
    let defs =
      Fn.apply_n_times ~n:(List.length pgcl.consts)
        (Map.Poly.map ~f:(Term.subst defs))
        defs
    in
    let query : Query.t =
      match pgcl.query with
      | Expectation expr -> Expectation (Term.subst defs expr)
      | Probability fml -> Probability (Formula.subst defs fml)
      | Bound bound ->
          Bound
            {
              bound with
              post = Term.subst defs bound.post;
              value = Term.subst defs bound.value;
            }
    in
    {
      pgcl with
      consts = [];
      stmts = Statement.subst defs pgcl.stmts;
      query;
    }

(* [asks_runtime query]: [query] is a bound on an expected runtime, the only
   query that gives the ticks a meaning *)
let asks_runtime : Query.t -> bool = function
  | Bound { transformer = Ert; _ } -> true
  | _ -> false

(* [elaborate ~print pgcl] gives every expression of the program its sort.

   A [nat] variable is a non-negative integer, an [int] or an [nparam] an
   integer of either sign and a [real] one a real; the grammar builds
   numerals and arithmetic operators without a sort, and they are resolved
   here, expression by expression, by these rules:
   - an operator takes the sort of its operands, so [%] between integers is
     the integer remainder (rounding toward zero, the mode the grammar
     attaches);
   - inside the program -- an assignment's value, a loop or branch guard, an
     observed condition -- [/] between two integer operands is integer
     division rounding toward zero, also when the quotient then meets a real
     ([y := x / 2 + 0.5] at [x = 1] gives 0.5); a quotient with a real
     operand is exact;
   - in an expectation, a bound, a choice weight or a probability [/] is
     exact rational division whatever its operands' sorts, since those are
     real-valued: [?Ex[x / 2]] at [x = 5] is 5/2, and the weight [x / 2] at
     [x = 1] is one half;
   - [a - b] is truncated subtraction (monus), [max(a - b, 0)], when both
     operands are [nat]-typed: built from [nat] variables and non-negative
     numerals by [+], [*], [^], [%], monus, and [/] where it is integer
     division, with at least one [nat] variable among them -- or with none,
     in the value assigned to a [nat] variable.  So a [nat] stays in its
     type.  A subtraction with an [nparam], a real or a mixed operand is
     ordinary, as is one between numerals elsewhere ([1 - 2] in a bound is
     -1), and so is every subtraction on [int] variables;
   - a numeral takes the sort its context requires, and is real where nothing
     requires an integer, which is what makes the weight [1/2] a half;
   - an expression whose operands mix the two (a [nat] variable times [0.5])
     is read over the reals: its [nat] variables are converted to reals first;
   - a context that needs a real converts an integer-valued expression to a
     real after evaluating it;
   - an assignment to a [nat] variable must have an integer value; one that
     does not (say [c := c * 0.5]) is refused rather than read over the
     reals, which would let the variable leave the integers;
   - a tick's cost is real-valued and read like an expectation, but only when
     the query is a bound on an expected runtime: elsewhere ticks mean
     nothing and are left as they were written, so that a program is never
     refused for a tick its query ignores.

   Encoding of monus, and its contract.  [a - b] becomes
   [ite(a >= b, a - b, 0)], which equals [max(a - b, 0)] for all integer
   values of [a] and [b].  An assignment whose value then contains such an
   [ite] is split into a conditional over the cases of [Term.elim_ite], whose
   conditions are disjoint and exhaustive, each branch assigning an
   [ite]-free value; so the weakest preexpectation applies a loop function to
   arithmetic arguments only, as it does for an [if] statement, and never to
   an [ite].  A guard or an observed condition that contains one has its
   [ite]s lifted into the formula ([Formula.elim_ite]).  In an expectation, a
   weight or a bound the [ite] stays a term, as an Iverson bracket does.  The
   [ite] is not built when [a >= b] is known at that point: [b] is the
   numeral 0, or [a] is a [nat] variable that an enclosing guard or
   observation, not invalidated by an assignment since, bounds below by at
   least [b] -- the loop body of [while (0 < x) { x := x - 1 }] is
   unchanged.  That knowledge is a set of atoms implied at the program point
   (a sound under-approximation: a guard's atoms enter its branches, an
   assignment removes every atom mentioning its target, and a loop body
   keeps only the atoms over variables the body does not assign).

   Before the sorts were kept every variable and numeral was read as a real,
   which changed the program wherever the two readings differ: [x := x / 2]
   never reached 0, and a guard [0 < x & x < 1] held at states no [nat]
   program reaches.  Expects the constants inlined (it reads the
   declarations only). *)
let elaborate ~print (pgcl : Program.t) : Program.t =
  let senv = Map.Poly.of_alist_exn @@ Program.sort_env_list_of_decls pgcl in
  let attempt f =
    try Some (f ()) with exn_ when not (Common.Timer.is_async exn_) -> None
  in
  (* the integer variables, each mapped to itself converted to a real: the
     declared ones, and the fresh ones that stand for integer quotients (see
     [integer_divs]) *)
  let int_quotients = ref Map.Poly.empty in
  let declared_ints =
    Map.Poly.filter_mapi senv ~f:(fun ~key ~data ->
        if Term.is_int_sort data then
          Some (T_irb.mk_int_to_real (Term.mk_var key data))
        else None)
  in
  let to_reals () =
    Map.merge_skewed declared_ints !int_quotients ~combine:(fun ~key:_ v _ -> v)
  in
  let infer_term ?sort_opt ~default t =
    attempt (fun () -> Typeinf.typeinf_term ~print ~default ~senv ~sort_opt t)
  in
  let real_term ~what t =
    match infer_term ~default:(Some T_real.SReal) t with
    | Some t' when Term.is_int_sort (Term.sort_of t') -> T_irb.mk_int_to_real t'
    | Some t' -> t'
    | None -> (
        match
          infer_term ~sort_opt:T_real.SReal ~default:(Some T_real.SReal)
            (Term.subst (to_reals ()) t)
        with
        | Some t' -> t'
        | None ->
            Common.Refusal.refuse "%s %s is not a number" what (Term.str_of t))
  in
  let formula ~what phi =
    let infer phi =
      attempt (fun () ->
          Typeinf.typeinf_formula ~print ~default:(Some T_real.SReal) ~senv phi)
    in
    match infer phi with
    | Some phi' -> phi'
    | None -> (
        match infer (Formula.subst (to_reals ()) phi) with
        | Some phi' -> phi'
        | None ->
            Common.Refusal.refuse "%s %s is not a condition" what
              (Formula.str_of phi))
  in
  let assigned x t =
    match Map.Poly.find senv x with
    | Some sort when Term.is_int_sort sort -> (
        match infer_term ~sort_opt:T_int.SInt ~default:(Some T_int.SInt) t with
        | Some t' -> t'
        | None ->
            Common.Refusal.refuse
              "the value %s assigned to the nat variable %s is not an integer"
              (Term.str_of t) (Ident.name_of_tvar x))
    | Some sort when Term.is_real_sort sort ->
        real_term ~what:"the value assigned to" t
    | Some sort -> (
        match infer_term ~sort_opt:sort ~default:(Some T_real.SReal) t with
        | Some t' -> t'
        | None ->
            Common.Refusal.refuse
              "the value %s assigned to %s has the wrong sort" (Term.str_of t)
              (Ident.name_of_tvar x))
    | None ->
        Common.Refusal.refuse "%s is assigned to but not declared"
          (Ident.name_of_tvar x)
  in
  (* --- monus --- *)
  let is_nat_var x = List.mem pgcl.nat_vars x ~equal:Ident.tvar_equal in
  let nat_numeral = function
    | Term.FunApp (T_num.Value (s, _), [], _) -> (
        match Z.of_string s with
        | n -> if Z.(geq n zero) then Some n else None
        | exception exn_ when not (Common.Timer.is_async exn_) -> None)
    | FunApp (T_int.Int n, [], _) when Z.(geq n zero) -> Some n
    | _ -> None
  in
  (* [nat_kind ~int_div t] is [`Nat] if [t] is [nat]-typed and mentions a
     [nat] variable, [`Lit] if it is [nat]-typed and built from numerals only,
     and [`No] otherwise; [int_div] says whether [/] is integer division
     here.  A subtraction counts only once rewritten to monus (an [ite] with
     the branch 0): an ordinary one may be negative. *)
  let rec nat_kind ~int_div t =
    let join k1 k2 =
      match (k1, k2) with
      | `No, _ | _, `No -> `No
      | `Nat, _ | _, `Nat -> `Nat
      | `Lit, `Lit -> `Lit
    in
    match t with
    | Term.Var (x, _, _) -> if is_nat_var x then `Nat else `No
    | FunApp (T_num.(NAdd _ | NMul _ | NPower _ | NRem _), [ a; b ], _)
    | FunApp (T_int.(Add | Mul | Power | Rem _), [ a; b ], _) ->
        join (nat_kind ~int_div a) (nat_kind ~int_div b)
    | FunApp (T_num.NDiv _, [ a; b ], _) when int_div ->
        join (nat_kind ~int_div a) (nat_kind ~int_div b)
    | FunApp
        (T_bool.IfThenElse, [ _; FunApp (T_num.NSub _, [ a; b ], _); zero ], _)
      when Option.equal Z.equal (nat_numeral zero) (Some Z.zero) ->
        join (nat_kind ~int_div a) (nat_kind ~int_div b)
    | t -> if Option.is_some (nat_numeral t) then `Lit else `No
  in
  (* the greatest lower bound on [x] that one of [facts] states, if any *)
  let lower_bound facts x =
    List.filter_map facts ~f:(function
      | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) -> (
          let is_x = function
            | Term.Var (y, _, _) -> Ident.tvar_equal x y
            | _ -> false
          in
          let int_of = function
            | Term.FunApp (T_int.Int m, [], _) -> Some m
            | _ -> None
          in
          match (psym, int_of t1, int_of t2) with
          | (T_int.Geq | T_bool.Eq), None, Some m when is_x t1 -> Some m
          | T_int.Gt, None, Some m when is_x t1 -> Some Z.(m + one)
          | (T_int.Leq | T_bool.Eq), Some m, None when is_x t2 -> Some m
          | T_int.Lt, Some m, None when is_x t2 -> Some Z.(m + one)
          | _ -> None)
      | _ -> None)
    |> List.max_elt ~compare:Z.compare
  in
  let known_geq ~facts a b =
    match (nat_numeral b, a) with
    | Some k, _ when Z.(equal k zero) -> true
    | Some k, Term.Var (x, _, _) -> (
        match lower_bound facts x with Some m -> Z.geq m k | None -> false)
    | _ -> false
  in
  (* rewrites a subtraction between [nat]-typed operands, whose operands have
     already been rewritten, and counts the [ite]s it builds in [built] *)
  let monus_node ~built ~int_div ~nat_ctx ~facts = function
    | Term.FunApp (T_num.NSub _, [ a; b ], _) as t -> (
        match (nat_kind ~int_div a, nat_kind ~int_div b) with
        | ((`Nat | `Lit) as ka), ((`Nat | `Lit) as kb)
          when nat_ctx || Stdlib.(ka = `Nat || kb = `Nat) ->
            if known_geq ~facts a b then t
            else (
              incr built;
              T_bool.mk_if_then_else
                (T_bool.of_atom (T_num.mk_ngeq a b))
                t (T_num.mk_value "0"))
        | _ -> t)
    | t -> t
  in
  let monus ~built ~int_div ~nat_ctx ~facts t =
    Term.map_term true t ~f:(monus_node ~built ~int_div ~nat_ctx ~facts)
  in
  (* --- exact division --- *)
  (* [abstract_divs ~facts map x] replaces each [/] of [x], innermost first,
     by the exact quotient of its operands read as reals, and returns the
     definitions it made, outermost first.  The rest of [x] is then typed with
     the quotients as opaque reals, so a [/] is never resolved to integer
     division by its operands' sorts or by its context's ([x + 1/2] with [x]
     a [nat] unified [1/2] with [x] and made it 0).  A quotient that mentions
     an integer variable stands as a fresh real variable until [restore]:
     typed in place it would meet the fallback that converts a mixed
     expression's integer variables to reals, which would convert [x] inside
     [int_to_real x] a second time. *)
  let abstract_divs ~facts map x =
    let defs = ref [] in
    let x =
      map x ~f:(function
        | Term.FunApp (T_num.NDiv _, [ a; b ], _) ->
            let operand t =
              real_term ~what:"the operand of a division"
                (monus ~built:(ref 0) ~int_div:false ~nat_ctx:false ~facts t)
            in
            let quotient = T_real.mk_rdiv (operand a) (operand b) in
            if
              Set.for_all
                (Set.union (Term.fvs_of a) (Term.fvs_of b))
                ~f:(Fn.non (Map.Poly.mem (to_reals ())))
            then
              (* no integer variable for the fallback's conversion to reach:
                 the typed quotient can stand in the term as it is *)
              quotient
            else
              let d = Ident.mk_fresh_tvar () in
              defs := (d, quotient) :: !defs;
              Term.mk_var d T_real.SReal
        | t -> t)
    in
    (x, !defs)
  in
  let restore subst defs x =
    List.fold defs ~init:x ~f:(fun x (d, def) ->
        subst (Map.Poly.singleton d def) x)
  in
  let exact_term ~what ~facts t =
    let t, defs =
      abstract_divs ~facts (fun t ~f -> Term.map_term true ~f t) t
    in
    let t = monus ~built:(ref 0) ~int_div:false ~nat_ctx:false ~facts t in
    restore Term.subst defs (real_term ~what t)
  in
  let exact_formula ~what ~facts phi =
    let phi, defs =
      abstract_divs ~facts (fun phi ~f -> Formula.map_term ~f phi) phi
    in
    let built = ref 0 in
    let phi =
      Formula.map_term phi
        ~f:(monus_node ~built ~int_div:false ~nat_ctx:false ~facts)
    in
    let phi = restore Formula.subst defs (formula ~what phi) in
    if !built > 0 then Formula.elim_ite phi else phi
  in
  (* --- integer division in the program --- *)
  (* [integer_divs map x] replaces each [/] of [x], innermost first, whose
     operands both type as integers and mention an integer variable, by a
     fresh integer variable standing for their truncated quotient, and returns
     the definitions it made, outermost first, for [restore].  Typed in place,
     the quotient would be lost to the fallback that reads a mixed expression
     over the reals: [y := x / 2 + 0.5] with [x] an integer converts [x] to a
     real and made the quotient exact.  The fresh variable is converted by
     that fallback like a declared integer ([to_reals]), so the quotient is
     computed on integers and only its value is converted.  A [/] between
     numerals, or with a real operand, is left to its context's sort, as
     before. *)
  let integer_divs map x =
    let defs = ref [] in
    let x =
      map x ~f:(function
        | Term.FunApp (T_num.NDiv _, [ a; b ], _) as t -> (
            let ints = to_reals () in
            let int_operand t =
              infer_term ~sort_opt:T_int.SInt ~default:(Some T_int.SInt) t
            in
            if
              not
                (Set.exists
                   (Set.union (Term.fvs_of a) (Term.fvs_of b))
                   ~f:(Map.Poly.mem ints))
            then t
            else
              match (int_operand a, int_operand b) with
              | Some a', Some b' ->
                  let d = Ident.mk_fresh_tvar () in
                  let v = Term.mk_var d T_int.SInt in
                  int_quotients :=
                    Map.Poly.set !int_quotients ~key:d
                      ~data:(T_irb.mk_int_to_real v);
                  defs := (d, T_int.mk_div Value.Truncated a' b') :: !defs;
                  v
              | _ -> t)
        | t -> t)
    in
    (x, !defs)
  in
  (* a guard or an observed condition: [/] between integers is integer
     division, as in an assignment, and a monus [ite] is lifted into the
     formula *)
  let program_formula ~what ~facts phi =
    let built = ref 0 in
    let phi =
      Formula.map_term phi
        ~f:(monus_node ~built ~int_div:true ~nat_ctx:false ~facts)
    in
    let phi, defs = integer_divs (fun phi ~f -> Formula.map_term ~f phi) phi in
    let phi = restore Formula.subst defs (formula ~what phi) in
    if !built > 0 then Formula.elim_ite phi else phi
  in
  let assign ~facts x t : Statement.t =
    let built = ref 0 in
    let t = monus ~built ~int_div:true ~nat_ctx:(is_nat_var x) ~facts t in
    let t =
      let t, defs = integer_divs (fun t ~f -> Term.map_term true ~f t) t in
      restore Term.subst defs (assigned x t)
    in
    if !built = 0 then ASSIGN (x, t)
    else
      match List.rev (Term.elim_ite t) with
      | [] -> ASSIGN (x, t)
      | (_, t_last) :: cases ->
          List.fold cases ~init:(Statement.ASSIGN (x, t_last))
            ~f:(fun rest (cond, t) ->
              Statement.IF (Evaluator.simplify cond, ASSIGN (x, t), rest))
  in
  (* --- statements, with the atoms known to hold at each point --- *)
  let rec assigned_vars : Statement.t -> Ident.tvar Set.Poly.t = function
    | ASSIGN (x, _) -> Set.Poly.singleton x
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
        let c = program_formula ~what:"the guard" ~facts c in
        let s1, _ = stmt (facts @ atoms_of c) s1 in
        let s2, _ = stmt (facts @ atoms_of (Formula.negate c)) s2 in
        (IF (c, s1, s2), kill (assigned_vars s) facts)
    | WHILE (c, body) ->
        let outer = kill (assigned_vars body) facts in
        let c = program_formula ~what:"the loop guard" ~facts:outer c in
        let body, _ = stmt (outer @ atoms_of c) body in
        (WHILE (c, body), outer @ atoms_of (Formula.negate c))
    | LOOP (n, body) ->
        let outer = kill (assigned_vars body) facts in
        (LOOP (n, fst (stmt outer body)), outer)
    | ASSIGN (x, t) -> (assign ~facts x t, kill (Set.Poly.singleton x) facts)
    | COMPOUND (s1, s2) ->
        let s1, facts = stmt facts s1 in
        let s2, facts = stmt facts s2 in
        (COMPOUND (s1, s2), facts)
    | CHOICE (p, s1, s2) as s ->
        let p = exact_term ~what:"the choice weight" ~facts p in
        let s1, _ = stmt facts s1 in
        let s2, _ = stmt facts s2 in
        (CHOICE (p, s1, s2), kill (assigned_vars s) facts)
    | TICK t when asks_runtime pgcl.query ->
        (TICK (exact_term ~what:"the cost of a tick" ~facts t), facts)
    | TICK t -> (TICK t, facts)
    | OBSERVE c ->
        let c = program_formula ~what:"the observed condition" ~facts c in
        (OBSERVE c, facts @ atoms_of c)
    | SKIP -> (SKIP, facts)
  in
  let query : Query.t =
    let exact_term = exact_term ~facts:[] in
    match pgcl.query with
    | Expectation e -> Expectation (exact_term ~what:"the expectation of" e)
    | Probability c -> Probability (exact_formula ~what:"the event" ~facts:[] c)
    | Bound b ->
        Bound
          {
            b with
            post = exact_term ~what:"the expectation of" b.post;
            value = exact_term ~what:"the bound" b.value;
          }
  in
  { pgcl with stmts = fst (stmt [] pgcl.stmts); query }

(* [validate pgcl] refuses, through [Common.Refusal], a program the reduction
   would give a meaning other than its own; it returns [()] otherwise.

   A choice weight that is a closed expression must lie in [0, 1]: the rule
   [p * wp(S1, f) + (1 - p) * wp(S2, f)] is an expectation transformer only
   there, and outside it a branch is weighted negatively.  A weight that
   mentions a program variable is not checked here: a run that reaches it
   outside [0, 1] is an error, resolved against the bound by [Program.wpt]
   and [problem_of_bound].  What a bound on a program with
   [observe] requires is checked by [reduce_conditional].

   For a bound on an expected runtime every tick's cost must be seen to be
   non-negative ([nonnegative_cost]): the runtime calculus adds the cost to
   the expectation after the tick, and a negative one could take the value
   out of QFL's [0, oo], where its least fixpoints live (a loop paying -1
   per iteration has no least solution there).  The check is syntactic, so
   a cost that is non-negative only on the reachable states, [tick(x)] for
   an [int] variable that the program keeps positive, is refused too.

   Expects constants already inlined, so that a weight given by a constant is
   seen as closed, and a program [elaborate]d, so that a counted tick's cost
   is a typed real term. *)
(* [nonnegative_cost pgcl r]: every value of [r] is non-negative, seen
   syntactically -- [r] is built from non-negative numerals and [nat]
   variables by addition, multiplication, conversion to a real, division by
   a positive numeral and if-then-else (which is how monus is written).  A
   sufficient check, not a decision. *)
let rec nonnegative_cost (pgcl : Program.t) r =
  let nonneg = nonnegative_cost pgcl in
  let constant t =
    if Set.is_empty (Term.fvs_of t) then
      match Evaluator.simplify_term t with
      | Term.FunApp (T_real.Real q, [], _) -> Some q
      | FunApp (T_int.Int n, [], _) -> Some (Q.of_bigint n)
      | _ -> None
    else None
  in
  match r with
  | Term.Var (x, _, _) -> List.mem pgcl.nat_vars x ~equal:Ident.tvar_equal
  | FunApp (T_irb.IntToReal, [ a ], _) -> nonneg a
  | FunApp
      ( ( T_int.(Add | Mul)
        | T_real.(RAdd | RMul)
        | T_num.(NAdd _ | NMul _) ),
        [ a; b ],
        _ ) ->
      nonneg a && nonneg b
  | FunApp ((T_real.RDiv | T_num.NDiv _), [ a; b ], _) -> (
      nonneg a
      && match constant b with Some q -> Q.(gt q zero) | None -> false)
  | FunApp (T_bool.IfThenElse, [ _; a; b ], _) -> nonneg a && nonneg b
  | t -> (
      match constant t with Some q -> Q.(geq q zero) | None -> false)

let validate ~print (pgcl : Program.t) =
  let check_weight p =
    if Set.is_empty (Term.fvs_of p) then
      match
        Evaluator.simplify_term
        @@ Typeinf.typeinf_term ~print ~default:(Some T_real.SReal)
             ~senv:(Map.Poly.of_alist_exn @@ Program.sort_env_list_of_decls pgcl)
             p
      with
      | t when T_real.is_real t ->
          let q = T_real.let_real t in
          if Q.(lt q zero || gt q one) then
            Common.Refusal.refuse
              "the weight %s of a probabilistic choice is outside [0, 1]"
              (Q.to_string q)
      | _ -> ()
  in
  let check_cost r =
    if asks_runtime pgcl.query && not (nonnegative_cost pgcl r) then
      Common.Refusal.refuse
        "the cost %s of a tick could not be seen to be non-negative, which an \
         expected-runtime bound requires (write it from non-negative numerals \
         and nat variables with +, * and division by a positive numeral)"
        (Term.str_of r)
  in
  let rec walk = function
    | Statement.CHOICE (p, s1, s2) ->
        check_weight p;
        walk s1;
        walk s2
    | Statement.TICK r -> check_cost r
    | stmt -> List.iter (Statement.get_inner_statements stmt) ~f:walk
  in
  walk pgcl.stmts

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
    let pgcl = elaborate ~print @@ inline_consts pgcl in
    validate ~print pgcl;
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
    (* an expression read alone has no declarations, so its variables and
       numerals take the sort a numeral takes where nothing requires an
       integer, real (see [elaborate]) *)
    let expr =
      Parser.expr Lexer.main lexbuf
      |> Typeinf.typeinf_term ~print ~default:(Some T_real.SReal)
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

let rec first_decl_var (pgcl : Program.t) =
  match pgcl.vars with
  | [] -> failwith "No declared variables in the pGCL program."
  | (var, T_real.SReal) :: _ -> Term.mk_var var T_real.SReal
  | _ :: rest -> first_decl_var { pgcl with vars = rest }

let wpt_of ~print ?ert ?f ?fail ?err (pgcl : Program.t) =
  let result =
    Program.wpt ~print:(fun _ -> ()) ?ert ?f ?fail ?err pgcl
    |> typeinf_eqs ~print pgcl
  in
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
  Formula.geq (Term.mk_var var sort)
    (if Term.is_int_sort sort then T_int.zero () else T_real.rzero ())

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

let rec has_observe stmt =
  Statement.is_observe stmt
  || List.exists (Statement.get_inner_statements stmt) ~f:has_observe

(* [has_loop stmt]: [stmt] contains a [while], the only statement whose
   weakest preexpectation is a fixpoint.  A bounded [loop(n) { S }] is [n]
   copies of [S] (see [Program.wpt]), so it counts only through a [while]
   inside [S]. *)
let rec has_loop stmt =
  Statement.is_while stmt
  || List.exists (Statement.get_inner_statements stmt) ~f:has_loop

(* [has_state_weight stmt]: [stmt] contains a choice whose weight mentions a
   variable, the only kind [Program.wpt] guards with an error value (a closed
   weight is checked to be a probability before the reduction). *)
let rec has_state_weight stmt =
  (match stmt with
  | Statement.CHOICE (p, _, _) -> not (Set.is_empty (Term.fvs_of p))
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

(* [feasibility ~print ~strict pgcl] is the condition, over the initial state,
   under which the normaliser [wlp(S, 1)] -- the probability that a run is not
   blocked by an observation -- is positive, as [None] when it holds
   everywhere the reduction can see; it refuses an infeasible program.  The
   reduction [num ⋈ q * den] is sound only where [den > 0]: where every run is
   blocked, [num = 0] and the reduced query [0 + q * 1 ⋈ q] holds vacuously
   (non-strict) or fails (strict), and neither is an answer about a
   conditional expectation, which is undefined there.  A loop-free program's
   blocking probability [wp(S, 0)] with a failed observation worth 1 is an
   expression, so [den = 1 - wp(S, 0)] is too: a closed one that is 0 makes
   the program infeasible, and one over the inputs becomes the query's
   antecedent [den > 0], which is said on stderr.  With a loop [den] is a
   fixpoint, which the antecedent cannot state soundly (the checker
   approximates a recursive function in the antecedent the wrong way round),
   so a strict bound is refused and a non-strict one is reduced with the note
   that its verdict speaks of the feasible initial states only. *)
let feasibility ~print ~strict (pgcl : Program.t) =
  if has_loop pgcl.stmts then (
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
      (wpt_of ~print ~f:(T_real.rzero ()) ~fail:(T_real.rone ()) pgcl).qf
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

(* [reduce_conditional ~print pgcl bound] reduces a bound on the conditional
   expectation [bound.transformer] names to a bound on one least fixpoint:
   it returns [(post, fail, kind, value, antecedent)] such that, at every
   initial state satisfying [antecedent], the bound holds iff
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
     fixpoint expresses ([N + q * (1 - D)] adds [q] times the divergence
     probability, a greatest fixpoint), and the query is refused.
   Without [observe], [cwp] is [wp(S, f)] and the bound is returned exactly as
   it was given, so such a program reduces as it always has.  A bound on an
   expected runtime ([Ert]) is returned as it was given too, and is refused
   on a program with [observe], for which the runtime calculus has no rule.  The bound must
   be a constant when it enters the program as [fail] (it is the value at
   the initial state, while the program changes the variables), and
   nonnegative, since an expectation is. *)
let reduce_conditional ~print (pgcl : Program.t) (bound : Query.bound) =
  let observes = has_observe pgcl.stmts in
  let constant_bound ~lo ~hi ~what =
    match real_value_of (typeinf_term ~print pgcl bound.value) with
    | Some q when Q.(geq q lo) && Option.for_all hi ~f:(fun hi -> Q.(leq q hi)) -> q
    | _ ->
        Common.Refusal.refuse
          "the bound %s of a %s query must be a constant in %s here"
          (Term.str_of bound.value) what
          (match hi with
          | None -> sprintf "[%s, oo)" (Q.to_string lo)
          | Some hi -> sprintf "[%s, %s]" (Q.to_string lo) (Q.to_string hi))
  in
  let transformer : Query.transformer =
    match bound.transformer with
    | R2 when has_loop pgcl.stmts ->
        Common.Refusal.refuse
          "an r2 bound on a program with a loop is not reduced: wp(S, f) / \
           wp(S, 1) compares a least fixpoint with a multiple of another, \
           which one certificate of one direction does not bound"
    | R2 -> Cwp
    | t -> t
  in
  let antecedent () = feasibility ~print ~strict:bound.strict pgcl in
  match transformer with
  | Ert when observes ->
      Common.Refusal.refuse
        "an expected-runtime bound on a program with observe is not reduced: \
         the expected-runtime calculus has no rule for conditioning"
  | Ert -> (bound.post, None, bound.kind, bound.value, None)
  | Cwp when not observes -> (bound.post, None, bound.kind, bound.value, None)
  | Cwp ->
      let q = constant_bound ~lo:Q.zero ~hi:None ~what:"cwp" in
      let antecedent = antecedent () in
      (bound.post, Some (T_real.mk_real q), bound.kind, bound.value, antecedent)
  | Cwlp ->
      let g = Evaluator.simplify_term @@ typeinf_term ~print pgcl bound.post in
      if not (bounded_by_one g) then
        Common.Refusal.refuse
          "the post-expectation %s of a cwlp query must be bounded by 1, and \
           could not be seen to be (write it as a constant or an indicator \
           [b])"
          (Term.str_of bound.post);
      let q = constant_bound ~lo:Q.zero ~hi:(Some Q.one) ~what:"cwlp" in
      let antecedent = if observes then antecedent () else None in
      let one_minus t = T_real.mk_rsub (T_real.rone ()) t in
      ( one_minus bound.post,
        Some (T_real.mk_real Q.(one - q)),
        (match bound.kind with Upper -> Lower | Lower -> Upper),
        T_real.mk_real Q.(one - q),
        antecedent )
  | R2 -> assert false (* turned into [Cwp] above *)

(* [error_value ~transformer kind] is what a run that reaches a choice weight
   outside [0, 1] is worth in the query [reduce_conditional] returns for a
   bound of [kind] on [transformer].  Such a run is an error from which no
   bound may be proved: it is worth 0 against a lower bound and +oo against an
   upper one, the value that makes the claim hardest.  A [cwp] bound (and an
   [r2] one, reduced as [cwp]) keeps its direction and so its value.  A [cwlp]
   bound is mirrored: the reduced post-expectation is [1 - g], and a run worth
   [v] in [wlp(S, g)] is worth [1 - v] in the reduced [wp], so 0 becomes 1
   (finite, so it is passed to [Program.wpt] as it is) and +oo becomes -oo
   against the reduced lower bound.  An [ert] bound keeps its direction, but
   0 is not the hardest value against its lower bound: the ticks paid before
   the error would still be counted ([r + 0]), so the error is worth -oo
   there, the value a whole run must be worth for nothing to be proved. *)
let error_value ~(transformer : Query.transformer) (kind : Query.bound_kind) =
  match (transformer, kind) with
  | Cwlp, Lower -> `Finite (T_real.rone ())
  | Cwlp, Upper -> `Minus_infinity
  | (Cwp | R2), Lower -> `Finite (T_real.rzero ())
  | Ert, Lower -> `Minus_infinity
  | (Cwp | R2 | Ert), Upper -> `Plus_infinity

(* [against_infinite_error ~print pgcl ~above ~value qf]: the pair
   [(qf', value')] of a preexpectation and a bound (typed) such that
   [qf' ⋈ value'] holds exactly where [qf ⋈ value] holds and no run reaching
   an out-of-range weight has positive probability.  [qf] is computed with
   such a run worth 0; the run is worth +oo against an upper bound ([above])
   or -oo against a lower one, so [wp] is that infinity wherever
   [P(error) > 0] and [qf] elsewhere.  No term is infinite, and every term of
   a QFL input must lie in [0, oo] (the checker refuses one negative at every
   state of its guard), so:
   - above: [qf' = ite(P(error) > 0, value + 1, qf)], [value' = value];
     [value + 1 > value] fails [<=] and [<], and [value + 1 >= 0].
   - below: [qf' = ite(P(error) > 0, 0, qf + 1)], [value' = value + 1].
     Where [P(error) = 0] this is [qf + 1 ⋈ value + 1], i.e. [qf ⋈ value].
     Where [P(error) > 0] it is [0 ⋈ value + 1], false for [>=] and [>]
     because [value >= 0] (an expectation bound is nonnegative).  The shift
     is needed: the error arm must lie strictly below the bound, and against
     a non-strict lower bound 0 (a cwlp upper bound 1 becomes one) no value
     in [0, oo] does; [value - 1], used before, is negative there.
   Requires a program without [while]: [P(error)] is
   then an expression over the initial state ([wp] with [f = 0], a blocked run
   worth 0 and an error worth 1).  With a loop it is a least fixpoint, and "it
   is positive" is a bound on it in the direction the query's one certificate
   does not give; nor can a finite pre-fixpoint be infinite at an error state,
   so the query is refused rather than answered with an error worth 0, under
   which an upper bound would hold at the error states. *)
let against_infinite_error ~print (pgcl : Program.t) ~above ~value qf =
  let value = typeinf_term ~print pgcl value in
  if not (has_state_weight pgcl.stmts) then (qf, value)
  else if has_loop pgcl.stmts then
    Common.Refusal.refuse
      "this bound on a program with a loop and a choice weight over program \
       variables is not reduced: a run reaching a weight outside [0, 1] is \
       worth +oo against an upper bound (-oo against a lower bound on an \
       expected runtime, or the lower bound a cwlp upper bound becomes), \
       which a certificate of one direction cannot express"
  else
    let p_err =
      Evaluator.simplify_term
        (wpt_of ~print ~f:(T_real.rzero ()) ~fail:(T_real.rzero ())
           ~err:(T_real.rone ()) pgcl)
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

let problem_of_bound ~print (pgcl : Program.t) (bound : Query.bound) =
  let open QFL in
  let post, fail, kind, value, antecedent = reduce_conditional ~print pgcl bound in
  (* With a loop the post-expectation is a function of its own, applied in
     each loop's exit branch.  The checker requires every function to be
     non-negative at every state of its domain, reachable or not, so a post
     over an [int] or [real] variable ([r] in [r := 1; ?Ex[r] <= 1]) failed
     that requirement at the states where it is negative and the bound was
     lost although the program never reaches them.  A loop-free program needs
     no such function: the post is substituted into the preexpectation, which
     is then a function of the initial state only (here the constant 1). *)
  let error = error_value ~transformer:bound.transformer bound.kind in
  let err = match error with `Finite v -> Some v | _ -> None in
  (* only the bound's own preexpectation counts the ticks: the error and
     blocking probabilities computed beside it are [wp]'s *)
  let ert = Stdlib.(bound.transformer = Ert) in
  let post_pred, wpt =
    if has_loop pgcl.stmts then
      let post_pred, post_app = post_predicate_of_query pgcl post in
      (Some post_pred, wpt_of ~print ~ert ~f:post_app ?fail ?err pgcl)
    else (None, wpt_of ~print ~ert ~f:post ?fail ?err pgcl)
  in
  let wpt, value =
    let shifted ~above =
      let qf, value = against_infinite_error ~print pgcl ~above ~value wpt.qf in
      ({ wpt with qf }, value)
    in
    match error with
    | `Finite _ -> (wpt, value)
    | `Plus_infinity -> shifted ~above:true
    | `Minus_infinity -> shifted ~above:false
  in
  (* The query form asks about ONE function applied to arguments, and the
     preexpectation need not have that shape: a choice or a conditional
     before the first loop gives a weighted sum or an [ite] of applications.
     Such an expression is given a function of its own, defined to be it; the
     definition is not recursive, so its least fixpoint is the expression, and
     its parameters are the program variables it mentions.  This used to
     raise "missing predicate for query". *)
  let entry_pred, name', args' =
    match wpt.qf with
    | FunApp (FVar (fvar, _, _), args, _) -> (None, fvar, args)
    | qf ->
        let name = Ident.mk_fresh_tvar () in
        let params =
          let fvs = Term.fvs_of qf in
          List.filter (Program.sort_env_list_of_decls pgcl) ~f:(fun (x, _) ->
              Set.mem fvs x)
        in
        ( Some (QFL.Pred.make Predicate.Mu name params qf),
          name,
          List.map params ~f:(fun (x, s) -> Term.mk_var x s) )
  in
  let query =
    (* the antecedent's variables are quantified with the rest; it has none
       unless the program has [observe] *)
    let query_params =
      used_query_vars (Program.sort_env_list_of_decls pgcl)
        (Option.value_map antecedent ~default:args' ~f:(fun fml ->
             T_bool.of_formula fml :: args'))
        value
    in
    Problem.Check
      {
        params = query_params;
        left =
          (match (nonnegative_query_domain pgcl query_params, antecedent) with
          | None, None -> None
          | Some fml, None | None, Some fml -> Some fml
          | Some domain, Some feasible -> Some (Formula.and_of [ domain; feasible ]));
        kind = qfl_kind_of_pgcl_bound_kind kind;
        name = name';
        args = args';
        bound = typeinf_term ~print pgcl value;
        strict = bound.strict;
      }
  in
  Problem.
    {
      preds =
        List.map
          (Option.to_list entry_pred @ Option.to_list post_pred
          @ PredSet.to_list wpt.equations)
          ~f:(add_nat_arg_constrs pgcl);
      query;
    }

let problem_of ~print (pgcl : Program.t) =
  match Query.bound_of pgcl.query with
  | Some bound -> Some (problem_of_bound ~print pgcl bound)
  | None ->
      let (_ : EquationSystem.t) = wpt_of ~print pgcl in
      None

(* [printable_problem_of ~print pgcl] is the QFL problem of [problem_of] when
   the program asks for a bound, and [None] beside it.  A program that asks for
   an expected value or a probability, which no bound query states, is given
   the bound [>= 0] on that expectation: every function of the problem is the
   one [problem_of] would build for a bound on it, and the query holds of
   every QFL problem, whose values are non-negative, so it carries no claim.
   The string says so, for the printed file's header. *)
let printable_problem_of ~print (pgcl : Program.t) =
  match Query.bound_of pgcl.query with
  | Some bound -> (problem_of_bound ~print pgcl bound, None)
  | None ->
      let bound : Query.bound =
        {
          post = Query.of_term pgcl.query;
          kind = Lower;
          value = T_real.rzero ();
          strict = false;
          transformer = Cwp;
        }
      in
      ( problem_of_bound ~print pgcl bound,
        Some
          (sprintf
             "The program asks for %s and states no bound: the query below, a \n\
              lower bound 0, holds of every QFL problem and makes the file \n\
              readable, nothing more."
             (Query.describe pgcl.query)) )
