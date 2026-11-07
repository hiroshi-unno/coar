(* Abstract syntax of pGCL, the probabilistic guarded command language, and
   its reduction to QFL.  A program has declared variables and constants,
   statements (assignment, conditional, loop, probabilistic choice weighted
   by an expression, observation, cost ticks) and a query: an expected
   value, a probability, or a bound on an expected value or on an expected
   runtime.  [Program.wpt] is the weakest-preexpectation transformer: it
   returns the query's preexpectation as a real-valued term together with
   one least-fixpoint equation per loop, the input of the QFL solver.  An
   observation that fails contributes a given value, 0 unless [Util]'s
   reduction of a conditional expectation asks for another; cost ticks are
   ignored by [wp] and counted by the expected-runtime transformer [ert]
   ([Program.wpt ~ert:true]); and the bounded [LOOP] statement
   [loop(n) { S }] is unrolled into [n] copies of [S]. *)
open Core
open Common.Ext
open Ast.LogicOld
open Ast
open QFL

module PredSet = struct
  module PredOrd = struct
    type t = Pred.t

    let compare p1 p2 = String.compare (Pred.str_of p1) (Pred.str_of p2)
  end

  module S = Stdlib.Set.Make (PredOrd)
  include S
end

module rec EquationSystem : sig
  type t = { qf : Term.t; equations : PredSet.t }

  val typeinf : print:(string lazy_t -> unit) -> Program.t -> t -> t
  val str_of : t -> string
  val simplify : t -> t
  val normalize : t -> t
end = struct
  type t = { qf : Term.t; equations : PredSet.t }

  let typeinf ~print pgcl eqs =
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
                    (Map.Poly.of_alist_exn
                    @@ Program.sort_env_list_of_decls pgcl)
                  pred.body;
            })
          eqs.equations;
    }

  let str_of (eqs : t) =
    sprintf "QF: %s\nEquations:\n%s" (Term.str_of eqs.qf)
      (String.concat ~sep:"\n"
         (List.map ~f:Pred.str_of (PredSet.elements eqs.equations)))

  let simplify (eqs : t) : t =
    {
      qf = Evaluator.simplify_term eqs.qf;
      equations = PredSet.map Pred.simplify eqs.equations;
    }

  let normalize (eqs : t) : t =
    {
      qf = Normalizer.normalize_term eqs.qf;
      equations = PredSet.map Pred.normalize eqs.equations;
    }
end

and Statement : sig
  type t =
    | IF of Formula.t * t * t
    | WHILE of Formula.t * t
    | LOOP of Term.t * t
    | ASSIGN of Ident.tvar * Term.t
    | COMPOUND of t * t
    | CHOICE of Term.t * t * t
    | TICK of Term.t
    | OBSERVE of Formula.t
    | SKIP

  val is_if : t -> bool
  val is_while : t -> bool
  val is_loop : t -> bool
  val is_assign : t -> bool
  val is_compound : t -> bool
  val is_choice : t -> bool
  val is_tick : t -> bool
  val is_observe : t -> bool
  val is_skip : t -> bool
  val mk_if : Formula.t -> t -> t -> t
  val mk_while : Formula.t -> t -> t
  val mk_loop : Term.t -> t -> t
  val mk_assign : Ident.tvar -> Term.t -> t
  val mk_compound : t -> t -> t
  val mk_choice : Term.t -> t -> t -> t
  val mk_tick : Term.t -> t
  val mk_observe : Formula.t -> t
  val mk_skip : unit -> t
  val let_if : t -> Formula.t * t * t
  val let_loop : t -> Term.t * t
  val let_assign : t -> Ident.tvar * Term.t
  val let_compound : t -> t * t
  val string_of : ?indent:int -> t -> string
  val subst : TermSubst.t -> t -> t
  val get_inner_statements : t -> t list
  val get_read_vars : t -> Variables.t
  val of_statements : t list -> t
end = struct
  type t =
    | IF of Formula.t * t * t
    | WHILE of Formula.t * t
    | LOOP of Term.t * t
    | ASSIGN of Ident.tvar * Term.t
    | COMPOUND of t * t
    | CHOICE of Term.t * t * t
    | TICK of Term.t
    | OBSERVE of Formula.t
    | SKIP

  let is_if = function IF _ -> true | _ -> false
  let is_while = function WHILE _ -> true | _ -> false
  let is_loop = function LOOP _ -> true | _ -> false
  let is_assign = function ASSIGN _ -> true | _ -> false
  let is_compound = function COMPOUND _ -> true | _ -> false
  let is_choice = function CHOICE _ -> true | _ -> false
  let is_tick = function TICK _ -> true | _ -> false
  let is_observe = function OBSERVE _ -> true | _ -> false
  let is_skip = function SKIP -> true | _ -> false
  let mk_if cond_fml t_stmt f_stmt = IF (cond_fml, t_stmt, f_stmt)
  let mk_while cond_fml body_stmt = WHILE (cond_fml, body_stmt)
  let mk_loop n stmt = LOOP (n, stmt)
  let mk_assign varname term = ASSIGN (varname, term)
  let mk_compound stmt1 stmt2 = COMPOUND (stmt1, stmt2)
  let mk_choice cond stmt1 stmt2 = CHOICE (cond, stmt1, stmt2)
  let mk_tick expr = TICK expr
  let mk_observe fml = OBSERVE fml
  let mk_skip () = SKIP

  let let_if = function
    | IF (cond_fml, t_stmt, f_stmt) -> (cond_fml, t_stmt, f_stmt)
    | _ -> assert false

  let let_loop = function LOOP (n, stmt) -> (n, stmt) | _ -> assert false

  let let_assign = function
    | ASSIGN (varname, term) -> (varname, term)
    | _ -> assert false

  let let_compound = function
    | COMPOUND (stmt1, stmt2) -> (stmt1, stmt2)
    | _ -> assert false

  let _varname_of_assign = function
    | ASSIGN (varname, t) -> (varname, Term.sort_of t)
    | _ -> assert false

  let make_indent indent = String.make indent ' '
  let _string_of_args = String.concat_map_list ~sep:", " ~f:Term.str_of

  let rec string_of ?(indent = 0) = function
    | IF (cond_fml, t_stmt, f_stmt) ->
        if is_skip f_stmt then
          sprintf "%sif (%s) {\n%s\n%s}" (make_indent indent)
            (Formula.str_of cond_fml)
            (string_of ~indent:(indent + 2) t_stmt)
            (make_indent indent)
        else
          sprintf "%sif (%s) {\n%s\n%s}\n%selse {\n%s\n%s}" (make_indent indent)
            (Formula.str_of cond_fml)
            (string_of ~indent:(indent + 2) t_stmt)
            (make_indent indent) (make_indent indent)
            (string_of ~indent:(indent + 2) f_stmt)
            (make_indent indent)
    | WHILE (cond_fml, body_stmt) ->
        sprintf "%swhile (%s) {\n%s\n%s}" (make_indent indent)
          (Formula.str_of cond_fml)
          (string_of ~indent:(indent + 2) body_stmt)
          (make_indent indent)
    | LOOP (n, stmt) ->
        sprintf "%sloop (%s) {\n%s\n%s}" (make_indent indent) (Term.str_of n)
          (string_of ~indent:(indent + 2) stmt)
          (make_indent indent)
    | ASSIGN (varname, term) ->
        sprintf "%s%s := %s;" (make_indent indent)
          (Ident.str_of_tvar varname)
          (Term.str_of term)
    | COMPOUND (stmt1, stmt2) ->
        sprintf "%s\n%s" (string_of ~indent stmt1) (string_of ~indent stmt2)
    | CHOICE (cond, stmt1, stmt2) ->
        sprintf "%s{\n%s\n%s}[%s]{\n%s\n%s}" (make_indent indent)
          (string_of ~indent:(indent + 2) stmt1)
          (make_indent indent) (Term.str_of cond)
          (string_of ~indent:(indent + 2) stmt2)
          (make_indent indent)
    | TICK expr -> sprintf "%stick(%s);" (make_indent indent) (Term.str_of expr)
    | OBSERVE fml ->
        sprintf "%sobserve(%s);" (make_indent indent) (Formula.str_of fml)
    | SKIP -> sprintf "%sskip;" (make_indent indent)

  let _subst_args sub = List.map ~f:(Term.subst sub)

  let rec subst sub stmt =
    match stmt with
    | IF (cond_fml, t_stmt, f_stmt) ->
        let t_stmt = subst sub t_stmt in
        let f_stmt = subst sub f_stmt in
        mk_if (Formula.subst sub cond_fml) t_stmt f_stmt
    | WHILE (cond_fml, body_stmt) ->
        let body_stmt = subst sub body_stmt in
        mk_while (Formula.subst sub cond_fml) body_stmt
    | LOOP (n', stmt') ->
        let n' = Term.subst sub n' in
        let stmt' = subst sub stmt' in
        mk_loop n' stmt'
    | ASSIGN (varname, term) -> mk_assign varname (Term.subst sub term)
    | COMPOUND (stmt1, stmt2) ->
        let stmt1 = subst sub stmt1 in
        let stmt2 = subst sub stmt2 in
        mk_compound stmt1 stmt2
    | CHOICE (cond, stmt1, stmt2) ->
        let stmt1 = subst sub stmt1 in
        let stmt2 = subst sub stmt2 in
        mk_choice (Term.subst sub cond) stmt1 stmt2
    | TICK expr -> mk_tick (Term.subst sub expr)
    | OBSERVE fml -> mk_observe (Formula.subst sub fml)
    | SKIP -> stmt

  let get_inner_statements = function
    | IF (_, stmt1, stmt2) | COMPOUND (stmt1, stmt2) | CHOICE (_, stmt1, stmt2)
      ->
        [ stmt1; stmt2 ]
    | LOOP (_, stmt) | WHILE (_, stmt) -> [ stmt ]
    | ASSIGN _ | TICK _ | OBSERVE _ | SKIP -> []

  let rec get_read_vars_rep used_labels = function
    | IF (cond_fml, t_stmt, f_stmt) ->
        let vars1, used_labels = get_read_vars_rep used_labels t_stmt in
        let vars2, used_labels = get_read_vars_rep used_labels f_stmt in
        ( Formula.term_sort_env_of cond_fml
          |> Variables.of_tvarset |> Variables.union vars1
          |> Variables.union vars2,
          used_labels )
    | WHILE (cond_fml, body_stmt) ->
        let vars_body, used_labels = get_read_vars_rep used_labels body_stmt in
        ( Formula.term_sort_env_of cond_fml
          |> Variables.of_tvarset |> Variables.union vars_body,
          used_labels )
    | LOOP (_, stmt') -> get_read_vars_rep used_labels stmt'
    | ASSIGN (_, term) ->
        (Term.term_sort_env_of term |> Variables.of_tvarset, used_labels)
    | COMPOUND (stmt1, stmt2) ->
        let vars1, used_labels = get_read_vars_rep used_labels stmt1 in
        let vars2, used_labels = get_read_vars_rep used_labels stmt2 in
        (Variables.union vars1 vars2, used_labels)
    | CHOICE (cond_expr, t_stmt, f_stmt) ->
        let vars1, used_labels = get_read_vars_rep used_labels t_stmt in
        let vars2, used_labels = get_read_vars_rep used_labels f_stmt in
        ( Term.term_sort_env_of cond_expr
          |> Variables.of_tvarset |> Variables.union vars1
          |> Variables.union vars2,
          used_labels )
    | OBSERVE fml ->
        (Formula.term_sort_env_of fml |> Variables.of_tvarset, used_labels)
    | TICK term ->
        (Term.term_sort_env_of term |> Variables.of_tvarset, used_labels)
    | SKIP -> (Variables.empty, used_labels)

  let get_read_vars stmt =
    let vars, _ = get_read_vars_rep Variables.empty stmt in
    vars

  let rec of_statements = function
    | [] -> mk_skip ()
    | stmt :: [] -> stmt
    | stmt :: tail -> mk_compound stmt (of_statements tail)
end

and Program : sig
  (* {
    bounds : sort_env_list;
    left : Formula.t option;
    kind : kind;
    name : Ident.tvar;
    args : Term.t list;
    bound : Term.t;
  } *)

  type const = Ident.tvar * Sort.t * Term.t

  type t = {
    vars : sort_env_list;
    consts : const list;
    nat_vars : Ident.tvar list;
    stmts : Statement.t;
    query : Query.t;
  }

  val make :
    ?nat_vars:Ident.tvar list -> sort_env_list * const list -> Statement.t -> Query.t -> t

  val str_of : t -> string
  val sort_env_list_of_decls : t -> sort_env_list
  val typeinf_consts : print:(string lazy_t -> unit) -> t -> const list
  val wpt :
    print:(string lazy_t -> unit) ->
    ?ert:bool ->
    ?f:Term.t ->
    ?fail:Term.t ->
    ?err:Term.t ->
    t ->
    EquationSystem.t
end = struct
  (* {
    bounds : sort_env_list;
    left : Formula.t option;
    kind : kind;
    name : Ident.tvar;
    args : Term.t list;
    bound : Term.t;
  } *)

  type const = Ident.tvar * Sort.t * Term.t

  type t = {
    vars : sort_env_list;
    consts : const list;
    nat_vars : Ident.tvar list;
    stmts : Statement.t;
    query : Query.t;
  }

  let make ?(nat_vars = []) (vars, consts) stmts query =
    { vars; consts; nat_vars; stmts; query }

  let sort_env_list_of_decls pgcl =
    pgcl.vars @ (pgcl.consts |> List.map ~f:(fun (var, sort, _) -> (var, sort)))

  let typeinf_const ~print senv (var, sort, term) =
    let term' =
      match sort with
      | Sort.SVar _ -> Typeinf.typeinf_term ~print ~default:None ~senv term
      | _ -> term
    in
    (var, Term.sort_of term', term')

  let typeinf_consts ~print pgcl =
    let senv acc = Map.Poly.of_alist_exn @@ acc in
    List.fold_left pgcl.consts ~init:(pgcl.vars, [])
      ~f:(fun (acc, consts') const ->
        let const' = typeinf_const ~print (senv acc) const in
        let var, sort, _ = const' in
        ((var, sort) :: acc, const' :: consts'))
    |> snd

  let str_of pgcl =
    sprintf "Decls:%s\nConsts:%s\nStmts:%s"
      (str_of_sort_env_list Term.str_of_sort pgcl.vars)
      (String.concat_map_list ~sep:"\n"
         ~f:(fun (var, sort, term) ->
           sprintf "%s: %s = %s;" (Ident.name_of_tvar var)
             (Term.str_of_sort sort) (Term.str_of term))
         pgcl.consts)
      (Statement.string_of pgcl.stmts)

  (* weakest preexpectation transformer.  [fail] is the value of a run that
     fails an observation: [wp(observe(b), X) = [b] * X + [not b] * fail].
     With [fail = 0] this is the unnormalised [wp] of Olmedo et al. (TOPLAS
     2018); a constant [fail = q >= 0] makes it the expected reward of a run
     that earns [f] when it terminates, [q] when an observation blocks it and
     0 when it diverges, that is [wp(S, f) + q * (1 - wlp(S, 1))], the
     identity the conditional reductions in [Util] rest on.  Every loop is a
     least fixpoint, whatever [fail] is. *)

  (* [guard_weight ~err p e] is the preexpectation of a choice weighted by
     [p] whose rule gives [e] when [p] is a probability.  [p * X + (1 - p) * Y]
     is an expectation transformer only for [0 <= p <= 1]: at a state where a
     weight over program variables lies outside the interval one branch has a
     negative coefficient, and a bound was proved about a program that has no
     such distribution ([E[c] >= 1.5] where every outcome of [c] is 0 or 1,
     with weight 2).  Such a run is an error from which no bound may be
     proved, so it is worth [err] there: [ite(0 <= p <= 1, e, err)].  The
     caller chooses [err] against the claim: 0 for a lower bound, and for an
     upper bound the run is worth +oo, which no term expresses, so the caller
     sets [err = 1] with [f = 0] to obtain the probability of reaching the
     error and makes the upper bound fail wherever it is positive.  Worth 0 an
     error run is a diverging one, whatever [fail] is, so the identities the
     conditional reductions rest on (every run terminates, is blocked or
     diverges) still hold.  A closed weight is refused outside the interval
     before the reduction, so it needs no guard. *)
  let guard_weight ~err p e =
    if Set.is_empty (Term.fvs_of p) then e
    else
      T_bool.mk_if_then_else
        (T_bool.of_formula
           (Formula.and_of
              [
                Formula.geq p (T_real.rzero ()); Formula.leq p (T_real.rone ());
              ]))
        e err

  (* The two weights [p] and [1 - p] of a choice; their sum is 1.  A closed
     weight is folded to two rational literals first, reading [/] as exact
     division (as the weight's range check does).  Left unfolded, [1 - 1/2]
     reaches the linear normaliser while [1/2] is still a division, which
     distributes [(1 - 1/2) * X] into [X - X * 1/2]: an unknown under a
     subtraction, outside the QFL grammar, which the QFL checker refuses for
     every loop whose choice weight is written as a fraction.  A weight over
     program variables keeps the symbolic form. *)
  let weights p =
    let complement p = T_num.mk_nsub (T_real.rone ()) p in
    if not (Set.is_empty (Term.fvs_of p)) then (p, complement p)
    else
      match
        Evaluator.simplify_term
        @@ Typeinf.typeinf_term
             ~print:(fun _ -> ())
             ~default:(Some T_real.SReal) p
      with
      | t when T_real.is_real t ->
          let q = T_real.let_real t in
          (T_real.mk_real q, T_real.mk_real Q.(one - q))
      | _ -> (p, complement p)

  (* With [ert] the transformer is a variant of the expected-runtime calculus
     of Kaminski, Katoen, Matheja and Olmedo (ESOP 2016), which charges one
     unit per statement; here only ticks cost: every rule
     is [wp]'s except [ert(tick(r), X) = r + X], so a tick is the only
     statement that costs time and [ert(S, f)] is the expected total of the
     ticks a run pays plus [f] at its end; a loop is still the least fixpoint
     of its body's transformer.  Requires every [r] to be non-negative and
     the program to have no [observe] (checked by the caller): QFL's values
     lie in [0, oo], and the calculus has no rule for conditioning.  Without
     [ert] a tick costs nothing and this is [wp]. *)
  let rec wpt_rep ~ert ~fail ~err (pgcl : t) eqs : EquationSystem.t =
    let wpt_rep = wpt_rep ~ert ~fail ~err in
    match pgcl.stmts with
    | SKIP -> eqs
    | IF (cond_fml, t_stmt, f_stmt) ->
        let eq_t = wpt_rep { pgcl with stmts = t_stmt } eqs in
        let eq_f = wpt_rep { pgcl with stmts = f_stmt } eqs in
        {
          qf =
            T_bool.mk_if_then_else (T_bool.of_formula cond_fml) eq_t.qf eq_f.qf;
          equations = PredSet.union eq_t.equations eq_f.equations;
        }
        (* TODO: calculate arguments of predicate *)
    | WHILE (cond_fml, body_stmt) ->
        let new_pred_var = Ident.mk_fresh_tvar () in
        let new_pred_app =
          Term.fvar_app_of_senv new_pred_var
            (sort_env_list_of_decls pgcl)
            T_real.SReal
        in
        let eq_body =
          wpt_rep { pgcl with stmts = body_stmt } { eqs with qf = new_pred_app }
        in
        let loop_formula =
          T_bool.mk_if_then_else (T_bool.of_formula cond_fml) eq_body.qf eqs.qf
        in
        let loop_pred =
          Pred.make Predicate.Mu new_pred_var
            (sort_env_list_of_decls pgcl)
            loop_formula
        in
        {
          qf = new_pred_app;
          equations = PredSet.add loop_pred eq_body.equations;
        }
    | LOOP (n, body_stmt) ->
        (* [loop(n) { S }] runs [S] exactly [n] times, so its weakest
           preexpectation is [wp(S, ...wp(S, f)...)] with [n] applications;
           the grammar admits only a natural-number literal for [n].  Each
           application builds its own equations: a [while] inside [S] gets a
           fresh function per copy, defined by the same body. *)
        let n =
          match n with
          | Term.FunApp (T_int.Int n, [], _) when Z.(geq n zero) && Z.fits_int n
            ->
              Z.to_int n
          | _ ->
              Common.Refusal.refuse
                "the repetition count %s of a loop statement is not a natural \
                 number"
                (Term.str_of n)
        in
        Fn.apply_n_times ~n (wpt_rep { pgcl with stmts = body_stmt }) eqs
    | ASSIGN (varname, term) ->
        let map = Map.Poly.of_alist_exn [ (varname, term) ] in
        { qf = Term.subst map eqs.qf; equations = eqs.equations }
    | COMPOUND (stmt1, stmt2) ->
        let f_inter = wpt_rep { pgcl with stmts = stmt2 } eqs in
        wpt_rep { pgcl with stmts = stmt1 } f_inter
    | CHOICE (cond, t_stmt, f_stmt) ->
        let eq_t = wpt_rep { pgcl with stmts = t_stmt } eqs in
        let eq_f = wpt_rep { pgcl with stmts = f_stmt } eqs in
        let p, not_p = weights cond in
        {
          qf =
            guard_weight ~err cond
              (T_num.mk_nadd
                 (T_num.mk_nmul p eq_t.qf)
                 (T_num.mk_nmul not_p eq_f.qf));
          equations = PredSet.union eq_t.equations eq_f.equations;
        }
    | TICK r when ert -> { eqs with qf = T_num.mk_nadd r eqs.qf }
    | TICK _ -> eqs
    | OBSERVE fml ->
        {
          qf = T_bool.mk_if_then_else (T_bool.of_formula fml) eqs.qf fail;
          equations = eqs.equations;
        }

  let wpt ~print ?(ert = false) ?f ?(fail = T_real.rzero ())
      ?(err = T_real.rzero ()) (pgcl : t) =
    let f = Option.value f ~default:(Query.of_term pgcl.query) in
    EquationSystem.simplify @@ EquationSystem.normalize
    @@ EquationSystem.typeinf ~print pgcl
    @@ wpt_rep ~ert ~fail ~err pgcl { qf = f; equations = PredSet.empty }
  (* if f is nat, translate into real *)
end

and Query : sig
  type bound_kind = Upper | Lower

  (** which conditional expectation a bound speaks of, for a program with
      [observe] (Olmedo et al., Conditioning in Probabilistic Programming,
      TOPLAS 40(1), 2018): [Cwp] is [wp(S, f) / wlp(S, 1)], where a diverging
      run counts as one that passed the observations, [Cwlp] its liberal
      [wlp(S, g) / wlp(S, 1)] for [g] bounded by 1, and [R2] is
      [wp(S, f) / wp(S, 1)], normalised over the terminating runs.  Without
      [observe], [Cwp] is [wp(S, f)].  [Ert] is not a conditional
      expectation: it is [ert(S, f)], the expected runtime (the expected sum
      of the ticks) plus [f], defined only for a program without [observe]. *)
  type transformer = Cwp | Cwlp | R2 | Ert

  type bound = {
    post : Term.t;
    kind : bound_kind;
    value : Term.t;
    strict : bool;
    transformer : transformer;
  }

  type t = Expectation of Term.t | Probability of Formula.t | Bound of bound

  val mk_expectation : Term.t -> t
  val mk_bound :
    Term.t -> bound_kind -> ?strict:bool -> ?transformer:transformer -> Term.t -> t

  (** [transformer_of_string name] reads [cwp], [cwlp] or [r2] *)
  val transformer_of_string : string -> transformer option
  val mk_probability : Formula.t -> t
  val of_term : t -> Term.t
  val bound_of : t -> bound option

  (** which of the three query forms this is, for a message the user reads *)
  val describe : t -> string
end = struct
  type bound_kind = Upper | Lower
  type transformer = Cwp | Cwlp | R2 | Ert

  type bound = {
    post : Term.t;
    kind : bound_kind;
    value : Term.t;
    strict : bool;
    transformer : transformer;
  }

  type t = Expectation of Term.t | Probability of Formula.t | Bound of bound

  let mk_expectation expr = Expectation expr
  let mk_bound post kind ?(strict = false) ?(transformer = Cwp) value =
    Bound { post; kind; value; strict; transformer }

  let transformer_of_string = function
    | "cwp" -> Some Cwp
    | "cwlp" -> Some Cwlp
    | "r2" -> Some R2
    | _ -> None

  let mk_probability fml = Probability fml

  let of_term = function
    | Expectation expr -> expr
    | Probability fml -> T_bool.of_formula fml
    | Bound { post; _ } -> post

  let bound_of = function Bound bound -> Some bound | _ -> None

  let describe = function
    | Expectation _ -> "the expected value of an expression"
    | Probability _ -> "the probability of a condition"
    | Bound { transformer = Ert; _ } ->
        "a bound on the expected runtime plus an expression"
    | Bound _ -> "a bound on the expected value of an expression"
end
