(* Abstract syntax of SGCL, a probabilistic guarded command language with
   undeclared numeric variables, and its reduction to QFL.  Statements are
   assignment (also in increment and decrement form), conditional, loop,
   probabilistic choice, a loop that continues with a given probability
   ([WHILE_FLIP]) and observation; a program's variables are all those its
   statements mention, each an integer or a real as [SGCL.Util.infer_sorts]
   decides.  [Program.wpt] is the
   weakest-preexpectation transformer: it returns the preexpectation of the
   program's post-expectation as a real-valued term together with one
   least-fixpoint equation per loop, the input of the QFL solver.  A failing
   observation contributes a given value, 0 unless [Util]'s reduction of a
   conditional expectation asks for another. *)
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
end = struct
  type t = { qf : Term.t; equations : PredSet.t }

  let typeinf ~print (pgcl : Program.t) eqs =
    {
      qf =
        Typeinf.typeinf_term ~print ~default:(Some T_real.SReal)
          ~senv:(Map.Poly.of_alist_exn pgcl.vars)
          eqs.qf;
      equations =
        PredSet.map
          (fun pred ->
            {
              pred with
              body =
                Typeinf.typeinf_term ~print ~default:(Some T_real.SReal)
                  ~senv:(Map.Poly.of_alist_exn pgcl.vars)
                  pred.body;
            })
          eqs.equations;
    }

  let str_of (eqs : t) =
    sprintf "QF: %s\nEquations:\n%s" (Term.str_of eqs.qf)
      (String.concat ~sep:"\n"
         (List.map ~f:Pred.str_of (PredSet.elements eqs.equations)))
end

and Statement : sig
  type t =
    | IF of Formula.t * t * t
    | WHILE of Formula.t * t
    | WHILE_FLIP of Term.t * t
    | ASSIGN of Ident.tvar * Term.t
    | PLUSASSIGN of Ident.tvar * Term.t
    | MINUSASSIGN of Ident.tvar * Term.t
    | COMPOUND of t * t
    | CHOICE of Term.t * t * t
    | OBSERVE of Formula.t
    | SKIP

  val is_if : t -> bool
  val is_while : t -> bool
  val is_while_flip : t -> bool
  val is_assign : t -> bool
  val is_compound : t -> bool
  val is_choice : t -> bool
  val is_plus_assign : t -> bool
  val is_minus_assign : t -> bool
  val is_observe : t -> bool
  val is_skip : t -> bool
  val mk_if : Formula.t -> t -> t -> t
  val mk_while : Formula.t -> t -> t
  val mk_while_flip : Term.t -> t -> t
  val mk_assign : Ident.tvar -> Term.t -> t
  val mk_compound : t -> t -> t
  val mk_choice : Term.t -> t -> t -> t
  val mk_plus_assign : Ident.tvar -> Term.t -> t
  val mk_minus_assign : Ident.tvar -> Term.t -> t
  val mk_observe : Formula.t -> t
  val mk_skip : unit -> t
  val let_if : t -> Formula.t * t * t
  val let_assign : t -> Ident.tvar * Term.t
  val let_plus_assign : t -> Ident.tvar * Term.t
  val let_minus_assign : t -> Ident.tvar * Term.t
  val let_compound : t -> t * t
  val string_of : ?indent:int -> t -> string
  val subst : TermSubst.t -> t -> t
  val get_inner_statements : t -> t list
  val collect_all_vars : t -> (Ident.tvar * Ast.LogicOld.Sort.t) list
  val of_statements : t list -> t
end = struct
  type t =
    | IF of Formula.t * t * t
    | WHILE of Formula.t * t
    | WHILE_FLIP of Term.t * t
    | ASSIGN of Ident.tvar * Term.t
    | PLUSASSIGN of Ident.tvar * Term.t
    | MINUSASSIGN of Ident.tvar * Term.t
    | COMPOUND of t * t
    | CHOICE of Term.t * t * t
    | OBSERVE of Formula.t
    | SKIP

  let is_if = function IF _ -> true | _ -> false
  let is_while = function WHILE _ -> true | _ -> false
  let is_while_flip = function WHILE_FLIP _ -> true | _ -> false
  let is_assign = function ASSIGN _ -> true | _ -> false
  let is_compound = function COMPOUND _ -> true | _ -> false
  let is_choice = function CHOICE _ -> true | _ -> false
  let is_plus_assign = function PLUSASSIGN _ -> true | _ -> false
  let is_minus_assign = function MINUSASSIGN _ -> true | _ -> false
  let is_observe = function OBSERVE _ -> true | _ -> false
  let is_skip = function SKIP -> true | _ -> false
  let mk_if cond_fml t_stmt f_stmt = IF (cond_fml, t_stmt, f_stmt)
  let mk_while cond_fml body_stmt = WHILE (cond_fml, body_stmt)
  let mk_while_flip prob body_stmt = WHILE_FLIP (prob, body_stmt)
  let mk_assign varname term = ASSIGN (varname, term)
  let mk_plus_assign varname term = PLUSASSIGN (varname, term)
  let mk_minus_assign varname term = MINUSASSIGN (varname, term)
  let mk_compound stmt1 stmt2 = COMPOUND (stmt1, stmt2)
  let mk_choice cond stmt1 stmt2 = CHOICE (cond, stmt1, stmt2)
  let mk_observe fml = OBSERVE fml
  let mk_skip () = SKIP

  let let_if = function
    | IF (cond_fml, t_stmt, f_stmt) -> (cond_fml, t_stmt, f_stmt)
    | _ -> assert false

  let let_assign = function
    | ASSIGN (varname, term) -> (varname, term)
    | _ -> assert false

  let let_plus_assign = function
    | PLUSASSIGN (varname, term) -> (varname, term)
    | _ -> assert false

  let let_minus_assign = function
    | MINUSASSIGN (varname, term) -> (varname, term)
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
    | WHILE_FLIP (prob, body_stmt) ->
        sprintf "%swhile flip(%s) {\n%s\n%s}" (make_indent indent)
          (Term.str_of prob)
          (string_of ~indent:(indent + 2) body_stmt)
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
    | PLUSASSIGN (varname, term) ->
        sprintf "%s%s += %s;" (make_indent indent)
          (Ident.str_of_tvar varname)
          (Term.str_of term)
    | MINUSASSIGN (varname, term) ->
        sprintf "%s%s -= %s;" (make_indent indent)
          (Ident.str_of_tvar varname)
          (Term.str_of term)
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
    | WHILE_FLIP (prob, body_stmt) ->
        let body_stmt = subst sub body_stmt in
        mk_while_flip (Term.subst sub prob) body_stmt
    | ASSIGN (varname, term) -> mk_assign varname (Term.subst sub term)
    | PLUSASSIGN (varname, term) -> mk_plus_assign varname (Term.subst sub term)
    | MINUSASSIGN (varname, term) ->
        mk_minus_assign varname (Term.subst sub term)
    | COMPOUND (stmt1, stmt2) ->
        let stmt1 = subst sub stmt1 in
        let stmt2 = subst sub stmt2 in
        mk_compound stmt1 stmt2
    | CHOICE (cond, stmt1, stmt2) ->
        let stmt1 = subst sub stmt1 in
        let stmt2 = subst sub stmt2 in
        mk_choice (Term.subst sub cond) stmt1 stmt2
    | OBSERVE fml -> mk_observe (Formula.subst sub fml)
    | SKIP -> stmt

  let get_inner_statements = function
    | IF (_, stmt1, stmt2) | COMPOUND (stmt1, stmt2) | CHOICE (_, stmt1, stmt2)
      ->
        [ stmt1; stmt2 ]
    | WHILE (_, stmt) | WHILE_FLIP (_, stmt) -> [ stmt ]
    | ASSIGN _ | PLUSASSIGN _ | MINUSASSIGN _ | OBSERVE _ | SKIP -> []

  let rec collect_all_vars_rep used_labels = function
    | IF (cond_fml, t_stmt, f_stmt) ->
        let vars1, used_labels = collect_all_vars_rep used_labels t_stmt in
        let vars2, used_labels = collect_all_vars_rep used_labels f_stmt in
        ( Formula.term_sort_env_of cond_fml
          |> Variables.of_tvarset |> Variables.union vars1
          |> Variables.union vars2,
          used_labels )
    | WHILE (cond_fml, body_stmt) ->
        let vars_body, used_labels =
          collect_all_vars_rep used_labels body_stmt
        in
        ( Formula.term_sort_env_of cond_fml
          |> Variables.of_tvarset |> Variables.union vars_body,
          used_labels )
    | WHILE_FLIP (prob, body_stmt) ->
        let vars_body, used_labels =
          collect_all_vars_rep used_labels body_stmt
        in
        ( Term.term_sort_env_of prob |> Variables.of_tvarset
          |> Variables.union vars_body,
          used_labels )
    | ASSIGN (varname, term)
    | PLUSASSIGN (varname, term)
    | MINUSASSIGN (varname, term) ->
        let lhs =
          Variables.of_list [ (Ident.name_of_tvar varname, T_real.SReal) ]
        in
        let rhs = Term.term_sort_env_of term |> Variables.of_tvarset in
        (Variables.union lhs rhs, used_labels)
    | COMPOUND (stmt1, stmt2) ->
        let vars1, used_labels = collect_all_vars_rep used_labels stmt1 in
        let vars2, used_labels = collect_all_vars_rep used_labels stmt2 in
        (Variables.union vars1 vars2, used_labels)
    | CHOICE (cond_expr, t_stmt, f_stmt) ->
        let vars1, used_labels = collect_all_vars_rep used_labels t_stmt in
        let vars2, used_labels = collect_all_vars_rep used_labels f_stmt in
        ( Term.term_sort_env_of cond_expr
          |> Variables.of_tvarset |> Variables.union vars1
          |> Variables.union vars2,
          used_labels )
    | OBSERVE fml ->
        (Formula.term_sort_env_of fml |> Variables.of_tvarset, used_labels)
    | SKIP -> (Variables.empty, used_labels)

  let collect_all_vars stmt =
    let vars, _ = collect_all_vars_rep Variables.empty stmt in
    Variables.to_list vars
    |> List.map ~f:(fun (varname, sort) -> (Ident.Tvar varname, sort))

  let rec of_statements = function
    | [] -> mk_skip ()
    | stmt :: [] -> stmt
    | stmt :: tail -> mk_compound stmt (of_statements tail)
end

and Program : sig
  type kind = LB | UB

  (** which conditional expectation a bound speaks of, for a program with
      [observe] (Olmedo et al., Conditioning in Probabilistic Programming,
      TOPLAS 40(1), 2018): [Cwp] is [wp(S, f) / wlp(S, 1)], where a diverging
      run counts as one that passed the observations, [Cwlp] its liberal
      [wlp(S, g) / wlp(S, 1)] for [g] bounded by 1, and [R2] is
      [wp(S, f) / wp(S, 1)], normalised over the terminating runs.  Without
      [observe], [Cwp] is [wp(S, f)]. *)
  type transformer = Cwp | Cwlp | R2

  type bound = {
    post : Term.t;
    kind : kind;
    value : Term.t;
    strict : bool;
    transformer : transformer;
  }

  type query = {
    bounds : sort_env_list;
    left : Formula.t option;
    kind : kind;
    name : Ident.tvar;
    args : Term.t list;
    bound : Term.t;
  }

  type t = {
    vars : sort_env_list;
    stmts : Statement.t;
    f : Term.t;
    bound : bound option;
  }

  val make : ?bound:bound -> Statement.t -> Term.t -> t

  val mk_bound :
    Term.t -> kind -> ?strict:bool -> ?transformer:transformer -> Term.t -> bound

  (** [transformer_of_string name] reads [cwp], [cwlp] or [r2] *)
  val transformer_of_string : string -> transformer option

  val str_of : t -> string

  val wpt :
    print:(string lazy_t -> unit) ->
    ?fail:Term.t ->
    ?err:Term.t ->
    t ->
    EquationSystem.t
end = struct
  type kind = LB | UB
  type transformer = Cwp | Cwlp | R2

  type bound = {
    post : Term.t;
    kind : kind;
    value : Term.t;
    strict : bool;
    transformer : transformer;
  }

  type query = {
    bounds : sort_env_list;
    left : Formula.t option;
    kind : kind;
    name : Ident.tvar;
    args : Term.t list;
    bound : Term.t;
  }

  type t = {
    vars : sort_env_list;
    stmts : Statement.t;
    f : Term.t;
    bound : bound option;
  }

  let make ?bound stmts f =
    { vars = Statement.collect_all_vars stmts; stmts; f; bound }

  let mk_bound post kind ?(strict = false) ?(transformer = Cwp) value =
    { post; kind; value; strict; transformer }

  let transformer_of_string = function
    | "cwp" -> Some Cwp
    | "cwlp" -> Some Cwlp
    | "r2" -> Some R2
    | _ -> None

  let str_of pgcl =
    sprintf "Variables:%s\nStmts:%s"
      (str_of_sort_env_list Term.str_of_sort pgcl.vars)
      (Statement.string_of pgcl.stmts)

  (* the variable [x] at the sort the program gives it (an integer or a real;
     see [SGCL.Util.infer_sorts]) *)
  let var_term_of (pgcl : t) x =
    Term.mk_var x
      (List.Assoc.find pgcl.vars x ~equal:Ident.tvar_equal
      |> Option.value ~default:T_real.SReal)

  (* weakest preexpectation transformer.  [fail] is the value of a run that
     fails an observation: [wp(observe(b), X) = [b] * X + [not b] * fail].
     With [fail = 0] this is the unnormalised [wp] of Olmedo et al. (TOPLAS
     2018); a constant [fail = q >= 0] makes it the expected reward of a run
     that earns [f] when it terminates, [q] when an observation blocks it and
     0 when it diverges, that is [wp(S, f) + q * (1 - wlp(S, 1))], the
     identity the conditional reductions in [Util] rest on.  Every loop is a
     least fixpoint, whatever [fail] is. *)

  (* [guard_weight ~err p e] is the preexpectation of a choice (or of one
     round of [while flip(p)]) weighted by [p] whose rule gives [e] when [p]
     is a probability.  The rule is an expectation transformer only for
     [0 <= p <= 1]: at a state where a weight over program variables lies
     outside the interval a branch has a negative coefficient, and a bound
     could be proved about a program with no such distribution.  Such a run is
     an error from which no bound may be proved, so it is worth [err] there:
     [ite(0 <= p <= 1, e, err)].  The caller chooses [err] against the claim:
     0 for a lower bound, and for an upper bound the run is worth +oo, which no
     term expresses, so the caller sets [err = 1] with [f = 0] to obtain the
     probability of reaching the error and makes the upper bound fail wherever
     it is positive.  Worth 0 an error run is a diverging one, whatever [fail]
     is, so the identities the conditional reductions rest on still hold.  A
     closed probability is refused outside the interval before the reduction,
     so it needs no guard. *)
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

  let rec wpt_rep ~fail ~err (pgcl : t) eqs : EquationSystem.t =
    let wpt_rep = wpt_rep ~fail ~err in
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
          Term.fvar_app_of_senv new_pred_var pgcl.vars T_real.SReal
        in
        let eq_body =
          wpt_rep { pgcl with stmts = body_stmt } { eqs with qf = new_pred_app }
        in
        let loop_formula =
          T_bool.mk_if_then_else (T_bool.of_formula cond_fml) eq_body.qf eqs.qf
        in
        let loop_pred =
          Pred.make Predicate.Mu new_pred_var pgcl.vars loop_formula
        in
        {
          qf = new_pred_app;
          equations = PredSet.add loop_pred eq_body.equations;
        }
    | WHILE_FLIP (prob, body_stmt) ->
        let new_pred_var = Ident.mk_fresh_tvar () in
        let new_pred_app =
          Term.fvar_app_of_senv new_pred_var pgcl.vars T_real.SReal
        in
        let eq_body =
          wpt_rep { pgcl with stmts = body_stmt } { eqs with qf = new_pred_app }
        in
        let loop_formula =
          guard_weight ~err prob
            (T_real.mk_radd
               (T_real.mk_rmul prob eq_body.qf)
               (T_real.mk_rmul (T_real.mk_rsub (T_real.rone ()) prob) eqs.qf))
        in
        let loop_pred =
          Pred.make Predicate.Mu new_pred_var pgcl.vars loop_formula
        in
        {
          qf = new_pred_app;
          equations = PredSet.add loop_pred eq_body.equations;
        }
    | ASSIGN (varname, term) ->
        let map = Map.Poly.of_alist_exn [ (varname, term) ] in
        { qf = Term.subst map eqs.qf; equations = eqs.equations }
    | PLUSASSIGN (varname, term) ->
        let var_term = var_term_of pgcl varname in
        let map =
          Map.Poly.of_alist_exn [ (varname, T_num.mk_nadd var_term term) ]
        in
        { qf = Term.subst map eqs.qf; equations = eqs.equations }
    | MINUSASSIGN (varname, term) ->
        let var_term = var_term_of pgcl varname in
        let map =
          Map.Poly.of_alist_exn [ (varname, T_num.mk_nsub var_term term) ]
        in
        { qf = Term.subst map eqs.qf; equations = eqs.equations }
    | COMPOUND (stmt1, stmt2) ->
        let f_inter = wpt_rep { pgcl with stmts = stmt2 } eqs in
        wpt_rep { pgcl with stmts = stmt1 } f_inter
    | CHOICE (cond, t_stmt, f_stmt) ->
        let eq_t = wpt_rep { pgcl with stmts = t_stmt } eqs in
        let eq_f = wpt_rep { pgcl with stmts = f_stmt } eqs in
        {
          qf =
            guard_weight ~err cond
              (T_real.mk_radd
                 (T_real.mk_rmul cond eq_t.qf)
                 (T_real.mk_rmul (T_real.mk_rsub (T_real.rone ()) cond) eq_f.qf));
          equations = PredSet.union eq_t.equations eq_f.equations;
        }
    | OBSERVE fml ->
        {
          qf = T_bool.mk_if_then_else (T_bool.of_formula fml) eqs.qf fail;
          equations = eqs.equations;
        }

  let wpt ~print ?(fail = T_real.rzero ()) ?(err = T_real.rzero ()) (pgcl : t)
      =
    EquationSystem.typeinf ~print pgcl
    @@ wpt_rep ~fail ~err pgcl { qf = pgcl.f; equations = PredSet.empty }
end
