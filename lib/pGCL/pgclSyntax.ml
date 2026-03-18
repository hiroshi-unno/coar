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
        sprintf "%swhile (%s) {\n%s\n%s}" (make_indent indent) (Term.str_of n)
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
    stmts : Statement.t;
    query : Query.t;
  }

  val make : sort_env_list * const list -> Statement.t -> Query.t -> t
  val str_of : t -> string
  val sort_env_list_of_decls : t -> sort_env_list
  val typeinf_consts : print:(string lazy_t -> unit) -> t -> const list
  val wpt : print:(string lazy_t -> unit) -> ?f:Term.t -> t -> EquationSystem.t
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
    stmts : Statement.t;
    query : Query.t;
  }

  let make (vars, consts) stmts query = { vars; consts; stmts; query }

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

  (* weakest preexpectation transformer *)
  let rec wpt_rep (pgcl : t) eqs : EquationSystem.t =
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
    | LOOP (_, stmt') ->
        let _ = wpt_rep { pgcl with stmts = stmt' } eqs in
        assert false (* TODO: fixme *)
    | ASSIGN (varname, term) ->
        let map = Map.Poly.of_alist_exn [ (varname, term) ] in
        { qf = Term.subst map eqs.qf; equations = eqs.equations }
    | COMPOUND (stmt1, stmt2) ->
        let f_inter = wpt_rep { pgcl with stmts = stmt2 } eqs in
        wpt_rep { pgcl with stmts = stmt1 } f_inter
    | CHOICE (cond, t_stmt, f_stmt) ->
        let eq_t = wpt_rep { pgcl with stmts = t_stmt } eqs in
        let eq_f = wpt_rep { pgcl with stmts = f_stmt } eqs in
        {
          qf =
            T_num.mk_nadd
              (T_num.mk_nmul cond eq_t.qf)
              (T_num.mk_nmul (T_num.mk_nsub (T_real.rone ()) cond) eq_f.qf);
          equations = PredSet.union eq_t.equations eq_f.equations;
        }
    | TICK _ -> eqs
    | OBSERVE fml ->
        {
          qf =
            T_bool.mk_if_then_else (T_bool.of_formula fml) eqs.qf
              (T_real.rzero ());
          equations = eqs.equations;
        }

  let wpt ~print ?f (pgcl : t) =
    let f = Option.value f ~default:(Query.of_term pgcl.query) in
    EquationSystem.simplify @@ EquationSystem.normalize
    @@ EquationSystem.typeinf ~print pgcl
    @@ wpt_rep pgcl { qf = f; equations = PredSet.empty }
  (* if f is nat, translate into real *)
end

and Query : sig
  type t = Expectation of Term.t | Probability of Formula.t

  val mk_expectation : Term.t -> t
  val mk_probability : Formula.t -> t
  val of_term : t -> Term.t
end = struct
  type t = Expectation of Term.t | Probability of Formula.t

  let mk_expectation expr = Expectation expr
  let mk_probability fml = Probability fml

  let of_term = function
    | Expectation expr -> expr
    | Probability fml -> T_bool.of_formula fml
end
