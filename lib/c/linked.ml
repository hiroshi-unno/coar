(* The C frontend's statement graph: a program as linked statements, the form
   the optimiser and the fixpoint-logic translation work on.

   [LinkedStatement.of_statement] turns the structured statements of
   [CSyntax.Statement] into a control-flow graph whose loops are cycles: each
   statement holds its successors as [t ref] fields, and the optimiser assigns
   to those references in place while maps built from the graph are still
   being read.  So a statement must never be hashed or compared on its
   contents -- the hash of a live key would change under the table, and a
   missed lookup reads as the lattice bottom.  Key statements by physical
   equality or by the identity every statement carries
   ([LinkedStatementHashtbl]).

   [mk_exit] returns one shared exit statement on purpose: code that
   deduplicates statements by physical equality treats all exits as one node,
   and allocating a fresh exit per call silently changes what the optimiser
   produces. *)

open Core
open Ast
open Ast.LogicOld
open CSyntax

exception Error of string

module LinkedStatement : sig
  type node =
    | IF of Formula.t * t ref * t ref
    | ASSIGN of string * Term.t * t ref
    | NONDET_INT_ASSIGN of string * t ref
    | NONDET_REAL_ASSIGN of string * t ref
    | NONDET of t ref * t ref
    | ASSUME of Formula.t * t ref
    | NOP of t ref
    | EXIT

  and t = { id : int; node : node }
  (** Every statement carries an identity that does not change when the graph
      around it does. Without one a statement can only be recognised by physical
      equality, so every map over statements has to be an association list
      scanned linearly -- and hashing the statement instead is not an
      alternative, because a statement holds mutable references to its
      successors and the optimiser assigns to them, so [Hashtbl.hash], which
      walks the structure, gives a different answer for the same key before and
      after. The identity makes a hashed lookup stable. *)

  val id_of : t -> int
  val is_if : t -> bool
  val is_assign : t -> bool
  val is_nondet_int_assign : t -> bool
  val is_nondet_real_assign : t -> bool
  val is_nondet : t -> bool
  val is_assume : t -> bool
  val is_nop : t -> bool
  val is_exit : t -> bool
  val mk_if : Formula.t -> t ref -> t ref -> t
  val mk_assign : string -> Term.t -> t ref -> t
  val mk_nondet_int_assign : string -> t ref -> t
  val mk_nondet_real_assign : string -> t ref -> t
  val mk_nondet : t ref -> t ref -> t
  val mk_assume : Formula.t -> t ref -> t
  val mk_nop : t ref -> t
  val mk_exit : unit -> t
  val let_if : t -> Formula.t * t ref * t ref
  val let_assign : t -> string * Term.t * t ref
  val let_nondet_int_assign : t -> string * t ref
  val let_nondet_real_assign : t -> string * t ref
  val let_assume : t -> Formula.t * t ref
  val let_nondet : t -> t ref * t ref
  val let_nop : t -> t ref
  val of_statement : Statement.t -> t
  val get_read_vars : t -> Variables.t
  val get_written_vars : t -> Variables.t
  val get_used_vars : t -> Variables.t
  val get_read_vars_from : t -> Variables.t
  val get_written_vars_from : t -> Variables.t
  val get_used_vars_from : t -> Variables.t
  val string_of : ?info:(t -> string) -> t -> string
  val get_next_statements : t -> t list
  val get_next_statements_ref : t -> t ref list
  val get_all_statements : t -> t list

  val sub : Ident.tvar -> Term.t -> t -> t
  (** this returns fresh stmt but this doesn't fix the other links *)
end = struct
  type node =
    | IF of Formula.t * t ref * t ref
    | ASSIGN of string * Term.t * t ref
    | NONDET_INT_ASSIGN of string * t ref
    | NONDET_REAL_ASSIGN of string * t ref
    | NONDET of t ref * t ref
    | ASSUME of Formula.t * t ref
    | NOP of t ref
    | EXIT

  and t = { id : int; node : node }
  (** Every statement carries an identity that does not change when the graph
      around it does. Without one a statement can only be recognised by physical
      equality, so every map over statements has to be an association list
      scanned linearly -- and hashing the statement instead is not an
      alternative, because a statement holds mutable references to its
      successors and the optimiser assigns to them, so [Hashtbl.hash], which
      walks the structure, gives a different answer for the same key before and
      after. The identity makes a hashed lookup stable. *)

  let __next_id = ref 0

  let mk node =
    Stdlib.incr __next_id;
    { id = !__next_id; node }

  let id_of stmt = stmt.id
  let is_if stmt = match stmt.node with IF _ -> true | _ -> false
  let is_assign stmt = match stmt.node with ASSIGN _ -> true | _ -> false

  let is_nondet_int_assign stmt =
    match stmt.node with NONDET_INT_ASSIGN _ -> true | _ -> false

  let is_nondet_real_assign stmt =
    match stmt.node with NONDET_REAL_ASSIGN _ -> true | _ -> false

  let is_nondet stmt = match stmt.node with NONDET _ -> true | _ -> false
  let is_assume stmt = match stmt.node with ASSUME _ -> true | _ -> false
  let is_nop stmt = match stmt.node with NOP _ -> true | _ -> false
  let is_exit stmt = match stmt.node with EXIT -> true | _ -> false
  let mk_if cond_fml t_stmt f_stmt = mk (IF (cond_fml, t_stmt, f_stmt))
  let mk_assign varname term nxt_stmt = mk (ASSIGN (varname, term, nxt_stmt))

  let mk_nondet_int_assign varname nxt_stmt =
    mk (NONDET_INT_ASSIGN (varname, nxt_stmt))

  let mk_nondet_real_assign varname nxt_stmt =
    mk (NONDET_REAL_ASSIGN (varname, nxt_stmt))

  let mk_nondet stmt1 stmt2 = mk (NONDET (stmt1, stmt2))
  let mk_assume fml nxt_stmt = mk (ASSUME (fml, nxt_stmt))
  let mk_nop stmt = mk (NOP stmt)

  (* One shared exit, deliberately. Before statements carried an identity,
     [EXIT] was a constant constructor, so every exit in a graph was physically
     the same value and everything that deduplicates statements by physical
     equality -- [get_all_statements], the statement maps -- treated them as one
     node. Allocating a fresh record per exit silently separates them and
     changes what the optimiser produces. *)
  let the_exit = mk EXIT
  let mk_exit () = the_exit

  let let_if stmt =
    match stmt.node with
    | IF (cond_fml, t_stmt, f_stmt) -> (cond_fml, t_stmt, f_stmt)
    | _ -> assert false

  let let_assign stmt =
    match stmt.node with
    | ASSIGN (varname, term, nxt_stmt) -> (varname, term, nxt_stmt)
    | _ -> assert false

  let let_nondet_int_assign stmt =
    match stmt.node with
    | NONDET_INT_ASSIGN (varname, nxt_stmt) -> (varname, nxt_stmt)
    | _ -> assert false

  let let_nondet_real_assign stmt =
    match stmt.node with
    | NONDET_REAL_ASSIGN (varname, nxt_stmt) -> (varname, nxt_stmt)
    | _ -> assert false

  let let_assume stmt =
    match stmt.node with
    | ASSUME (fml, nxt_stmt) -> (fml, nxt_stmt)
    | _ -> assert false

  let let_nondet stmt =
    match stmt.node with
    | NONDET (stmt1, stmt2) -> (stmt1, stmt2)
    | _ -> assert false

  let let_nop stmt = match stmt.node with NOP s -> s | _ -> assert false

  let get_next_statements_ref stmt =
    match stmt.node with
    | ASSIGN (_, _, nxt_stmt) -> [ nxt_stmt ]
    | NONDET_INT_ASSIGN (_, nxt_stmt) -> [ nxt_stmt ]
    | NONDET_REAL_ASSIGN (_, nxt_stmt) -> [ nxt_stmt ]
    | IF (_, t_stmt, f_stmt) -> [ t_stmt; f_stmt ]
    | NONDET (stmt1, stmt2) -> [ stmt1; stmt2 ]
    | ASSUME (_, nxt_stmt) -> [ nxt_stmt ]
    | NOP stmt -> [ stmt ]
    | EXIT -> []

  let get_next_statements stmt =
    get_next_statements_ref stmt |> List.map ~f:(fun stmt' -> !stmt')

  let rec get_all_statements_rep stmt res =
    if List.exists ~f:(fun stmt' -> phys_equal stmt' stmt) res then res
    else
      let res = stmt :: res in
      get_next_statements stmt
      |> List.fold_left
           ~f:(fun res nxt_stmt -> get_all_statements_rep nxt_stmt res)
           ~init:res

  let get_all_statements stmt = get_all_statements_rep stmt [] |> List.rev
  let dummy_stmt = ref (mk_exit ())

  let rec of_statement_rep label_to_stmt nxt_stmt break_nxt_stmt stmt =
    if Statement.is_assign stmt then
      let varname, term = Statement.let_assign stmt in
      mk_assign varname term nxt_stmt
    else if Statement.is_break stmt then
      if phys_equal break_nxt_stmt dummy_stmt then
        raise (Error "break can use only in while loops")
      else mk_nop break_nxt_stmt
    else if Statement.is_compound stmt then
      let stmt1, stmt2 = Statement.let_compound stmt in
      of_statement_rep label_to_stmt
        (ref (of_statement_rep label_to_stmt nxt_stmt break_nxt_stmt stmt2))
        break_nxt_stmt stmt1
    else if Statement.is_exit stmt then mk_exit ()
    else if Statement.is_if stmt then
      let cond_fml, t_stmt, f_stmt = Statement.let_if stmt in
      let t_stmt =
        of_statement_rep label_to_stmt nxt_stmt break_nxt_stmt t_stmt
      in
      let f_stmt =
        of_statement_rep label_to_stmt nxt_stmt break_nxt_stmt f_stmt
      in
      mk_if cond_fml (ref t_stmt) (ref f_stmt)
    else if Statement.is_loop stmt then (
      let first_stmt = ref (mk_exit ()) in
      let body =
        of_statement_rep label_to_stmt first_stmt nxt_stmt
          (Statement.let_loop stmt)
      in
      let body =
        if phys_equal body !first_stmt then (
          first_stmt := mk_nop first_stmt;
          !first_stmt)
        else body
      in
      first_stmt := body;
      body)
    else if Statement.is_nondet stmt then
      let stmt1, stmt2 = Statement.let_nondet stmt in
      let stmt1 =
        of_statement_rep label_to_stmt nxt_stmt break_nxt_stmt stmt1
      in
      let stmt2 =
        of_statement_rep label_to_stmt nxt_stmt break_nxt_stmt stmt2
      in
      mk_nondet (ref stmt1) (ref stmt2)
    else if Statement.is_assume stmt then
      let fml = Statement.let_assume stmt in
      mk_assume fml nxt_stmt
    else if Statement.is_nondet_int_assign stmt then
      let varname = Statement.let_nondet_int_assign stmt in
      mk_nondet_int_assign varname nxt_stmt
    else if Statement.is_nondet_real_assign stmt then
      let varname = Statement.let_nondet_real_assign stmt in
      mk_nondet_real_assign varname nxt_stmt
    else if Statement.is_nop stmt then mk_nop nxt_stmt
    else if Statement.is_label stmt then (
      let label_name = Statement.let_label stmt in
      let stmt = mk_nop nxt_stmt in
      Hashtbl.Poly.find_exn label_to_stmt (label_name, T_int.SInt (*Dummy*))
      := stmt;
      stmt)
    else if Statement.is_goto stmt then
      let label_name = Statement.let_goto stmt in
      Hashtbl.Poly.find_exn label_to_stmt (label_name, T_int.SInt (*Dummy*))
      |> mk_nop
    else if Statement.is_vardecl stmt then (* TODO *)
      mk_nop nxt_stmt
    else
      failwith
      @@ sprintf "LinkedStatement.of_statement_rep: not implemented: %s"
      @@ Statement.string_of stmt

  let of_statement stmt =
    let labels = Statement.get_all_labels stmt in
    let label_to_stmt = Hashtbl.Poly.create ~size:(List.length labels) () in
    let exit_stmt = ref (mk_exit ()) in
    List.iter
      ~f:(fun label ->
        Hashtbl.Poly.add_exn label_to_stmt ~key:label
          ~data:(ref (mk_nop exit_stmt)))
      labels;
    of_statement_rep label_to_stmt exit_stmt exit_stmt stmt

  let rec get_vars_rep get_vars_one stmt (used_stmts, vars) =
    if List.exists ~f:(fun used_stmt -> phys_equal used_stmt stmt) used_stmts
    then (used_stmts, vars)
    else
      let used_stmts = stmt :: used_stmts in
      let vars = get_vars_one stmt |> Variables.union vars in
      get_next_statements stmt
      |> List.fold_left
           ~f:(fun (used_stmts, vars) nxt_stmt ->
             get_vars_rep get_vars_one nxt_stmt (used_stmts, vars))
           ~init:(used_stmts, vars)

  let get_read_vars stmt =
    match stmt.node with
    | IF (fml, _, _) -> Formula.term_sort_env_of fml |> Variables.of_tvarset
    | ASSIGN (_, term, _) -> Term.term_sort_env_of term |> Variables.of_tvarset
    | ASSUME (fml, _) -> Formula.term_sort_env_of fml |> Variables.of_tvarset
    | NONDET_INT_ASSIGN _ | NONDET_REAL_ASSIGN _ | NONDET _ | NOP _ | EXIT ->
        Variables.empty

  let get_written_vars stmt =
    match stmt.node with
    | NONDET_INT_ASSIGN (varname, _) ->
        Variables.of_varname (varname, T_int.SInt)
    | NONDET_REAL_ASSIGN (varname, _) ->
        Variables.of_varname (varname, T_real.SReal)
    | ASSIGN (varname, rhs, _) ->
        Variables.of_varname (varname, Term.sort_of rhs)
    | ASSUME _ | IF _ | NONDET _ | NOP _ | EXIT -> Variables.empty

  let get_used_vars stmt =
    Variables.union (get_read_vars stmt) (get_written_vars stmt)

  let get_read_vars_from stmt =
    let _, vars = get_vars_rep get_read_vars stmt ([], Variables.empty) in
    vars

  let get_written_vars_from stmt =
    let _, vars = get_vars_rep get_written_vars stmt ([], Variables.empty) in
    vars

  let get_used_vars_from stmt =
    let _, vars = get_vars_rep get_used_vars stmt ([], Variables.empty) in
    vars

  let string_of_indent n = String.make n ' '
  let string_of_labelid n = sprintf "L%d" n

  let rec string_of_stmt_rep ?info used indent stmt =
    let id_opt = List.find ~f:(fun (stmt', _) -> phys_equal stmt' stmt) used in
    match id_opt with
    | Some (_, id) ->
        ( used,
          sprintf "%sgoto %s;" (string_of_indent indent) (string_of_labelid id)
        )
    | None ->
        let id = List.length used + 1 in
        let used = (stmt, id) :: used in
        let prefix =
          match info with
          | None ->
              sprintf "%s%s: " (string_of_indent indent) (string_of_labelid id)
          | Some to_s ->
              sprintf "%s: // %s\n%s" (string_of_labelid id) (to_s stmt)
                (string_of_indent indent)
        in
        let used, bodystr =
          match stmt.node with
          | IF (cond_fml, t_stmt, f_stmt) ->
              let used, t_stmt_str =
                string_of_stmt_rep ?info used (indent + 2) !t_stmt
              in
              let used, f_stmt_str =
                string_of_stmt_rep ?info used (indent + 2) !f_stmt
              in
              ( used,
                sprintf "if (%s) {\n%s\n%s}\n%selse {\n%s\n%s}"
                  (Formula.str_of cond_fml) t_stmt_str (string_of_indent indent)
                  (string_of_indent indent) f_stmt_str (string_of_indent indent)
              )
          | ASSIGN (varname, term, nxt_stmt) ->
              let used, nxt_stmt_str =
                string_of_stmt_rep ?info used indent !nxt_stmt
              in
              ( used,
                sprintf "%s = %s;\n%s" varname (Term.str_of term) nxt_stmt_str
              )
          | NONDET_INT_ASSIGN (varname, nxt_stmt) ->
              let used, nxt_stmt_str =
                string_of_stmt_rep ?info used indent !nxt_stmt
              in
              (used, sprintf "%s = nondet_int();\n%s" varname nxt_stmt_str)
          | NONDET_REAL_ASSIGN (varname, nxt_stmt) ->
              let used, nxt_stmt_str =
                string_of_stmt_rep ?info used indent !nxt_stmt
              in
              (used, sprintf "%s = nondet_real();\n%s" varname nxt_stmt_str)
          | NONDET (stmt1, stmt2) ->
              let used, stmt1_str =
                string_of_stmt_rep ?info used (indent + 2) !stmt1
              in
              let used, stmt2_str =
                string_of_stmt_rep ?info used (indent + 2) !stmt2
              in
              ( used,
                sprintf "nondet {\n%s\n%s}\n%selse {\n%s\n%s}" stmt1_str
                  (string_of_indent indent) (string_of_indent indent) stmt2_str
                  (string_of_indent indent) )
          | ASSUME (fml, nxt_stmt) ->
              let used, nxt_stmt_str =
                string_of_stmt_rep ?info used indent !nxt_stmt
              in
              (used, sprintf "assume(%s);\n%s" (Formula.str_of fml) nxt_stmt_str)
          | NOP nxt_stmt ->
              let used, nxt_stmt_str =
                string_of_stmt_rep ?info used indent !nxt_stmt
              in
              (used, sprintf "nop\n%s" nxt_stmt_str)
          | EXIT -> (used, sprintf "exit 0;")
        in
        (used, prefix ^ bodystr)

  let string_of ?info stmt =
    let _, str = string_of_stmt_rep ?info [] 0 stmt in
    str

  let sub tvar term stmt =
    let subst = [ (tvar, term) ] |> Map.Poly.of_alist_exn in
    match stmt.node with
    | IF (cond_fml, t_stmt, f_stmt) ->
        mk_if (Formula.subst subst cond_fml) t_stmt f_stmt
    | ASSIGN (varname, term, nxt_stmt) ->
        mk_assign varname (Term.subst subst term) nxt_stmt
    | NONDET_INT_ASSIGN (varname, nxt_stmt) ->
        mk_nondet_int_assign varname nxt_stmt
    | NONDET_REAL_ASSIGN (varname, nxt_stmt) ->
        mk_nondet_real_assign varname nxt_stmt
    | NONDET (stmt1, stmt2) -> mk_nondet stmt1 stmt2
    | ASSUME (fml, nxt_stmt) -> mk_assume (Formula.subst subst fml) nxt_stmt
    | NOP stmt -> mk_nop stmt
    | EXIT -> mk_exit ()
end

module LinkedStatementHashtbl = Stdlib.Hashtbl.Make (struct
  type t = LinkedStatement.t

  let equal = phys_equal

  (* Hash the identity, never the statement. [Hashtbl.hash] walks the structure,
     and a statement's successor references are assigned to while tables keyed
     by it are alive, so hashing the structure gives a different answer for the
     same key before and after and the lookup silently misses. *)
  let hash stmt = LinkedStatement.id_of stmt
end)
