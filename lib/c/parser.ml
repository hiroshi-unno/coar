(* The C frontend's entry points: read a C program annotated with a CTL
   ([from_cctl_file], [-p cctl]) or LTL ([from_cltl_file], [-p cltl]) property
   and translate it into a muCLP problem whose validity is the property.

   The program is normalised before translation: function calls are inlined
   ([ElimFuncall]; calls inside conditions are first lifted into assignments),
   [#define]s are substituted (on the LTL path textually, by [Preprocess]), and
   on the LTL path local declarations are also renamed apart ([ElimVardecl]),
   returns from [main] become exits and the leading assignments become the
   initial state ([Init.of_stmt]).  The SV-COMP nondeterministic
   value functions are declared as ordinary functions here.  An LTL property is
   negated, turned into a Buchi automaton by the external tool LTL3BA and then
   into a modal equation system; [HesOf] does the rest.

   Syntax and semantic errors are returned as [Error], never raised. *)

open Core
open Common.Ext
open Common.Util
open Common.Combinator
open CSyntax
open Ast
open Ast.LogicOld

let rec sub_inits_rep subst res = function
  | [] -> List.rev res
  | init :: tail ->
      if Init.is_assign init then
        let varname, term = Init.let_assign init in
        let term = Term.subst subst term in
        let tvar = Ident.Tvar varname in
        let subst = Map.Poly.update subst tvar ~f:(fun _ -> term) in
        let init = Init.mk_assign varname term in
        sub_inits_rep subst (init :: res) tail
      else if Init.is_assume init then
        let init =
          Init.let_assume init |> Formula.subst subst |> Init.mk_assume
        in
        sub_inits_rep subst (init :: res) tail
      else if Init.is_nondet_int_assign init then
        let varname = Init.let_nondet_int_assign init in
        let subst = Map.Poly.remove subst (Ident.Tvar varname) in
        sub_inits_rep subst (init :: res) tail
      else if Init.is_nondet_real_assign init then
        let varname = Init.let_nondet_real_assign init in
        let subst = Map.Poly.remove subst (Ident.Tvar varname) in
        sub_inits_rep subst (init :: res) tail
      else assert false

let sub_inits inits = sub_inits_rep Map.Poly.empty [] inits

module ReturnReplacer : sig
  (* val replace_return_int: f:(Term.t -> Statement.t) -> Statement.t -> Statement.t
     val replace_return_nondet: replace_to:Statement.t -> Statement.t -> Statement.t
     val replace_return_void: replace_to:Statement.t -> Statement.t -> Statement.t *)
  val replace_return :
    f:(Statement.t -> Statement.t) -> Statement.t -> Statement.t
end = struct
  let rec replace_return ~f stmt =
    if
      Statement.is_return_int stmt
      || Statement.is_return_real stmt
      || Statement.is_return_void stmt
      || Statement.is_return_nondet_int stmt
      || Statement.is_return_nondet_real stmt
    then f stmt
    else if Statement.is_compound stmt then
      let stmt1, stmt2 = Statement.let_compound stmt in
      Statement.mk_compound (replace_return ~f stmt1) (replace_return ~f stmt2)
    else if Statement.is_if stmt then
      let cond_fml, t_stmt, f_stmt = Statement.let_if stmt in
      Statement.mk_if cond_fml (replace_return ~f t_stmt)
        (replace_return ~f f_stmt)
    else if Statement.is_nondet stmt then
      let stmt1, stmt2 = Statement.let_nondet stmt in
      Statement.mk_nondet (replace_return ~f stmt1) (replace_return ~f stmt2)
    else if Statement.is_loop stmt then
      let stmt' = Statement.let_loop stmt in
      Statement.mk_loop (replace_return ~f stmt')
    else if
      Statement.is_assign stmt
      || Statement.is_unref_assign stmt
      || Statement.is_vardecl stmt
      || Statement.is_call_assign stmt
      || Statement.is_call_voidfun stmt
      || Statement.is_goto stmt || Statement.is_label stmt
      || Statement.is_nondet_int_assign stmt
      || Statement.is_nondet_real_assign stmt
      || Statement.is_assume stmt || Statement.is_break stmt
      || Statement.is_exit stmt || Statement.is_nop stmt
    then stmt
    else assert false
  (* let replace_return_void ~replace_to query =
     replace_return
      ~f:(fun stmt -> if Statement.is_return_void stmt then replace_to else stmt)
      query
     let replace_return_nondet ~replace_to query =
     replace_return
      ~f:(fun stmt -> if Statement.is_return_nondet stmt then replace_to else stmt)
      query
     let replace_return_int ~f query =
     replace_return
      ~f:(fun stmt ->
          if Statement.is_return_int stmt then
            let term = Statement.let_return_int stmt in
            f term
          else stmt)
      query *)
end

module ElimFuncall : sig
  val elim_funcall : FunDecl.t list -> Statement.t -> Statement.t
end = struct
  let mk_labelname funname nxt_label_id =
    (sprintf "%s#%d" funname nxt_label_id, nxt_label_id + 1)

  let subst_terms subst terms = List.map ~f:(Term.subst subst) terms

  (* Inlining is the only treatment of a call, and it unfolds a recursive
     function without end, so a call from which a cycle of calls is reachable
     is refused. *)
  let refuse_recursive funname =
    raise
      (SemanticError
         (sprintf "the call to %s reaches a recursive function, which is not \
                   supported" funname))

  (* TODO: *p = &hoge; *p = q; (elim by optimization) *)
  (* *p = q -> p' = q *)
  let rec unref_ref_stmt_rep from_varname to_varname subst stmt =
    if Statement.is_unref_assign stmt then
      let varname, term = Statement.let_unref_assign stmt in
      let term = Term.subst subst term in
      if String.equal varname from_varname then
        Statement.mk_assign to_varname term
      else Statement.mk_unref_assign varname term
    else if Statement.is_assign stmt then
      (* A pointer parameter stands for its target throughout the body
         (reassigning a pointer is not modelled), so an assignment to it is a
         write through it -- the form an inner call leaves: inlining [g(p)]
         with [void g(int *q) { *q = 1; }] gives [p = 1].  It writes
         [to_varname]; renaming only the reads let [f(&x)] with
         [void f(int *p) { g(p); }] leave [x] unchanged. *)
      let varname, term = Statement.let_assign stmt in
      let varname =
        if String.equal varname from_varname then to_varname else varname
      in
      Statement.mk_assign varname (Term.subst subst term)
    else if Statement.is_assume stmt then
      let fml = Statement.let_assume stmt in
      Statement.mk_assume (Formula.subst subst fml)
    else if Statement.is_call_assign stmt then
      let varname, funname, args = Statement.let_call_assign stmt in
      Statement.mk_call_assign varname funname (subst_terms subst args)
    else if Statement.is_call_voidfun stmt then
      let funname, args = Statement.let_call_voidfun stmt in
      Statement.mk_call_voidfun funname (subst_terms subst args)
    else if Statement.is_compound stmt then
      let stmt1, stmt2 = Statement.let_compound stmt in
      Statement.mk_compound
        (unref_ref_stmt_rep from_varname to_varname subst stmt1)
        (unref_ref_stmt_rep from_varname to_varname subst stmt2)
    else if Statement.is_if stmt then
      let cond_fml, tstmt, fstmt = Statement.let_if stmt in
      Statement.mk_if
        (Formula.subst subst cond_fml)
        (unref_ref_stmt_rep from_varname to_varname subst tstmt)
        (unref_ref_stmt_rep from_varname to_varname subst fstmt)
    else if Statement.is_loop stmt then
      let stmt = Statement.let_loop stmt in
      Statement.mk_loop (unref_ref_stmt_rep from_varname to_varname subst stmt)
    else if Statement.is_nondet stmt then
      let stmt1, stmt2 = Statement.let_nondet stmt in
      Statement.mk_nondet
        (unref_ref_stmt_rep from_varname to_varname subst stmt1)
        (unref_ref_stmt_rep from_varname to_varname subst stmt2)
    else if Statement.is_return_int stmt then
      let term = Statement.let_return_int stmt in
      Statement.mk_return_int (Term.subst subst term)
    else if
      Statement.is_break stmt || Statement.is_exit stmt || Statement.is_nop stmt
      || Statement.is_goto stmt || Statement.is_label stmt
      || Statement.is_return_nondet_int stmt
      || Statement.is_return_nondet_real stmt
      || Statement.is_return_void stmt
      || Statement.is_vardecl stmt
      || Statement.is_nondet_int_assign stmt
      || Statement.is_nondet_real_assign stmt
    then stmt
    else
      failwith
      @@ sprintf "move_funcall_rep: not implemented: %s"
           (Statement.string_of stmt)

  (* [rename_decls ren stmt] renames, in [stmt] read as a function body, the
     variables [ren] maps (name -> new name and sort) from where they are in
     scope, and declarations of the names in [clash] from the declaration to
     the end of its scope (the rest of the sequence, with an [if] branch and a
     loop body each a scope, as the pass that later renames locals apart has
     it).  It returns the renaming in force after [stmt]. *)
  let rec rename_decls clash suffix ren stmt =
    let open Statement in
    let name v = match Map.Poly.find ren v with Some (v', _) -> v' | None -> v in
    let sub =
      Map.Poly.of_alist_exn
      @@ List.map (Map.Poly.to_alist ren) ~f:(fun (v, (v', sort)) ->
          (Ident.Tvar v, Term.mk_var (Ident.Tvar v') sort ~info:Dummy))
    in
    let term = Term.subst sub and fml = Formula.subst sub in
    let scoped stmt = fst (rename_decls clash suffix ren stmt) in
    match stmt with
    | VARDECL (v, sort) when Set.mem clash v ->
        let v' = v ^ suffix in
        (VARDECL (v', sort), Map.Poly.set ren ~key:v ~data:(v', sort))
    | COMPOUND (stmt1, stmt2) ->
        let stmt1, ren = rename_decls clash suffix ren stmt1 in
        let stmt2, ren = rename_decls clash suffix ren stmt2 in
        (COMPOUND (stmt1, stmt2), ren)
    | IF (cond, stmt1, stmt2) -> (IF (fml cond, scoped stmt1, scoped stmt2), ren)
    | NONDET (stmt1, stmt2) -> (NONDET (scoped stmt1, scoped stmt2), ren)
    | LOOP stmt -> (LOOP (scoped stmt), ren)
    | ASSIGN (v, t) -> (ASSIGN (name v, term t), ren)
    | NONDET_INT_ASSIGN v -> (NONDET_INT_ASSIGN (name v), ren)
    | NONDET_REAL_ASSIGN v -> (NONDET_REAL_ASSIGN (name v), ren)
    | UNREF_ASSIGN (v, t) -> (UNREF_ASSIGN (v, term t), ren)
    | ASSUME phi -> (ASSUME (fml phi), ren)
    | CALL_VOIDFUN (f, args) -> (CALL_VOIDFUN (f, List.map args ~f:term), ren)
    | CALL_ASSIGN (v, f, args) ->
        (CALL_ASSIGN (name v, f, List.map args ~f:term), ren)
    | RETURN_INT t -> (RETURN_INT (term t), ren)
    | RETURN_REAL t -> (RETURN_REAL (term t), ren)
    | VARDECL _ | LABEL _ | GOTO _ | RETURN_NONDET_INT | RETURN_NONDET_REAL
    | RETURN_VOID | BREAK | EXIT | NOP ->
        (stmt, ren)

  (*
    void f(int a, int b) { P; }
    f(x, y);

    ->

    while (1) {
      int a = x, b = y;
      P;
      break;
    }
    f#0:
  *)
  let rec mk_inline_funcall nxt_label_id fundecls params args labelname
      return_replaced_funbody =
    let body, nxt_label_id =
      elim_funcall_rep nxt_label_id fundecls return_replaced_funbody
    in
    let zipped = List.zip_exn params args in
    let pa_int =
      List.filter ~f:(fun ((_, sort), _) -> Term.is_int_sort sort) zipped
    in
    let pa_unref =
      List.filter ~f:(fun ((_, sort), _) -> Term.is_int_ref_sort sort) zipped
    in
    assert (List.length pa_int + List.length pa_unref = List.length zipped);
    (* A pointer parameter is inlined by substituting the variable it points
       to for it, and that variable is named as the caller sees it.  A
       parameter or a local of the callee with the same name would capture it:
       [void f(int *p) { int x = 5; *p = 1; }] called as [f(&x)] assigned the
       local [x] and left the caller's unchanged.  Such parameters and
       declarations are therefore first given a name unique to this call site
       (no C identifier contains [#]). *)
    let clash =
      Set.Poly.of_list
      @@ List.map pa_unref ~f:(fun (_, arg) ->
          let (tvar, _), _ = Term.let_var arg in
          Ident.name_of_tvar tvar)
    in
    let suffix = "#in#" ^ labelname in
    let body, pa_int =
      if Set.is_empty clash then (body, pa_int)
      else
        let param_ren =
          List.filter_map pa_int ~f:(fun ((varname, sort), _) ->
              if Set.mem clash varname then
                Some (varname, (varname ^ suffix, sort))
              else None)
        in
        ( fst
          @@ rename_decls clash suffix (Map.Poly.of_alist_exn param_ren) body,
          List.map pa_int ~f:(fun ((varname, sort), arg) ->
              if Set.mem clash varname then ((varname ^ suffix, sort), arg)
              else ((varname, sort), arg)) )
    in
    (* replace "*&p" with "p" *)
    let body =
      List.fold_left ~init:body pa_unref ~f:(fun body ((varname, _), arg) ->
          (* arg = Term.Var (_, T_int.SRefInt, _) *)
          let (tvar, _), _ = Term.let_var arg in
          (* if sort <> T_int.SRefInt then
             failwith @@ sprintf "sort of (param, arg) = (%s, %s) is not T_int.SRefInt" varname (Term.str_of arg); *)
          let subst =
            Map.Poly.of_alist_exn
              [ (Ident.Tvar varname, Term.mk_var tvar T_int.SInt ~info:Dummy) ]
          in
          unref_ref_stmt_rep varname (Ident.name_of_tvar tvar) subst body)
    in
    (* The arguments are evaluated in the caller's scope, all of them before any
       parameter is bound.  The parameters are declared first and assigned one
       by one, and a declaration renames its variable for the rest of the
       inlined body, so an argument naming a variable that is also the name of
       a parameter would read the fresh, uninitialised parameter instead:
       [int f(int x) { return x; }] called as [f(x)] returned an arbitrary
       value, and [g(b, a)] with parameters [a, b] passed [b] twice.  When an
       argument mentions a parameter's name, every argument is therefore first
       copied into a temporary named after this call site (unique, since the
       label is), and the parameters are bound from the temporaries.  Calls
       with no such clash keep the direct binding, which is the same thing. *)
    let param_names = List.map pa_int ~f:(fun ((varname, _), _) -> varname) in
    let captured =
      List.exists pa_int ~f:(fun (_, arg) ->
          Set.exists (Term.tvs_of arg) ~f:(fun tvar ->
              List.mem param_names (Ident.name_of_tvar tvar)
                ~equal:String.equal))
    in
    let arg_temps, pa_int =
      if not captured then ([], pa_int)
      else
        List.unzip
        @@ List.mapi pa_int ~f:(fun i (param, arg) ->
            let tmp = sprintf "%s#arg%d" labelname i in
            ( Statement.mk_assign tmp arg,
              (param, Term.mk_var (Ident.Tvar tmp) T_int.SInt ~info:Dummy) ))
    in
    ( Statement.mk_compound
        (arg_temps
        @ List.map
            ~f:(fun ((varname, _), _) -> Statement.mk_vardecl varname T_int.SInt)
            pa_int
        @ List.map
            ~f:(fun ((varname, _), arg) -> Statement.mk_assign varname arg)
            pa_int
        @ [ body; Statement.mk_break () ]
        |> Statement.of_statements |> Statement.mk_loop)
        (Statement.mk_label labelname),
      nxt_label_id )

  and elim_funcall_rep nxt_label_id fundecls stmt =
    if Statement.is_call_assign stmt then
      let varname, funname, args = Statement.let_call_assign stmt in
      let fundecl =
        FunDecl.rename_labels
        @@ FunDecl.find_fundecl (funname, T_int.SInt (*Dummy*)) fundecls
      in
      if FunDecl.is_fun_nondet_int fundecl then
        (Statement.mk_nondet_int_assign varname, nxt_label_id)
      else if FunDecl.is_fun_nondet_real fundecl then
        (Statement.mk_nondet_real_assign varname, nxt_label_id)
      else if FunDecl.is_fun_int fundecl then
        let _, params, body = FunDecl.let_fun_int fundecl in
        let labelname, nxt_label_id = mk_labelname funname nxt_label_id in
        if FunDecl.is_non_recursive fundecls fundecl then
          ReturnReplacer.replace_return
            ~f:(fun stmt ->
              if Statement.is_return_int stmt then
                let term = Statement.let_return_int stmt in
                Statement.mk_compound
                  (Statement.mk_assign varname term)
                  (Statement.mk_goto labelname)
              else if Statement.is_return_nondet_int stmt then
                Statement.mk_compound
                  (Statement.mk_nondet_int_assign varname)
                  (Statement.mk_goto labelname)
              else assert false)
            (* append 'return nondet();' if it's missing *)
            (Statement.mk_compound body (Statement.mk_return_nondet_int ()))
          |> mk_inline_funcall nxt_label_id fundecls params args labelname
        else refuse_recursive funname
      else if FunDecl.is_fun_real fundecl then
        let _, params, body = FunDecl.let_fun_real fundecl in
        let labelname, nxt_label_id = mk_labelname funname nxt_label_id in
        if FunDecl.is_non_recursive fundecls fundecl then
          ReturnReplacer.replace_return
            ~f:(fun stmt ->
              if Statement.is_return_real stmt then
                let term = Statement.let_return_real stmt in
                Statement.mk_compound
                  (Statement.mk_assign varname term)
                  (Statement.mk_goto labelname)
              else if Statement.is_return_nondet_real stmt then
                Statement.mk_compound
                  (Statement.mk_nondet_real_assign varname)
                  (Statement.mk_goto labelname)
              else assert false)
            (* append 'return nondet();' if it's missing *)
            (Statement.mk_compound body (Statement.mk_return_nondet_real ()))
          |> mk_inline_funcall nxt_label_id fundecls params args labelname
        else refuse_recursive funname
      else assert false
    else if Statement.is_call_voidfun stmt then
      let funname, args = Statement.let_call_voidfun stmt in
      let fundecl =
        FunDecl.rename_labels
        @@ FunDecl.find_fundecl (funname, T_int.SInt (*Dummy*)) fundecls
      in
      let _, params, body = FunDecl.let_fun fundecl in
      if Statement.is_nop body then (body, nxt_label_id)
      else
        let labelname, nxt_label_id = mk_labelname funname nxt_label_id in
        if FunDecl.is_non_recursive fundecls fundecl then
          ReturnReplacer.replace_return
            ~f:(fun _ -> Statement.mk_goto labelname)
            body
          |> mk_inline_funcall nxt_label_id fundecls params args labelname
        else refuse_recursive funname
    else if Statement.is_if stmt then
      let cond_fml, t_stmt, f_stmt = Statement.let_if stmt in
      let t_stmt, nxt_label_id =
        elim_funcall_rep nxt_label_id fundecls t_stmt
      in
      let f_stmt, nxt_label_id =
        elim_funcall_rep nxt_label_id fundecls f_stmt
      in
      (Statement.mk_if cond_fml t_stmt f_stmt, nxt_label_id)
    else if Statement.is_nondet stmt then
      let stmt1, stmt2 = Statement.let_nondet stmt in
      let stmt1, nxt_label_id = elim_funcall_rep nxt_label_id fundecls stmt1 in
      let stmt2, nxt_label_id = elim_funcall_rep nxt_label_id fundecls stmt2 in
      (Statement.mk_nondet stmt1 stmt2, nxt_label_id)
    else if Statement.is_compound stmt then
      let stmt1, stmt2 = Statement.let_compound stmt in
      let stmt1, nxt_label_id = elim_funcall_rep nxt_label_id fundecls stmt1 in
      let stmt2, nxt_label_id = elim_funcall_rep nxt_label_id fundecls stmt2 in
      (Statement.mk_compound stmt1 stmt2, nxt_label_id)
    else if Statement.is_loop stmt then
      let stmt' = Statement.let_loop stmt in
      let stmt', nxt_label_id = elim_funcall_rep nxt_label_id fundecls stmt' in
      (Statement.mk_loop stmt', nxt_label_id)
    else if
      Statement.is_assign stmt
      || Statement.is_unref_assign stmt
      || Statement.is_vardecl stmt || Statement.is_goto stmt
      || Statement.is_label stmt
      || Statement.is_nondet_int_assign stmt
      || Statement.is_nondet_real_assign stmt
      || Statement.is_assume stmt || Statement.is_break stmt
      || Statement.is_exit stmt || Statement.is_nop stmt
      || Statement.is_return_int stmt
      || Statement.is_return_real stmt
      || Statement.is_return_nondet_int stmt
      || Statement.is_return_nondet_real stmt
      || Statement.is_return_void stmt
    then (stmt, nxt_label_id)
    else
      failwith
      @@ sprintf "elim_funcall_rep: not implemented for: %s"
           (Statement.string_of stmt)

  let move_funcall_tvar_of_count count =
    (Ident.Tvar (sprintf "#result%d" count), count + 1)

  let rec move_funcall_term_rep ?(gen = Fn.id) count term :
      Term.t * (Statement.t -> Statement.t) * int =
    if Term.is_app term then
      let fsym, args, info = Term.let_app term in
      let args, gen, count = move_funcall_terms ~gen count args in
      match fsym with
      | FunCall funname ->
          let tvar, count = move_funcall_tvar_of_count count in
          let gen stmt =
            Statement.mk_compound
              (Statement.mk_call_assign (Ident.name_of_tvar tvar) funname args)
              (gen stmt)
          in
          (Term.mk_var tvar T_int.SInt ~info:Dummy, gen, count)
      | fsym -> (Term.mk_fsym_app fsym args ~info, gen, count)
    else if Term.is_var term then (term, gen, count)
    else
      failwith
      @@ sprintf "move_funcall_term_rep: not implemented: %s" (Term.str_of term)

  and move_funcall_terms ?(gen = Fn.id) count terms =
    List.fold_left ~init:([], gen, count) (List.rev terms)
      ~f:(fun (terms, gen, count) term ->
        let term, gen, count = move_funcall_term_rep ~gen count term in
        (term :: terms, gen, count))

  let move_funcall_atom_rep ?(gen = Fn.id) count atom :
      Atom.t * (Statement.t -> Statement.t) * int =
    if Atom.is_psym_app atom then
      let psym, args, info = Atom.let_psym_app atom in
      let args, gen, count = move_funcall_terms ~gen count args in
      (Atom.mk_app (Predicate.mk_psym psym) args ~info, gen, count)
    else if Atom.is_true atom || Atom.is_false atom then (atom, gen, count)
    else
      failwith
      @@ sprintf "move_funcall_atom_rep: not implemented: %s" (Atom.str_of atom)

  let rec move_funcall_formula_rep ?(gen = Fn.id) count fml :
      Formula.t * (Statement.t -> Statement.t) * int =
    if Formula.is_atom fml then
      let atom, info = Formula.let_atom fml in
      let atom, gen, count = move_funcall_atom_rep ~gen count atom in
      (Formula.mk_atom atom ~info, gen, count)
    else if Formula.is_binop fml then
      let binop, fml1, fml2, info = Formula.let_binop fml in
      let fml1, gen, count = move_funcall_formula_rep ~gen count fml1 in
      let fml2, gen, count = move_funcall_formula_rep ~gen count fml2 in
      (Formula.mk_binop binop fml1 fml2 ~info, gen, count)
    else if Formula.is_unop fml then
      let unop, fml, info = Formula.let_unop fml in
      let fml, gen, count = move_funcall_formula_rep ~gen count fml in
      (Formula.mk_unop unop fml ~info, gen, count)
    else
      failwith
      @@ sprintf "move_funcall_formula_rep: not implemented %s"
           (Formula.str_of fml)

  (* A call that may change the state or block: anything but a
     [__VERIFIER_nondet_*] draw.  A draw has no side effect and its range
     assumption is always satisfiable, so evaluating one that C would have
     skipped changes no run's observable states. *)
  let rec term_has_effectful_call term =
    if Term.is_app term then
      let fsym, args, _ = Term.let_app term in
      (match fsym with
      | FunCall funname ->
          not (String.is_prefix funname ~prefix:"__VERIFIER_nondet_")
      | _ -> false)
      || List.exists args ~f:term_has_effectful_call
    else false

  let rec formula_has_effectful_call fml =
    if Formula.is_atom fml then
      let atom, _ = Formula.let_atom fml in
      Atom.is_psym_app atom
      &&
      let _, args, _ = Atom.let_psym_app atom in
      List.exists args ~f:term_has_effectful_call
    else if Formula.is_binop fml then
      let _, fml1, fml2, _ = Formula.let_binop fml in
      formula_has_effectful_call fml1 || formula_has_effectful_call fml2
    else if Formula.is_unop fml then
      let _, fml, _ = Formula.let_unop fml in
      formula_has_effectful_call fml
    else false

  (* [&&] and [||] evaluate their right operand only when the left one does not
     decide the result.  Lifting every call out of a condition and placing it
     before the statement evaluates them all, so [x == 0 || --x == 5]
     decremented [x] even when [x] was 0, and the left operand then read the
     decremented value.  [short_circuit fml] returns statements that evaluate
     [fml] in C's order and a formula equivalent to [fml] after them in which
     no effectful call sits in a right operand of [&&]/[||]: such an operand is
     evaluated under an [if] on the left one, its outcome stored in a fresh
     0/1 flag [#scN], and the flag stands for the operator.  A condition with
     no effectful call in a right operand comes back unchanged with no
     statements, so the translation of every other program is untouched. *)
  let rec short_circuit count fml : Statement.t list * Formula.t * int =
    if Formula.is_binop fml then
      let binop, fml1, fml2, info = Formula.let_binop fml in
      let pre1, fml1, count = short_circuit count fml1 in
      match binop with
      | (Formula.And | Formula.Or) when formula_has_effectful_call fml2 ->
          let flag = sprintf "#sc%d" count in
          let pre2, fml2, count = short_circuit (count + 1) fml2 in
          let set b =
            Statement.mk_assign flag
              (if b then T_int.one () else T_int.zero ())
          in
          let eval_rhs =
            Statement.of_statements
              (pre2 @ [ Statement.mk_if fml2 (set true) (set false) ])
          in
          let stmt =
            match binop with
            | Formula.And -> Statement.mk_if fml1 eval_rhs (set false)
            | _ -> Statement.mk_if fml1 (set true) eval_rhs
          in
          ( pre1 @ [ stmt ],
            formula_of_term
              (Term.mk_var (Ident.Tvar flag) T_int.SInt ~info:Dummy),
            count )
      | _ ->
          let pre2, fml2, count = short_circuit count fml2 in
          (pre1 @ pre2, Formula.mk_binop binop fml1 fml2 ~info, count)
    else if Formula.is_unop fml then
      let unop, fml, info = Formula.let_unop fml in
      let pre, fml, count = short_circuit count fml in
      (pre, Formula.mk_unop unop fml ~info, count)
    else ([], fml, count)

  let rec move_funcall_rep stmt =
    if Statement.is_assign stmt then
      let varname, term = Statement.let_assign stmt in
      let term, gen, _ = move_funcall_term_rep 0 term in
      Statement.mk_assign varname term |> gen
    else if Statement.is_unref_assign stmt then
      let varname, term = Statement.let_unref_assign stmt in
      let term, gen, _ = move_funcall_term_rep 0 term in
      Statement.mk_unref_assign varname term |> gen
    else if Statement.is_assume stmt then
      let pre, fml, _ = short_circuit 0 (Statement.let_assume stmt) in
      let fml, gen, _ = move_funcall_formula_rep 0 fml in
      Statement.of_statements
        (List.map pre ~f:move_funcall_rep @ [ Statement.mk_assume fml |> gen ])
    else if Statement.is_call_assign stmt then
      let varname, funname, args = Statement.let_call_assign stmt in
      let args, gen, _ = move_funcall_terms 0 args in
      Statement.mk_call_assign varname funname args |> gen
    else if Statement.is_call_voidfun stmt then
      let funname, args = Statement.let_call_voidfun stmt in
      let args, gen, _ = move_funcall_terms 0 args in
      Statement.mk_call_voidfun funname args |> gen
    else if Statement.is_compound stmt then
      let stmt1, stmt2 = Statement.let_compound stmt in
      Statement.mk_compound (move_funcall_rep stmt1) (move_funcall_rep stmt2)
    else if Statement.is_if stmt then
      let cond_fml, tstmt, fstmt = Statement.let_if stmt in
      let pre, cond_fml, _ = short_circuit 0 cond_fml in
      let cond_fml, gen, _ = move_funcall_formula_rep 0 cond_fml in
      Statement.of_statements
        (List.map pre ~f:move_funcall_rep
        @ [
            Statement.mk_if cond_fml (move_funcall_rep tstmt)
              (move_funcall_rep fstmt)
            |> gen;
          ])
    else if Statement.is_loop stmt then
      let stmt = Statement.let_loop stmt in
      Statement.mk_loop (move_funcall_rep stmt)
    else if Statement.is_nondet stmt then
      let stmt1, stmt2 = Statement.let_nondet stmt in
      Statement.mk_nondet (move_funcall_rep stmt1) (move_funcall_rep stmt2)
    else if Statement.is_return_int stmt then
      let term = Statement.let_return_int stmt in
      let term, gen, _ = move_funcall_term_rep 0 term in
      Statement.mk_return_int term |> gen
    else if
      Statement.is_break stmt || Statement.is_exit stmt || Statement.is_nop stmt
      || Statement.is_goto stmt || Statement.is_label stmt
      || Statement.is_return_nondet_int stmt
      || Statement.is_return_nondet_real stmt
      || Statement.is_return_void stmt
      || Statement.is_vardecl stmt
      || Statement.is_nondet_int_assign stmt
      || Statement.is_nondet_real_assign stmt
    then stmt
    else
      failwith
      @@ sprintf "move_funcall_rep: not implemented: %s"
           (Statement.string_of stmt)

  let move_funcall_fundecl fundecl =
    if FunDecl.is_fun_int fundecl then
      let funname, args, body = FunDecl.let_fun_int fundecl in
      FunDecl.mk_fun_int funname args (move_funcall_rep body)
    else if FunDecl.is_fun_real fundecl then
      let funname, args, body = FunDecl.let_fun_real fundecl in
      FunDecl.mk_fun_real funname args (move_funcall_rep body)
    else if FunDecl.is_fun_void fundecl then
      let funname, args, body = FunDecl.let_fun_void fundecl in
      FunDecl.mk_fun_void funname args (move_funcall_rep body)
    else if FunDecl.is_fun_nondet_int fundecl then fundecl
    else if FunDecl.is_fun_nondet_real fundecl then fundecl
    else failwith "unknown fundecl"

  let elim_funcall fundecls stmt =
    let stmt = move_funcall_rep stmt in
    let fundecls = List.map ~f:move_funcall_fundecl fundecls in
    let res, _ = elim_funcall_rep 0 fundecls stmt in
    res
end

module ElimVardecl : sig
  val elim_vardecl :
    Statement.t -> Statement.t * (Ident.tvar, Term.t) Map.Poly.t
  (** [elim_vardecl body] renames every declared variable of [body] apart and
      drops the declarations.  It also returns the renaming in force at the end
      of [body]'s outermost sequence, which maps each name that sequence itself
      declares (not one declared under a branch or a loop, so not a local of an
      inlined call, whose body is a loop) to the variable it became; a name
      declared there twice maps to the later one. *)
end = struct
  let rename renamed_vars varname =
    match Map.Poly.find renamed_vars (Ident.Tvar varname) with
    | Some term ->
        let (tvar, _), _ = Term.let_var term in
        Ident.name_of_tvar tvar
    | None -> varname

  (* the key recording that a generated name is in use; no C identifier
     starts with [#], so it never substitutes anything *)
  let live_prefix = "#live#"
  let live_key name = Ident.Tvar (live_prefix ^ name)

  let is_live_key tvar =
    String.is_prefix (Ident.name_of_tvar tvar) ~prefix:live_prefix

  let rename_term renamed_vars term = Term.subst renamed_vars term
  let rename_formula renamed_vars formula = Formula.subst renamed_vars formula

  let rec elim_vardecl_rep renamed_vars stmt =
    if Statement.is_call_assign stmt then
      let varname, funname, args = Statement.let_call_assign stmt in
      ( Statement.mk_call_assign
          (rename renamed_vars varname)
          funname
          (List.map args ~f:(rename_term renamed_vars)),
        renamed_vars )
    else if Statement.is_call_voidfun stmt then
      let funname, args = Statement.let_call_voidfun stmt in
      ( Statement.mk_call_voidfun funname
          (List.map args ~f:(rename_term renamed_vars)),
        renamed_vars )
    else if Statement.is_if stmt then
      let cond_fml, t_stmt, f_stmt = Statement.let_if stmt in
      let t_stmt', _ = elim_vardecl_rep renamed_vars t_stmt in
      let f_stmt', _ = elim_vardecl_rep renamed_vars f_stmt in
      ( Statement.mk_if (rename_formula renamed_vars cond_fml) t_stmt' f_stmt',
        renamed_vars )
    else if Statement.is_nondet stmt then
      let stmt1, stmt2 = Statement.let_nondet stmt in
      let stmt1', _ = elim_vardecl_rep renamed_vars stmt1 in
      let stmt2', _ = elim_vardecl_rep renamed_vars stmt2 in
      (Statement.mk_nondet stmt1' stmt2', renamed_vars)
    else if Statement.is_compound stmt then
      let stmt1, stmt2 = Statement.let_compound stmt in
      let stmt1', renamed_vars = elim_vardecl_rep renamed_vars stmt1 in
      let stmt2', renamed_vars = elim_vardecl_rep renamed_vars stmt2 in
      (Statement.mk_compound stmt1' stmt2', renamed_vars)
    else if Statement.is_loop stmt then
      let inner_stmt = Statement.let_loop stmt in
      let inner_stmt', _ = elim_vardecl_rep renamed_vars inner_stmt in
      (Statement.mk_loop inner_stmt', renamed_vars)
    else if Statement.is_assign stmt then
      let varname, term = Statement.let_assign stmt in
      ( Statement.mk_assign
          (rename renamed_vars varname)
          (rename_term renamed_vars term),
        renamed_vars )
    else if Statement.is_nondet_int_assign stmt then
      let varname = Statement.let_nondet_int_assign stmt in
      ( Statement.mk_nondet_int_assign (rename renamed_vars varname),
        renamed_vars )
    else if Statement.is_nondet_real_assign stmt then
      let varname = Statement.let_nondet_real_assign stmt in
      ( Statement.mk_nondet_real_assign (rename renamed_vars varname),
        renamed_vars )
    else if Statement.is_assume stmt then
      let fml = Statement.let_assume stmt in
      (Statement.mk_assume (rename_formula renamed_vars fml), renamed_vars)
    else if Statement.is_vardecl stmt then
      let varname, sort = Statement.let_vardecl stmt in
      (* The new name must not be one a variable of an enclosing scope already
         carries, shadowed or not.  The index is the number of names renamed,
         which does not grow when a declaration shadows a name already
         renamed, so a third nested [int a] got the name of the second and
         overwrote it.  Every name given out is therefore also recorded under
         a [live_key] (dropped with the rest of the scope's renaming when the
         scope ends), and the index is advanced past those; where there is no
         clash the name is the one the count alone gives. *)
      let real_keys =
        Map.Poly.counti renamed_vars ~f:(fun ~key ~data:_ ->
            not (is_live_key key))
      in
      let rec fresh i =
        let name = sprintf "%s#%d" varname i in
        if Map.Poly.mem renamed_vars (live_key name) then fresh (i + 1)
        else name
      in
      let new_varname = fresh real_keys in
      let renamed_vars =
        Map.Poly.set renamed_vars ~key:(live_key new_varname)
          ~data:(Term.mk_var (Ident.Tvar new_varname) sort ~info:Dummy)
      in
      ( (if Term.is_int_sort sort then Statement.mk_nondet_int_assign new_varname
         else Statement.mk_nondet_real_assign new_varname),
        Map.Poly.update renamed_vars (Ident.Tvar varname) ~f:(fun _ ->
            Term.mk_var (Ident.Tvar new_varname) sort ~info:Dummy) )
    else if Statement.is_return_int stmt then
      let term = Statement.let_return_int stmt in
      (Statement.mk_return_int (rename_term renamed_vars term), renamed_vars)
    else if Statement.is_return_real stmt then
      let term = Statement.let_return_real stmt in
      (Statement.mk_return_real (rename_term renamed_vars term), renamed_vars)
    else if
      Statement.is_goto stmt || Statement.is_label stmt
      || Statement.is_break stmt || Statement.is_exit stmt
      || Statement.is_nop stmt
      (* main's own returns are still here: they become exits only after this
         pass, and a [return;] in a [void main] was refused *)
      || Statement.is_return_void stmt
      || Statement.is_return_nondet_int stmt
      || Statement.is_return_nondet_real stmt
    then (stmt, renamed_vars)
    else
      failwith
      @@ sprintf "elim_vardecl_rep: not implemented: %s"
           (Statement.string_of stmt)

  let elim_vardecl stmt =
    let stmt, renamed_vars = elim_vardecl_rep Map.Poly.empty stmt in
    (stmt, Map.Poly.filter_keys renamed_vars ~f:(Fn.non is_live_key))
end

(* [__VERIFIER_nondet_<type>()] as a function whose result is bounded by the
   width of <type> *)
let nondet_int_fun name bits signed =
  let r = "#nondet_" ^ name in
  FunDecl.mk_fun_int name []
    (Statement.of_statements
       [
         Statement.mk_vardecl r T_int.SInt;
         Statement.mk_nondet_int_assign r;
         Statement.mk_assume (nondet_range r bits signed);
         Statement.mk_return_int
           (Term.mk_var (Ident.Tvar r) T_int.SInt ~info:Dummy);
       ])

let warn_unsigned ~print =
  if !unsigned_seen then
    print
    @@ lazy
         "[warning] `unsigned` is treated as a mathematical integer: no \
          wrap-around modulo 2^w is modelled"

(* [havoc_cctl_inits inits] gives each draw [x = nondet();] of a CTL [init()]
   its meaning in the initial state.  The initial state is read with every
   variable that [init] leaves open bound universally, so a draw of a variable
   no earlier entry mentions is that variable's own initial value and is
   dropped.  A draw of a variable an earlier entry assigned or read makes a
   value of its own: it becomes an assignment of a fresh variable (no C
   identifier contains [#]), so that [x = 1; x = nondet();] leaves [x] open
   and [y = x; x = nondet();] does not tie [y] to the new [x].
   Postcondition: the result has no draw. *)
let havoc_cctl_inits inits =
  let mentioned = function
    | Init.ASSIGN (v, t) ->
        Set.add (Set.Poly.map ~f:Ident.name_of_tvar (Term.tvs_of t)) v
    | Init.ASSUME fml -> Set.Poly.map ~f:Ident.name_of_tvar (Formula.tvs_of fml)
    | Init.NONDET_INT_ASSIGN v | Init.NONDET_REAL_ASSIGN v -> Set.Poly.singleton v
  in
  List.foldi inits ~init:(Set.Poly.empty, []) ~f:(fun i (seen, res) init ->
      let res =
        match init with
        | Init.NONDET_INT_ASSIGN v | Init.NONDET_REAL_ASSIGN v ->
            if Set.mem seen v then
              let sort =
                match init with
                | Init.NONDET_REAL_ASSIGN _ -> T_real.SReal
                | _ -> T_int.SInt
              in
              Init.mk_assign v
                (Term.mk_var (Ident.Tvar (sprintf "%s#init%d" v i)) sort)
              :: res
            else res
        | _ -> init :: res
      in
      (Set.union seen (mentioned init), res))
  |> snd |> List.rev

(* Cook and Koskinen's CTL benchmarks (Reasoning about nondeterminism in
   programs, PLDI 2013, Section 5.2) make every nondeterministic choice
   explicit as a "rho" variable: [if (read()) C1 else C2] becomes
   [rho := *; if (rho > 0) C1 else C2], and [x := read()] becomes
   [rho := *; x := rho].  Their C files keep the reads of [__rho_<k>_] and
   drop the assignment, leaving a name that nothing declares or assigns.  Read
   as a global, such a name would be one value fixed by the initial state, a
   single choice for the whole run, which is not what the program means: a
   loop testing it could never take both branches.  So each statement that
   reads such a name is preceded by a fresh draw of it.
   Assumes: [body] has no [UNREF_ASSIGN] (pointer writes are not in this
   dialect) and its calls are inlined; [inits] is [init()] as written, before
   [havoc_cctl_inits] drops its first draws (a name drawn once there is one
   choice read in several places, as [__rho_666_] in the OS fragment 4
   programs).  Guarantees: a [__rho_] name that is declared, assigned
   anywhere, or drawn or assigned in [inits] is left alone, and no other name
   is touched. *)
let draw_rho_placeholders decls inits body =
  let declared =
    List.map decls ~f:(function Declare.INT v | Declare.REAL v -> v)
  in
  let rec assigned acc = function
    | Statement.ASSIGN (v, _)
    | Statement.NONDET_INT_ASSIGN v
    | Statement.NONDET_REAL_ASSIGN v
    | Statement.UNREF_ASSIGN (v, _)
    | Statement.CALL_ASSIGN (v, _, _) ->
        v :: acc
    | Statement.IF (_, s1, s2)
    | Statement.NONDET (s1, s2)
    | Statement.COMPOUND (s1, s2) ->
        assigned (assigned acc s1) s2
    | Statement.LOOP s -> assigned acc s
    | _ -> acc
  in
  let written =
    assigned
      (List.filter_map inits ~f:(function
        | Init.ASSIGN (v, _) | Init.NONDET_INT_ASSIGN v | Init.NONDET_REAL_ASSIGN v
          ->
            Some v
        | Init.ASSUME _ -> None))
      body
  in
  let is_placeholder v =
    String.is_prefix v ~prefix:"__rho_"
    && (not (List.mem declared v ~equal:String.equal))
    && not (List.mem written v ~equal:String.equal)
  in
  let with_draws vars stmt =
    Variables.to_list vars
    |> List.filter_map ~f:(fun (v, _) ->
           if is_placeholder v then Some (Statement.mk_nondet_int_assign v)
           else None)
    |> List.fold_right ~init:stmt ~f:Statement.mk_compound
  in
  let rec go = function
    | Statement.IF (cond, s1, s2) ->
        with_draws
          (Formula.term_sort_env_of cond |> Variables.of_tvarset)
          (Statement.IF (cond, go s1, go s2))
    | Statement.LOOP s -> Statement.LOOP (go s)
    | Statement.NONDET (s1, s2) -> Statement.NONDET (go s1, go s2)
    | Statement.COMPOUND (s1, s2) -> Statement.COMPOUND (go s1, go s2)
    | ( Statement.ASSIGN _ | Statement.ASSUME _ | Statement.CALL_VOIDFUN _
      | Statement.CALL_ASSIGN _ | Statement.RETURN_INT _
      | Statement.RETURN_REAL _ ) as s ->
        with_draws (Statement.get_read_vars s) s
    | s -> s
  in
  go body

let parse_cctl_from_lexbuf ~print lexbuf =
  try
    unsigned_seen := false;
    let (phi, decls, inits, body), defs, fundecls =
      CCtlParser.toplevel CCtlLexer.main lexbuf
    in
    warn_unsigned ~print;
    (* the draws of [init()] as written: [havoc_cctl_inits] removes a first
       draw, which [draw_rho_placeholders] must still see as an assignment *)
    let written_inits = inits in
    let inits = havoc_cctl_inits inits in
    (* a = 3; b = a; -> a = 3; b = 3; *)
    let inits = sub_inits inits in
    let def_subst = Define.subst_of_defines defs in
    (* A #define replaces its name everywhere in the file, the property and
       the helper functions' bodies included: left in the property, the name
       was a free variable, so [CAP(x == MAX)] was asked of every value of
       [MAX]. *)
    let phi = Ctl.subst def_subst phi in
    (* dispose #define for inits *)
    let inits = List.map ~f:(Init.subst def_subst) inits in
    (* elim all fun callings *)
    let body = ElimFuncall.elim_funcall fundecls body in
    (* An inlined helper's parameters and locals are declared in the inlined
       body; renaming them apart keeps them from being the global of the same
       name, which every declaration otherwise was, read as a no-op: [f(5)]
       with [void f(int x) { x = x + 1; }] assigned the global [x]. *)
    let body, _ = ElimVardecl.elim_vardecl body in
    (* dispose #define for body, the inlined bodies included (after the
       declarations are gone: [Statement.subst] does not take one) *)
    let body = Statement.subst def_subst body in
    (* a return left after inlining is one of body or main: the run ends *)
    let body =
      ReturnReplacer.replace_return ~f:(fun _ -> Statement.mk_exit ()) body
    in
    let body = draw_rho_placeholders decls written_inits body in
    print @@ lazy "vvvvvvvvvvvvv Input C Program vvvvvvvvvvvvv";
    print @@ lazy (sprintf "[phi]\n%s\n" (Ctl.string_of phi));
    print
    @@ lazy
         (sprintf "[decls]\n%s\n"
            (String.concat_map_list ~sep:"\n" decls ~f:Declare.string_of));
    print
    @@ lazy
         (sprintf "[inits]\n%s\n"
            (String.concat_map_list ~sep:"\n" inits ~f:Init.string_of));
    print @@ lazy (sprintf "[body]\n%s\n" (Statement.string_of body));
    print @@ lazy "";
    Ok (HesOf.hes_of_cctl ~print (phi, decls, inits, body))
  with
  | CSyntax.SemanticError error ->
      Result.fail (Error.of_string (sprintf "semantic error: %s" error))
  | CSyntax.SyntaxError error ->
      Result.fail
        (Error.of_string
           (sprintf "%s: syntax error: %s"
              (LexingHelper.get_position_string lexbuf)
              error))
  | CCtlParser.Error ->
      Result.fail
        (Error.of_string
           (sprintf "%s: syntax error"
              (LexingHelper.get_position_string lexbuf)))
  | CCtlLexer.SyntaxError error ->
      Result.fail
        (Error.of_string
           (sprintf "%s: syntax error: %s"
              (LexingHelper.get_position_string lexbuf)
              error))
  | CCtlLexer.ErrorFormatted error -> Result.fail (Error.of_string error)

let parse_cltl_from_lexbuf ~print lexbuf =
  try
    unsigned_seen := false;
    let (ltl, decls, inits, body), property_locals, defs, fundecls =
      CLtlParser.toplevel CLtlLexer.main lexbuf
    in
    warn_unsigned ~print;
    let fundecls =
      [
        FunDecl.mk_fun_int "#dec"
          [ ("x", T_int.SRefInt) ]
          (let tvar = Ident.Tvar "x" in
           Statement.of_statements
             [
               (* *x = x-1 *)
               Statement.mk_unref_assign "x"
                 (T_int.mk_sub
                    (Term.mk_var tvar T_int.SUnrefInt ~info:Dummy)
                    (T_int.mk_int Z.one ~info:Dummy)
                    ~info:Dummy);
               (* return *x *)
               Statement.mk_return_int
                 (Term.mk_var tvar T_int.SUnrefInt ~info:Dummy);
             ]);
        FunDecl.mk_fun_int "#inc"
          [ ("x", T_int.SRefInt) ]
          (let tvar = Ident.Tvar "x" in
           Statement.of_statements
             [
               (* *x = x+1 *)
               Statement.mk_unref_assign "x"
                 (T_int.mk_add
                    (Term.mk_var tvar T_int.SUnrefInt ~info:Dummy)
                    (T_int.mk_int Z.one ~info:Dummy)
                    ~info:Dummy);
               (* return *x *)
               Statement.mk_return_int
                 (Term.mk_var tvar T_int.SUnrefInt ~info:Dummy);
             ]);
        (* a bool draw is 0 or 1; without this declaration a call anywhere but
           the whole right-hand side of an assignment was refused *)
        nondet_int_fun funname_nondet_bool 1 false;
        nondet_int_fun funname_nondet_char 8 true;
        nondet_int_fun funname_nondet_uchar 8 false;
        nondet_int_fun funname_nondet_short 16 true;
        nondet_int_fun funname_nondet_ushort 16 false;
        nondet_int_fun funname_nondet_int 32 true;
        nondet_int_fun funname_nondet_uint 32 false;
        nondet_int_fun funname_nondet_long 64 true;
        nondet_int_fun funname_nondet_ulong 64 false;
        FunDecl.mk_fun_real funname_nondet_float []
          (Statement.mk_return_nondet_real ());
        FunDecl.mk_fun_real funname_nondet_double []
          (Statement.mk_return_nondet_real ());
      ]
      @ fundecls
    in
    let def_subst = Define.subst_of_defines defs in
    (* elim all fun callings *)
    let body = ElimFuncall.elim_funcall fundecls body in
    (* rename local variables to elim Statement.VARDECL *)
    let body, outer_renaming = ElimVardecl.elim_vardecl body in
    (* A property naming a local of main's outermost block (and no global)
       means the variable that local was renamed to; without this the name
       would match nothing the program assigns.  The renaming at the end of
       main's outermost sequence holds every such local: a bare block nested
       in it can leave a name of its own there too, but the parser admits
       only names main's outermost block declares, and that declaration, the
       later one, is the one kept. *)
    let ltl =
      Ltl.subst
        (Map.Poly.of_alist_exn
        @@ List.map property_locals ~f:(fun name ->
            let tvar = Ident.Tvar name in
            match Map.Poly.find outer_renaming tvar with
            | Some term -> (tvar, term)
            | None ->
                failwith
                  (sprintf "the local %s of main named by the property was not \
                            renamed" name)))
        ltl
    in
    (* dispose #define for body *)
    (* let body = Statement.subst def_subst body in *)
    (* replace all return in main *)
    let body =
      ReturnReplacer.replace_return ~f:(fun _ -> Statement.mk_exit ()) body
    in
    (* a = 3; b = 4; if ... -> inits: a=3;b=4; body: if ... *)
    (* A local of main's outermost block is declared once, at the start of a
       run if it heads main: the draw its declaration stands for is dead when
       an initialiser follows, so `int i = 0;` there makes `i` 0 in the
       initial state, as a global's initialiser does, rather than a run whose
       first state shows the draw. *)
    let outer_locals =
      Map.Poly.data outer_renaming
      |> List.map ~f:(fun term ->
          let (tvar, _), _ = Term.let_var term in
          Ident.name_of_tvar tvar)
      |> Set.Poly.of_list
    in
    let inits, body_opt =
      Init.of_stmt ~declared:(Set.mem outer_locals) inits body
    in
    let body =
      match body_opt with None -> Statement.mk_exit () | Some body -> body
    in
    (* a = 3; b = a; -> a = 3; b = 3; *)
    let inits = sub_inits inits in
    (* dispose #define for inits *)
    let inits = List.map ~f:(Init.subst def_subst) inits in
    print @@ lazy "vvvvvvvvvvvvv Input C Program vvvvvvvvvvvvv";
    print @@ lazy (sprintf "[ltl]\n%s\n" (Ltl.string_of ltl));
    (* Debug.print @@ lazy
       (sprintf "[decls]\n%s\n"
         (String.concat_map_list ~sep:"\n" decls ~f:Declare.string_of)); *)
    print
    @@ lazy
         (sprintf "[inits]\n%s\n"
            (String.concat_map_list ~sep:"\n" inits ~f:Init.string_of));
    print @@ lazy (sprintf "[body]\n%s\n" (Statement.string_of body));
    print @@ lazy "";
    (* convert the given specification *)
    let ltl = Ltl.simplify_neg ltl in
    print @@ lazy (sprintf "[ltl(neg)]\n%s\n" (Ltl.string_of ltl));
    let ba = LogicConverter.ba_of_ltl ~print ltl in
    print
    @@ lazy
         (sprintf "[ba]\n%s\n"
            (BuchiAutomaton.string_of ~printer:Formula.str_of ba));
    let hmes = LogicConverter.hmes_of_ba ba in
    print @@ lazy (sprintf "[hmes]\n%s\n" (HMES.string_of hmes));
    Ok (HesOf.hes_of_chmes ~print (hmes, decls, inits, body))
  with
  | CSyntax.SemanticError error ->
      Result.fail (Error.of_string (sprintf "semantic error: %s" error))
  | CSyntax.SyntaxError error ->
      Result.fail
        (Error.of_string
           (sprintf "%s: syntax error: %s"
              (LexingHelper.get_position_string lexbuf)
              error))
  | CLtlParser.Error ->
      Result.fail
        (Error.of_string
           (sprintf "%s: syntax error"
              (LexingHelper.get_position_string lexbuf)))
  | CLtlLexer.SyntaxError error ->
      Result.fail
        (Error.of_string
           (sprintf "%s: syntax error: %s"
              (LexingHelper.get_position_string lexbuf)
              error))
  | CLtlLexer.ErrorFormatted error -> Result.fail (Error.of_string error)

let read_file file =
  In_channel.with_file file ~f:(fun ic ->
      let res = ref "" in
      try
        while true do
          res := !res ^ In_channel.input_line_exn ic ^ "\n"
        done;
        assert false
      with End_of_file -> !res)

module Preprocess : sig
  val preprocess : string -> string
end = struct
  let is_preprocess line = String.is_prefix ~prefix:"#" line

  (* let reg_include = Str.regexp "#include[ \t]+\\(\"[^\"]+\"|<[^>]+>\\)[ \t\r\n]+$" *)
  (* let let_include_preprocess line = assert (is_include_preprocess line); Str.matched_group 1 line *)

  let reg_type_of = Str.regexp "#\\([^ <\"\t\n]*\\)"

  let type_of_preprocess line =
    assert (Str.string_match reg_type_of line 0);
    Str.matched_group 1 line

  let reg_define_macro =
    Str.regexp
      "#define[ \
       \t]+\\([a-zA-Z_][a-zA-Z_0-9]*\\)(\\(\\|[a-zA-Z_][a-zA-Z_0-9]*\\(,[a-zA-Z_][a-zA-Z_0-9]*\\)*\\))[ \
       \t]+\\(.*\\)$"

  let is_define_macro line = Str.string_match reg_define_macro line 0

  let rec string_repeat str times =
    if times = 0 then "" else str ^ string_repeat str (times - 1)

  let subst_identifier id subst_to str =
    Str.global_replace
      (Str.regexp @@ "\\(^\\|[^a-zA-Z_0-9]\\)" ^ id ^ "\\($\\|[^a-zA-Z_0-9]\\)")
      ("\\1" ^ subst_to ^ "\\2")
      str

  let subst_macro id params subst_to program =
    let regstr_args =
      if List.is_empty params then ""
      else string_repeat "[^,]+," (List.length params - 1) ^ "[^)]+"
    in
    let reg =
      Str.regexp @@ "\\(^\\|[^a-zA-Z_0-9]\\)" ^ id ^ "[ \t]*(\\(" ^ regstr_args
      ^ "\\))"
    in
    Str.global_substitute reg
      (fun program ->
        let head = Str.matched_group 1 program in
        let args = Str.matched_group 2 program in
        let args =
          if String.equal args "" then []
          else String.split_on_chars ~on:[ ',' ] args
        in
        head
        ^ List.fold_left ~init:subst_to (List.zip_exn params args)
            ~f:(fun subst_to (param, arg) ->
              subst_identifier param arg subst_to))
      program

  let reg_define_const =
    Str.regexp "#define[ \t]+\\([a-zA-Z_][a-zA-Z_0-9]*\\)[ \t]+\\(.*\\)$"

  let is_define_const line = Str.string_match reg_define_const line 0

  (* TODO: for comments *)
  let preprocess program =
    let lines = program |> String.split_on_chars ~on:[ '\n' ] in
    let program, _ =
      List.fold_left
        ~f:(fun (program, line_number) line ->
          let line_number = line_number + 1 in
          if Fn.non is_preprocess line then (program, line_number)
          else if String.equal (type_of_preprocess line) "include" then
            (program, line_number (* TODO? *))
          else if String.equal (type_of_preprocess line) "define" then
            if is_define_macro line then
              let id = Str.matched_group 1 line in
              let params =
                Str.matched_group 2 line |> fun params ->
                if String.equal params "" then []
                else String.split_on_chars ~on:[ ',' ] params
              in
              let subst_to = Str.matched_group 4 line in
              (subst_macro id params subst_to program, line_number)
            else if is_define_const line then
              let id = Str.matched_group 1 line in
              let subst_to = Str.matched_group 2 line in
              (subst_identifier id subst_to program, line_number)
            else failwith @@ sprintf "%d: syntax error: %s" line_number line
          else
            failwith
            @@ sprintf "unknown preprocess: %s" (type_of_preprocess line))
        ~init:
          ( String.concat_map_list lines ~sep:"\n" ~f:(fun line ->
                if is_preprocess line then "" else line),
            0 )
        lines
    in
    program
end

let parse_cltl ~print program =
  let program = Preprocess.preprocess program in
  (*print @@ lazy "=============== Preprocessed ===============";
    print @@ lazy (program ^ "\n");*)
  program |> Lexing.from_string |> parse_cltl_from_lexbuf ~print

let parse_cctl ~print = Lexing.from_string >> parse_cctl_from_lexbuf ~print
let from_cltl_file ~print file = parse_cltl ~print @@ read_file file
let from_cctl_file ~print file = parse_cctl ~print @@ read_file file
