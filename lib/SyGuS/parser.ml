(* Reader for the SyGuS input format (linear integer arithmetic only; any other
   [set-logic] raises), producing the problem of [Problem.Make] with each
   [synth-fun] or [synth-inv] and its grammar, the declared variables and the
   constraints (an [inv-constraint] expanded into its three implications, and
   each constraint made conditional on the [assume]d terms, if any).  Every
   defined function is expanded while reading, and so is every [let] whose
   expansion stays small; a [let] whose expansion would not is kept as a [Let]
   binder over a fresh name, so the only binders a constraint contains are
   such [Let]s, and no two of them bind the same name.
   [solution_from_file] reads a list of [define-fun]s, used to load a candidate
   solution for a run. *)
open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.Logic
open Parsexp
open Problem
module Sexp = Ppx_sexp_conv_lib.Sexp

module type TermType = sig
  val of_term : Sexp.t list -> (term list, Error.t) result
  val sort_of_text : string -> Sort.t
  val term_of_op : string -> Sexp.t list -> term option
end

let count = ref 0

(* A fresh variable for the expansion of an [inv-constraint], named [INV_n] and
   guaranteed not to satisfy [taken].  The caller passes every name the file
   has given a meaning (declared variables, functions to synthesise, defined
   functions): a legal input may itself use [INV_1], and a generated variable
   equal to a declared one was added to the declared variables a second time
   (a crash), while one equal to the invariant's own name turned an
   application of the invariant into an Int argument of function sort. *)
let get_var ~taken =
  let rec go () =
    incr count;
    let v = Ident.Tvar (sprintf "INV_%d" !count) in
    if taken v then go () else v
  in
  go ()

module BoolTerm : TermType = struct
  open BoolTerm

  let of_term _sexps = failwith "not implemented yet"

  let sort_of_text = function
    | "Bool" -> SBool
    | s -> failwith @@ sprintf "unknown sort: %s" s

  let term_of_op op _args =
    match op with
    | "true" -> mk_bool true |> Option.some
    | "false" -> mk_bool false |> Option.some
    | "not" -> mk_not () |> Option.some
    | "and" -> mk_and () |> Option.some
    | "or" -> mk_or () |> Option.some
    | "=>" -> mk_imply () |> Option.some
    | "xor" -> mk_xor () |> Option.some
    | "=" -> mk_eq (Sort.mk_fresh_svar ()) |> Option.some
    | "ite" -> mk_ite (Sort.mk_fresh_svar ()) |> Option.some
    | _ -> None
end

module IntTerm : TermType = struct
  open IntTerm

  let of_term _sexps = failwith "not implemented yet"

  let sort_of_text = function
    | "Int" -> SInt
    | s -> failwith @@ sprintf "unknown sort: %s" s

  let term_of_op op args =
    match op with
    | "+" -> mk_add () |> Option.some
    | "-" -> (
        match List.length args with
        | 1 -> mk_neg () |> Option.some
        | 2 -> mk_sub () |> Option.some
        | _ -> None)
    | "*" -> mk_mul () |> Option.some
    | "div" -> mk_div Value.Euclidean |> Option.some
    | "mod" -> mk_rem Value.Euclidean |> Option.some
    | "abs" -> mk_abs () |> Option.some
    | text -> (
        try
          mk_int (Z.of_string text)
          |> Option.some (* assume that the text can be converted into bigint *)
        with Invalid_argument err ->
          failwith (sprintf "[term_of_op] %s not supported\n%s" op err))
end

module ExtTerm : TermType = struct
  open Ast.Logic.ExtTerm

  let of_term _sexps = failwith "not implemented yet"

  let sort_of_text = function
    | "Bool" -> SBool
    | "Int" -> SInt
    | s -> failwith @@ sprintf "unknown sort: %s" s

  let term_of_op op args =
    match op with
    | "=" ->
        mk_int_eq ()
        |> Option.some (* '=' is used only for comparing int value in LIA *)
    | "<=" -> mk_leq () |> Option.some
    | ">=" -> mk_geq () |> Option.some
    | "<" -> mk_lt () |> Option.some
    | ">" -> mk_gt () |> Option.some
    | op -> (
        match BoolTerm.term_of_op op args with
        | None -> IntTerm.term_of_op op args
        | x -> x)
end

module Make (Term : TermType) (ProblemTerm : Problem.TermType) : sig
  val parse_fundef :
    term_subst_map -> sort_env_map -> Sexp.t -> Ident.tvar * term

  val parse_term :
    Problem.Make(ProblemTerm).t ->
    term_subst_map ->
    sort_env_map ->
    Sexp.t ->
    term

  val of_problem : Sexp.t list -> (Problem.Make(ProblemTerm).t, Error.t) result
end = struct
  module CFG = Problem.CFG (ProblemTerm)
  module Problem = Problem.Make (ProblemTerm)
  open Ast.Logic.IntTerm
  open Ast.Logic.BoolTerm

  let rec parse_bfTerm = function
    | Sexp.Atom idORlit -> (
        match Term.term_of_op idORlit [] with
        | Some term -> CFG.mk_bfTerm_literal term
        | None -> failwith "unknown style of bfTerm")
    | Sexp.List [ Sexp.Atom "_"; _; _ ] ->
        failwith "this style of identifier is not supported yet"
    | Sexp.List (Sexp.Atom id :: bfTerms) -> (
        match Term.term_of_op id bfTerms with
        | Some term ->
            List.map ~f:parse_bfTerm bfTerms
            |> CFG.mk_bfTerm_fun (CFG.mk_identifier term)
        | None -> failwith "unknown style of bfTerm")
    | _ -> failwith "unknown style of bfTerm"

  let parse_gTerm = function
    | Sexp.List [ Sexp.Atom "Constant"; Sexp.Atom sort ] ->
        Term.sort_of_text sort |> CFG.mk_gTerm_constant
    | Sexp.List [ Sexp.Atom "Variable"; Sexp.Atom sort ] ->
        Term.sort_of_text sort |> CFG.mk_gTerm_variable
    | bfterm -> parse_bfTerm bfterm |> CFG.mk_gTerm_bfTerm

  let parse_cfg (symbol_def : Sexp.t list) grammer_def =
    let starting_symbol =
      match symbol_def with
      | Sexp.List [ Sexp.Atom sym; Sexp.Atom _sort ] :: _ -> CFG.mk_symbol sym
      | _ -> failwith "unknown style of symbol_def"
    in
    let grammer =
      List.fold ~init:Map.Poly.empty ~f:(fun acc (sym, rule) ->
          Map.Poly.add_exn acc ~key:sym ~data:rule)
      @@ List.map grammer_def ~f:(function
        | Sexp.List [ Sexp.Atom sym; Sexp.Atom sort; Sexp.List rule ] ->
            (sym, (Term.sort_of_text sort, List.map ~f:parse_gTerm rule))
        | _ -> failwith "invalid syntax in grammer")
    in
    CFG.mk_cfg starting_symbol grammer

  let parse_synth_fun problem name (args : Sexp.t list) (sort : Sort.t)
      (grammer : Sexp.t list) : Problem.t =
    let cfg =
      match grammer with
      | [] -> None
      | _ ->
          (* A grammar restricts the terms a solution may be built from, and
             nothing downstream honours it: the conversion to a constraint
             problem keeps only the function's sort, so the problem solved is the
             unrestricted one and its answer is reported as the answer to the
             stated one -- a grammar admitting exactly [0] for a function that
             must satisfy [f 0 = 1] came back sat, where cvc5 reports the
             synthesis as failed.  It is refused here, where it is read, rather
             than after being parsed, because parsing it first produces the wrong
             complaint: a production naming a synthesis parameter or another
             nonterminal is sent to the operator table, and the file was rejected
             with "[term_of_op] z not supported", which reads as a fault in the
             user's grammar rather than as a feature this tool does not have.
             No file in this repository's SyGuS corpus carries a grammar -- 0 of
             2,661 -- so nothing that used to be answered stops being answered. *)
          failwith
          @@ sprintf
               "%s is declared with a grammar, and synthesis restricted by a \
                grammar is not implemented: the grammar would be ignored and \
                the answer would be about the unrestricted problem"
               (Ident.name_of_tvar name)
    in
    let parse_arg = function
      | Sexp.List [ Sexp.Atom _name; Sexp.Atom sort ] -> Term.sort_of_text sort
      | _ -> failwith "unknown style of args"
    in
    let sort =
      List.fold_right ~init:sort args ~f:(parse_arg >> Sort.mk_arrow)
    in
    Problem.add_synth_fun problem name sort cfg

  (* The reader for a grammar, kept although the declaration above refuses one
     before reaching it.  It is what a repair starts from, and the first thing it
     needs is the case it does not have: a production naming a synthesis
     parameter or another nonterminal goes to [Term.term_of_op], which reads it
     as an operator or a numeral and fails on "z" or on "Start". *)
  let _ = parse_cfg

  (* The sort of each fresh name a [let] binds, for [sort_of_let_def]: the
     names are fresh, so one table for the whole read cannot confuse two
     scopes. *)
  let let_sorts : (Ident.tvar, Sort.t) Hashtbl.Poly.t = Hashtbl.Poly.create ()

  (* The sort of an untyped [let]'s definition [t], read in [venv] (declared
     variables and the parameters of the enclosing [define-fun]) and the sorts
     of the [let] names bound so far.  The conversion to a constraint problem
     needs it: a [Let] whose variable is used as a Boolean atom must say it is
     Boolean.  An [ite]'s result sort is a sort variable, so it is read off the
     [then] branch; a term whose sort cannot be determined here keeps a sort
     variable. *)
  let rec sort_of_let_def venv t =
    let env =
      Hashtbl.fold let_sorts ~init:venv ~f:(fun ~key ~data acc ->
          Map.Poly.set acc ~key ~data)
    in
    match Ast.Logic.ExtTerm.head_sort_of env t with
    | Sort.SVar _ -> (
        match let_apps t with
        | _, [ _; t_then; _ ] -> sort_of_let_def venv t_then
        | _ -> Sort.mk_fresh_svar ())
    | sort -> sort
    | exception exn_ when not (Common.Timer.is_async exn_) ->
        Sort.mk_fresh_svar ()

  (* Whether [t] with every [Let] substituted away has at most [cap] nodes;
     the count saturates, so a [let] chain whose expansion is exponential is
     measured in time linear in its size.  The variables a [Let] binds are
     fresh, so a name never needs to be looked up past its own binder. *)
  let expanded_size_at_most cap t =
    let rec size env = function
      | Var (v, _) -> Option.value (Map.Poly.find env v) ~default:1
      | Con _ -> 1
      | App (t1, t2, _) -> min cap (size env t1 + size env t2)
      | Bin (_, _, _, t1, _) | TyApp (t1, _, _) | TyLam (_, t1, _) ->
          min cap (1 + size env t1)
      | Let (v, _, def, body, _) ->
          size (Map.Poly.set env ~key:v ~data:(size env def)) body
    in
    size Map.Poly.empty t < cap

  (* The expansion bound above which a [let] is kept as a binder rather than
     substituted.  Keeping every [let] would send every such input through the
     constraint pipeline's [let] handling, which once answered a satisfiable
     CHC encoding of a Lustre benchmark [unsat] where the same clauses with
     their [let]s expanded were answered [sat]; substituting every [let]
     exhausts memory on a chain whose expansion is exponential.  A file of the
     SyGuS invariant corpus expands to a few thousand nodes or to about 1e10,
     so any bound between keeps the first kind on the substituting path. *)
  let let_expansion_cap = 100_000

  let rec parse_term problem fenv venv = function
    | Sexp.List (Sexp.Atom op :: args) -> (
        match Problem.find_synth_fun_of problem (Ident.Tvar op) with
        (* uninterpreted variable *)
        | Some (_sort, _cfg) ->
            List.fold ~init:(mk_var (Ident.Tvar op)) args ~f:(fun acc ->
                parse_term problem fenv venv >> mk_app acc)
        | None -> (
            match Map.Poly.find fenv (Ident.Tvar op) with
            | Some term ->
                (* if the term is an interpreted variable, substitute it  *)
                beta_reduction
                  (mk_apps term
                     (List.map args ~f:(parse_term problem fenv venv)))
            | None -> (
                match op with
                | "+" -> sum (List.map ~f:(parse_term problem fenv venv) args)
                | "*" -> prod (List.map ~f:(parse_term problem fenv venv) args)
                | "and" ->
                    and_of (List.map ~f:(parse_term problem fenv venv) args)
                | "or" ->
                    or_of (List.map ~f:(parse_term problem fenv venv) args)
                | "distinct" ->
                    (* pairwise over the POSITIONS of the operand list: two
                       occurrences of one variable are two operands, and
                       [distinct] is false as soon as two of its arguments are
                       equal.  Collecting them into a set first dropped the
                       repetition and made [(distinct x x)] the empty
                       conjunction, i.e. true. *)
                    let ts = List.map args ~f:(parse_term problem fenv venv) in
                    let rec pairs = function
                      | [] -> []
                      | t :: rest ->
                          List.map rest ~f:(neq_of SInt t) @ pairs rest
                    in
                    and_of @@ pairs ts
                | "let" -> (
                    (* A [let] is read as a binder, [Let (x', s, d, body)],
                       under a FRESH name [x'] for each bound name [x]: the
                       body is read with [x] standing for the variable [x'].
                       The definitions are then substituted for the fresh
                       names unless the expansion would pass
                       [let_expansion_cap], in which case the binder is
                       kept.  Substituting unconditionally (as this reader
                       once did) copies a definition into every use, and a
                       chain of [let]s each using the previous name several
                       times grows exponentially: the Lustre-generated
                       SyGuS invariant benchmarks nest 44 [let]s whose
                       expansion has about 1.5e10 nodes, and the reader grew
                       by about 80 MB/s until it was killed.  The fresh name
                       is what keeps the binder from capturing: [fenv] holds
                       terms read in an OUTER scope, and one placed under a
                       binder of the same name would be captured by it -- in
                       [(let ((y x)) (let ((x Int 5)) (= y 5)))] the [x]
                       that [y] stands for must stay the outer [x], or the
                       constraint reads as [5 = 5].  Bindings are
                       simultaneous: every definition is read in the outer
                       scope.  SyGuS v1 writes [(var sort def)], v2/SMT-LIB
                       [(var def)]; an untyped binding gets the sort of its
                       definition ([sort_of_let_def]). *)
                    match args with
                    | [ Sexp.List binds; body ] ->
                        let bound =
                          List.map binds ~f:(function
                            | Sexp.List [ Sexp.Atom var; Sexp.Atom sort; def ]
                              ->
                                ( Ident.Tvar var,
                                  Term.sort_of_text sort,
                                  parse_term problem fenv venv def )
                            | Sexp.List [ Sexp.Atom var; def ] ->
                                let def = parse_term problem fenv venv def in
                                (Ident.Tvar var, sort_of_let_def venv def, def)
                            | _ -> failwith "let")
                          |> List.map ~f:(fun (tvar, sort, def) ->
                                 let fresh = Ident.mk_fresh_tvar () in
                                 Hashtbl.set let_sorts ~key:fresh ~data:sort;
                                 (tvar, fresh, sort, def))
                        in
                        let fenv =
                          List.fold bound ~init:fenv
                            ~f:(fun acc (tvar, fresh, _, _) ->
                              Map.Poly.set acc ~key:tvar ~data:(mk_var fresh))
                        in
                        (* The inner binding is the nearer one and must win over
                           an outer declared variable of the same name.  The
                           bound names go into [fenv] while a declared variable
                           lives in [venv], and the lookup for an atom consults
                           [venv] first -- so the outer declaration won, and
                           [(declare-var x Int)] beside [(let ((x 0)) x)] made
                           the body read as the declared [x], turning a
                           realizable problem unsat and an infeasible one sat.
                           Removing the bound names from [venv] for the BODY
                           restores the nearest binding. *)
                        let venv =
                          List.fold bound ~init:venv
                            ~f:(fun acc (tvar, _, _, _) ->
                              Map.Poly.remove acc tvar)
                        in
                        let body = parse_term problem fenv venv body in
                        let bound_term =
                          List.fold_right bound ~init:body
                            ~f:(fun (_, fresh, sort, def) acc ->
                              mk_let fresh sort def acc)
                        in
                        if expanded_size_at_most let_expansion_cap bound_term
                        then
                          subst
                            (Map.Poly.of_alist_exn
                            @@ List.map bound ~f:(fun (_, fresh, _, def) ->
                                   (fresh, def)))
                            body
                        else bound_term
                    | _ -> failwith "let")
                (* SMT-LIB's attributes for operators of more than two
                   operands (Core and Ints theories): [=] and the orders are
                   :chainable, [(op a b c)] meaning [(and (op a b) (op b c))];
                   [-], [div] and [xor] are :left-assoc; [=>] is :right-assoc.
                   The theory constructors below take exactly two operands,
                   and three or more used to be rejected ([-]) or applied
                   regardless and refused later as an unknown symbol. *)
                | ("=" | "<=" | "<" | ">=" | ">") when List.length args > 2 ->
                    let rec chain = function
                      | a :: (b :: _ as rest) ->
                          Sexp.List [ Sexp.Atom op; a; b ] :: chain rest
                      | _ -> []
                    in
                    and_of
                      (List.map (chain args) ~f:(parse_term problem fenv venv))
                | ("-" | "div" | "xor") when List.length args > 2 -> (
                    match args with
                    | a :: b :: rest ->
                        parse_term problem fenv venv
                        @@ Sexp.List
                             (Sexp.Atom op
                             :: Sexp.List [ Sexp.Atom op; a; b ]
                             :: rest)
                    | _ -> assert false)
                | "=>" when List.length args > 2 -> (
                    match List.rev args with
                    | last :: rev_init ->
                        parse_term problem fenv venv
                        @@ List.fold rev_init ~init:last ~f:(fun acc a ->
                               Sexp.List [ Sexp.Atom op; a; acc ])
                    | [] -> assert false)
                | _ -> (
                    match Term.term_of_op op args with
                    | Some x ->
                        List.fold ~init:x args ~f:(fun acc ->
                            parse_term problem fenv venv >> mk_app acc)
                        (* if the operator is defined in the theory *)
                    | None -> failwith @@ sprintf "unknown operator : %s" op))))
    | Sexp.Atom var -> (
        match Map.Poly.find venv (Ident.Tvar var) with
        | Some SBool -> eq_of SBool (mk_var (Ident.Tvar var)) (mk_bool true)
        | Some _ -> mk_var (Ident.Tvar var)
        | None -> (
            match Map.Poly.find fenv (Ident.Tvar var) with
            | Some term ->
                (* if the term is an interpreted variable, substitute it  *)
                beta_reduction term
            | None -> (
                match Problem.find_synth_fun_of problem (Ident.Tvar var) with
                | Some _ ->
                    (* a function to synthesise of no parameters: SMT-LIB writes
                       its application as the bare symbol, [c] and not [(c)];
                       it was sent to the numeral reader and rejected *)
                    mk_var (Ident.Tvar var)
                | None -> (
                    match Term.term_of_op var [] with
                    | Some term -> term (* nullary term *)
                    | None -> failwith @@ sprintf "unknown operator: %s" var))))
    | _ -> failwith "unknown style of constraint"

  let parse_inv_constraint problem fenv inv_f pre_f trans_f post_f =
    let sort_of_inv_f =
      match Problem.find_synth_fun_of problem inv_f with
      | Some (sort, _) -> sort
      | None -> (
          match Problem.find_synth_fun_of problem pre_f with
          | Some (sort, _) -> sort
          | None -> (
              match Problem.find_synth_fun_of problem post_f with
              | Some (sort, _) -> sort
              | None -> failwith "sort need to be known by trans_f"))
    in

    (* p1 = pre_f x1 x2 .. xn *)
    (* p2 = inv_f x1 x2 .. xn *)
    (* p3 = trans_f x1 x2 .. xn x1' x2' .. xn' *)
    (* p4 = inv_f x1' x2' .. xn' *)
    (* p5 = post_f x1 x2 .. xn *)

    (* p1 => p2 *)
    (* p2 and p3 => p4 *)
    (* p2 => p5 *)
    let var_list, var_list' =
      let taken v =
        let synth_funs, declared_vars, _ = problem in
        Map.Poly.mem synth_funs v || Map.Poly.mem declared_vars v
        || Map.Poly.mem fenv v
      in
      let rec sub acc = function
        | Sort.SArrow (s, c) when Sort.is_pure_triple c ->
            sub ((get_var ~taken, s) :: acc) c.val_type
        | Sort.SArrow (_, _) -> failwith "sub"
        | _ -> List.rev acc
      in
      (sub [] sort_of_inv_f, sub [] sort_of_inv_f)
    in
    let mk_atom pvar var_list =
      match Map.Poly.find fenv pvar with
      | Some term ->
          let term, map =
            let rec sub term var_list map =
              match var_list with
              | [] -> (term, map)
              | (v, _) :: vs ->
                  assert (is_lam term);
                  let _, var, _sort, term, _ = let_bin term in
                  sub term vs @@ Map.Poly.add_exn map ~key:var ~data:(mk_var v)
            in
            sub term var_list Map.Poly.empty
          in
          subst map term
      | None ->
          List.fold var_list ~init:(mk_var pvar) ~f:(fun acc ->
              fst >> mk_var >> mk_app acc)
    in
    let p1 = mk_atom pre_f var_list in
    let p2 = mk_atom inv_f var_list in
    let p3 = mk_atom trans_f @@ var_list @ var_list' in
    let p4 = mk_atom inv_f var_list' in
    let p5 = mk_atom post_f var_list in
    ( List.fold ~init:problem ~f:(Problem.add_declared_var >> Tuple2.uncurry)
      @@ var_list @ var_list',
      [
        mk_apps (mk_imply ()) [ p1; p2 ];
        mk_apps (mk_imply ()) [ mk_apps (mk_and ()) [ p2; p3 ]; p4 ];
        mk_apps (mk_imply ()) [ p2; p5 ];
      ] )

  let var_and_sort_of_arg = function
    | Sexp.List [ Sexp.Atom var; Sexp.Atom sort ] ->
        (Ident.Tvar var, Term.sort_of_text sort)
    | _ -> failwith "args are invalid"

  let add_args_to_venv venv =
    List.fold ~init:venv ~f:(fun acc (var, sort) ->
        Map.Poly.update acc var ~f:(fun _ -> sort))

  let parse_fundef fenv venv = function
    | Sexp.List
        [
          Sexp.Atom "define-fun";
          Sexp.Atom name;
          Sexp.List args;
          Sexp.Atom _sort;
          def;
        ] ->
        let args = List.map ~f:var_and_sort_of_arg args in
        (* The defined fun contains neighter any free variable nor any synth-fun*)
        let venv' = add_args_to_venv venv args in
        ( Ident.Tvar name,
          mk_lambda args
          @@ parse_term
               (Problem.mk_problem Map.Poly.empty Map.Poly.empty [])
               fenv venv' def )
    | _ ->
        failwith
        @@ sprintf "sygus function definition should start from 'define-fun'"

  let parse_smt_cmd problem fenv venv = function
    | Sexp.List [ Sexp.Atom "declare-datatype"; _; _ ]
    | Sexp.List [ Sexp.Atom "declare-datatypes"; _; _ ] ->
        failwith "declare-datatype(s) is not supported yet"
    | Sexp.List [ Sexp.Atom "declare-sort"; _; _ ] ->
        failwith "declare-sort is not supported yet"
    | Sexp.List
        [
          Sexp.Atom "define-fun";
          Sexp.Atom _name;
          Sexp.List _args;
          Sexp.Atom _sort;
          _def;
        ] as sexp ->
        let name, term = parse_fundef fenv venv sexp in
        (problem, Map.Poly.add_exn fenv ~key:name ~data:term)
    | Sexp.List [ Sexp.Atom "define-sort" ] ->
        failwith "define-sort is not supported yet"
    | Sexp.List (Sexp.Atom cmd :: _) ->
        failwith @@ sprintf "unknown smt cmd : %s" cmd
    | _ -> failwith "unknown smt cmd"

  (* [assumes] holds the terms of the [assume] commands read so far (SyGuS-IF
     2.1).  The specification is that the conjunction of all assumptions
     implies the conjunction of all constraints, wherever in the file each
     appears; so at [check-synth] every constraint [c] becomes
     [assumptions => c], which is the same formula split per constraint. *)
  let rec parse_cmds assumes problem fenv (venv : sort_env_map) = function
    | [] -> Result.fail @@ Error.of_string "lack of check-synth command"
    | Sexp.List [ Sexp.Atom "check-synth" ] :: [] -> (
        match assumes with
        | [] -> Ok problem
        | _ ->
            let synth_funs, declared_vars, constraints = problem in
            let assumption = and_of (List.rev assumes) in
            Ok
              (Problem.mk_problem synth_funs declared_vars
                 (List.map constraints ~f:(fun c ->
                      mk_apps (mk_imply ()) [ assumption; c ]))))
    | Sexp.List [ Sexp.Atom "assume"; t ] :: es ->
        parse_cmds
          (parse_term problem fenv venv t :: assumes)
          problem fenv venv es
    | Sexp.List (Sexp.Atom ("set-info" | "set-option" | "set-feature") :: _)
      :: es ->
        (* metadata, solver options and feature declarations: none changes
           what the problem means, and each used to stop the reader *)
        parse_cmds assumes problem fenv venv es
    | Sexp.List [ Sexp.Atom "constraint"; constr ] :: es ->
        let problem' =
          Problem.add_constraint problem @@ parse_term problem fenv venv constr
        in
        parse_cmds assumes problem' fenv venv es
    | Sexp.List [ Sexp.Atom "declare-var"; Sexp.Atom var; Sexp.Atom sort ] :: es
      ->
        let var = Ident.Tvar var in
        let sort = Term.sort_of_text sort in
        let problem' = Problem.add_declared_var problem var sort in
        parse_cmds assumes problem' fenv (Map.Poly.add_exn venv ~key:var ~data:sort) es
    | Sexp.List
        [ Sexp.Atom "declare-primed-var"; Sexp.Atom var; Sexp.Atom sort ]
      :: es ->
        (* SyGuS-IF 1.0: declares both [var] and its primed copy [var!]; the
           copy was missing, so a constraint naming it was rejected *)
        let sort = Term.sort_of_text sort in
        let vars = [ Ident.Tvar var; Ident.Tvar (var ^ "!") ] in
        let problem', venv' =
          List.fold vars ~init:(problem, venv) ~f:(fun (p, v) x ->
              ( Problem.add_declared_var p x sort,
                Map.Poly.add_exn v ~key:x ~data:sort ))
        in
        parse_cmds assumes problem' fenv venv' es
    | Sexp.List
        [
          Sexp.Atom "inv-constraint";
          Sexp.Atom inv_f;
          Sexp.Atom pre_f;
          Sexp.Atom trans_f;
          Sexp.Atom post_f;
        ]
      :: es ->
        let inv_f, pre_f, trans_f, post_f =
          ( Ident.Tvar inv_f,
            Ident.Tvar pre_f,
            Ident.Tvar trans_f,
            Ident.Tvar post_f )
        in
        let problem, constrs =
          parse_inv_constraint problem fenv inv_f pre_f trans_f post_f
        in
        (*print_endline @@ sprintf "[parse_inv_constraint]\n%s"
           (String.concat_map_list ~sep:"\n" constrs ~f:(fun t -> "*) " ^ str_of t));*)
        let problem' =
          List.fold ~init:problem constrs ~f:Problem.add_constraint
        in
        parse_cmds assumes problem' fenv venv es
    | Sexp.List
        (Sexp.Atom "synth-fun"
        :: Sexp.Atom name
        :: Sexp.List args
        :: Sexp.Atom sort
        :: grammer_def)
      :: es ->
        let problem' =
          parse_synth_fun problem (Ident.Tvar name) args
            (Term.sort_of_text sort) grammer_def
        in
        parse_cmds assumes problem' fenv venv es
    | Sexp.List
        (Sexp.Atom "synth-inv"
        :: Sexp.Atom name
        :: Sexp.List args
        :: grammer_def)
      :: es ->
        let problem' =
          parse_synth_fun problem (Ident.Tvar name) args SBool grammer_def
        in
        parse_cmds assumes problem' fenv venv es
    | cmd :: es ->
        let problem', fenv' = parse_smt_cmd problem fenv venv cmd in
        parse_cmds assumes problem' fenv' venv es

  let of_problem =
    parse_cmds []
      (Problem.mk_problem Map.Poly.empty Map.Poly.empty [])
      Map.Poly.empty Map.Poly.empty
end

let parse = function
  | Sexp.List [ Sexp.Atom "set-logic"; Sexp.Atom logic ] :: es -> (
      match logic_type_of_str logic with
      | Lia ->
          let module Parser = Make (ExtTerm) (Problem.ExtTerm) in
          Parser.of_problem es
      | _ ->
          Result.fail
          @@ Error.of_thunk (fun () ->
              sprintf
                "[set-logic] SyGuS logic %s is not supported: only LIA (or \
                 SAT) is implemented"
                logic))
  | _ ->
      Result.fail
      @@ Error.of_thunk (fun () ->
          sprintf "sygus problem file should start from 'set-logic'")

(* SMT-LIB's quoted symbol [|s|] is the same symbol as [s] whenever [s] is a
   legal simple symbol; the s-expression reader keeps the bars as part of the
   atom, so a file declaring [|x|] and using [x] was rejected, and a solution
   printed by [Printer] (which quotes every name) did not name the function
   it defines when read back.  Bars are removed only when what is inside is a
   simple symbol that is not a reserved word: [|5|] is a symbol and not the
   numeral, and [|let|] is not the binder.  A quoted symbol containing white
   space is split by the s-expression reader before this point and is not
   supported. *)
let rec unquote_symbols = function
  | Sexp.Atom s as atom ->
      let n = String.length s in
      if n >= 3 && Char.equal s.[0] '|' && Char.equal s.[n - 1] '|' then
        let inner = String.sub s ~pos:1 ~len:(n - 2) in
        let simple_char c =
          Char.is_alphanum c || String.mem "~!@$%^&*_-+=<>.?/" c
        in
        let reserved =
          [ "let"; "forall"; "exists"; "!"; "_"; "as"; "par"; "match";
            "NUMERAL"; "DECIMAL"; "STRING"; "BINARY"; "HEXADECIMAL" ]
        in
        if
          String.for_all inner ~f:simple_char
          && (not (Char.is_digit inner.[0]))
          && not (List.mem reserved inner ~equal:String.equal)
        then Sexp.Atom inner
        else atom
      else atom
  | Sexp.List l -> Sexp.List (List.map l ~f:unquote_symbols)

let from_file filename =
  match Many.parse_string @@ In_channel.read_all filename with
  | Ok sexps -> parse (List.map sexps ~f:unquote_symbols)
  | Error err ->
      Result.fail
      @@ Error.of_thunk (fun () ->
          let pos = Parse_error.position err in
          let msg = Parse_error.message err in
          sprintf "at line %d, col %d: %s" pos.line pos.col msg)

let solution_from_file filename =
  try
    match Many.parse_string @@ In_channel.read_all filename with
    | Ok sexps ->
        let module Parser = Make (ExtTerm) (Problem.ExtTerm) in
        Result.return
        @@ List.map sexps
             ~f:
               (unquote_symbols
               >> Parser.parse_fundef Map.Poly.empty Map.Poly.empty)
    | Error err ->
        Result.fail
        @@ Error.of_thunk (fun () ->
            let pos = Parse_error.position err in
            let msg = Parse_error.message err in
            sprintf "at line %d, col %d: %s" pos.line pos.col msg)
  with Sys_error err -> Result.fail @@ Error.of_thunk (fun () -> err)

(*
let sort_of_sexp = function
  | "Bool" -> T_bool.SBool
  | "Int"  -> T_int.SInt
  | "Real" -> T_real.SReal
  | _ -> failwith "[sort_of_sexp] unimplemented"
(* Assume that every input is integer *)
let rec formula_of_sexp tenv = function
  | Sexp.List [Sexp.Atom ">="; left; right] ->
    let left, right = term_of_sexp tenv left, term_of_sexp tenv right in
    Formula.geq left right
  | Sexp.List [Sexp.Atom "<="; left; right] ->
    let left, right = term_of_sexp tenv left, term_of_sexp tenv right in
    Formula.leq left right
  | Sexp.List [Sexp.Atom "<"; left; right] ->
    let left, right = term_of_sexp tenv left, term_of_sexp tenv right in
    Formula.lt left right
  | Sexp.List [Sexp.Atom ">"; left; right] ->
    let left, right = term_of_sexp tenv left, term_of_sexp tenv right in
    Formula.gt left right
  | Sexp.List [Sexp.Atom "="; left; right] ->
    let left, right = term_of_sexp tenv left, term_of_sexp tenv right in
    Formula.eq left right
  | Sexp.List [Sexp.Atom "not"; sexp] ->
    Formula.mk_neg (formula_of_sexp tenv sexp)
  | Sexp.List [Sexp.Atom "and"; left; right] ->
    Formula.mk_and (formula_of_sexp tenv left) (formula_of_sexp tenv right)
  | Sexp.List (Sexp.Atom "and" :: args) -> (* for SyGuS '18 *)
    Formula.and_of (List.map ~f:(formula_of_sexp tenv) args)
  | Sexp.List [Sexp.Atom "or"; left; right] ->
    Formula.mk_or (formula_of_sexp tenv left) (formula_of_sexp tenv right)
  | Sexp.List (Sexp.Atom "or" :: args) -> (* for SyGuS '18 *)
    Formula.or_of (List.map ~f:(formula_of_sexp tenv) args)
  | Sexp.List [Sexp.Atom "=>"; left; right] -> (* for SyGuS '18 *)
    Formula.mk_imply (formula_of_sexp tenv left) (formula_of_sexp tenv right)
  | Sexp.List [Sexp.Atom "ite"; cond; left; right] -> (* for SyGuS '18 *)
    let cond' = formula_of_sexp tenv cond in
    Formula.mk_or
      (Formula.mk_and cond' (formula_of_sexp tenv left))
      (Formula.mk_and (Formula.mk_neg cond') (formula_of_sexp tenv right))
  | sexp -> failwith @@ "parse error: " ^ (Sexp.to_string_hum sexp)
and term_of_sexp tenv = function
  | Sexp.List [Sexp.Atom "+"; left; right] ->
    T_int.mk_add (term_of_sexp tenv left) (term_of_sexp tenv right)
  | Sexp.List (Sexp.Atom "+" :: terms) -> (* for SyGuS '18 *)
    T_int.mk_sum (T_int.zero ()) (List.map ~f:(term_of_sexp tenv) terms)
  | Sexp.List [Sexp.Atom "-"; left; right] ->
    T_int.mk_sub (term_of_sexp tenv left) (term_of_sexp tenv right)
  | Sexp.List [Sexp.Atom "*"; left; right] ->
    T_int.mk_mul (term_of_sexp tenv left) (term_of_sexp tenv right)
  | Sexp.List [Sexp.Atom "/"; left; right] ->
    T_int.mk_div (term_of_sexp tenv left) (term_of_sexp tenv right)
  | Sexp.List [Sexp.Atom "ite"; cond; left; right] -> (* for SyGuS '18 *)
    T_bool.mk_if_then_else (term_of_sexp tenv cond)
      (term_of_sexp tenv left) (term_of_sexp tenv right)
  | Sexp.Atom ident -> begin
      try T_int.mk_int (Z.of_string ident)
      with _ ->
        Term.mk_var (Ident.Tvar ident) @@
        List.Assoc.find_exn ~equal:Stdlib.(=) tenv (Ident.Tvar ident)
    end
  | sexp -> failwith @@ "[term_of_sexp] parse error: " ^ Sexp.to_string_hum sexp
let bind_of_sexp = function
  | Sexp.List [Sexp.Atom ident; Sexp.Atom sort] -> Ident.Tvar ident, sort_of_sexp sort
  | sexp -> failwith @@ "[bind_of_sexp] parse error: " ^ Sexp.to_string_hum sexp
let rec toplevel acc logic_type tenv
    (fenv: (string * Formula.t) list)
    (penv: (string * Atom.t) list) = function
  | [] -> Result.fail @@ Error.of_string "check-synth is lacking"
  | Sexp.List [Sexp.Atom "check-synth"] :: _ -> Ok (logic_type, acc)
  | Sexp.List [Sexp.Atom "set-logic"; Sexp.Atom str] :: es ->
    let logic_type = Problem.logic_type_of_str str in
    toplevel acc logic_type tenv fenv penv es
  | Sexp.List [Sexp.Atom "synth-inv"; Sexp.Atom name; Sexp.List args] :: es ->
    let pvapp =
      let args = List.map ~f:bind_of_sexp args in
      Atom.pvar_app_of_senv (Ident.Pvar name) args
    in
    toplevel acc logic_type tenv fenv ((name, pvapp) :: penv) es
  | Sexp.List [Sexp.Atom "declare-primed-var"; Sexp.Atom name; Sexp.Atom sort] :: es ->
    let term  = Ident.Tvar name, sort_of_sexp sort in
    let term' = Ident.Tvar (name ^ "!"), sort_of_sexp sort in
    toplevel acc logic_type ((term, term') :: tenv) fenv penv es
  | Sexp.List [Sexp.Atom "define-fun"; Sexp.Atom name; Sexp.List args; _; def] :: es ->
    let fn = formula_of_sexp (List.map ~f:bind_of_sexp args) def in
    toplevel acc logic_type tenv ((name, fn) :: fenv) penv es
  | Sexp.List (Sexp.Atom "inv-constraint" :: cs) :: es ->
    let mk_inv_constraint acc tenv
        (fenv: (string, Formula.t) List.Assoc.t)
        (penv: (string, Atom.t) List.Assoc.t) = function
      | [Sexp.Atom invf; Sexp.Atom pref; Sexp.Atom transf; Sexp.Atom postf] ->
        let inv  = Formula.mk_atom (List.Assoc.find_exn ~equal:Stdlib.(=) penv invf) in
        let sub =
          Map.Poly.of_alist_exn @@
          List.map tenv ~f:(fun ((idx, _), (idx', sx')) -> idx, Term.mk_var idx' sx')
        in
        let pre = Formula.mk_imply (List.Assoc.find_exn ~equal:Stdlib.(=) fenv pref) inv in
        let post = Formula.mk_imply inv (List.Assoc.find_exn ~equal:Stdlib.(=) fenv postf) in
        let trans =
          Formula.mk_imply
            (Formula.mk_and inv (List.Assoc.find_exn ~equal:Stdlib.(=) fenv transf))
            (Formula.subst sub inv)
        in
        pre :: trans :: post :: acc
      | cs ->
        failwith @@ "[mk_inv_constraint] parse error: " ^ Sexp.to_string_hum @@ Sexp.List cs
    in
    let acc' = mk_inv_constraint acc tenv fenv penv cs in
    toplevel acc' logic_type tenv fenv penv es
  | Sexp.List (Sexp.Atom cmd :: _) :: _ ->
    Or_error.unimplemented @@ cmd ^ " is not supported"
  | sexp ->
    Result.fail @@
    Error.of_thunk (fun () -> "parse error: " ^ Sexp.to_string_hum @@ Sexp.List sexp)
let toplevel = toplevel [] Any [] [] []

let from_file filename =
  match Many.parse_string @@ In_channel.read_all filename with
  | Ok sexps -> toplevel sexps
  | Error err ->
    Result.fail @@ Error.of_thunk (fun () ->
        let pos = Parse_error.position err in
        let msg = Parse_error.message err in
        sprintf "at line %d, col %d: %s" pos.line pos.col msg)
*)
