open Core
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open Problem

(*val typeinf : print:(string lazy_t -> unit) -> t -> t*)
let typeinf ~print muclp =
  (* ToDo: infer types of mutually recursive predicates *)
  let senv =
    Map.Poly.map_keys_exn
      (Map.Poly.map (penv_of muclp) ~f:(fun sargs ->
           Sort.mk_fun (sargs @ [ T_bool.SBool ])))
      ~f:Ident.pvar_to_tvar
  in
  {
    preds =
      List.map muclp.preds ~f:(fun pred ->
          let args, body, _ =
            Formula.mk_forall pred.args pred.body
            |> Typeinf.typeinf_formula ~print ~senv
                 ~default:(Some T_int.SInt (*ToDo*))
            |> Formula.let_forall
          in
          { pred with args; body });
    query =
      Typeinf.typeinf_formula ~print ~senv ~default:(Some T_int.SInt (*ToDo*))
        muclp.query;
  }

(*val typeinf_query : print:(string lazy_t -> unit) -> query -> query*)
let typeinf_query ~print query =
  Typeinf.typeinf_formula ~print ~default:(Some T_int.SInt (*ToDo*)) query

(* The problem a [.hes] text denotes, with a closed query: a term variable the
   query mentions and no binder binds is universally quantified, the standard
   reading of the validity of an open formula, so [x < 0 \/ P x] is read as
   [forall x. x < 0 \/ P x].  The closing happens here, once, after type
   inference has given each free variable its sort, so that every engine
   receives a closed query; an engine that converted the open query for a
   constraint solver met the variable unbound and crashed, or gave up on it.
   Only the query is closed; a predicate body with a free term variable is
   refused instead ([Problem.refuse_free_body_vars] says why it has no
   reading of its own).  On a closed query and closed bodies this is the
   identity. *)
let parse_from_lexbuf ~print lexbuf =
  try
    Ok
      (Problem.elim_neg @@ Problem.bind_fvs_with_forall
     @@ Problem.refuse_free_body_vars @@ typeinf ~print
      @@ Parser.toplevel Lexer.main lexbuf)
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
  | Problem.Syntax_error error ->
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
  | Problem.Syntax_error error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error: %s"
              (LexingHelper.get_position_string lexbuf)
              error)
  | Lexer.SyntaxError error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error: %s"
              (LexingHelper.get_position_string lexbuf)
              error)

(* [split_datatype_prelude text]: the SMT-LIB [declare-datatypes] and
   [declare-datatype] commands that open [text], and [text] with each of them
   blanked.  Only a prelude counts: the scan skips blanks and this format's
   comments and stops at the first other character, so a command after the
   query is left to the grammar, which refuses it.  Blanking keeps every
   newline, so the grammar's positions are still the file's.  A command is
   delimited by balancing parentheses, skipping SMT-LIB's [|...|] symbols and
   [;] comments; an unbalanced one is left in place for the grammar to
   refuse. *)
let split_datatype_prelude text =
  let n = String.length text in
  let buf = Bytes.of_string text in
  let rec skip i =
    if i >= n then i
    else
      match text.[i] with
      | ' ' | '\t' | '\r' | '\n' -> skip (i + 1)
      | '/' when i + 1 < n && Char.equal text.[i + 1] '/' -> (
          match String.index_from text i '\n' with
          | Some j -> skip (j + 1)
          | None -> n)
      | '/' when i + 1 < n && Char.equal text.[i + 1] '*' -> (
          match String.substr_index ~pos:(i + 2) text ~pattern:"*/" with
          | Some j -> skip (j + 2)
          | None -> i)
      | _ -> i
  in
  (* the index just past the parenthesis closing the one at [i] *)
  let rec close depth i =
    if i >= n then None
    else
      match text.[i] with
      | '(' -> close (depth + 1) (i + 1)
      | ')' -> if depth = 1 then Some (i + 1) else close (depth - 1) (i + 1)
      | '|' -> (
          match String.index_from text (i + 1) '|' with
          | Some j -> close depth (j + 1)
          | None -> None)
      | ';' -> (
          match String.index_from text i '\n' with
          | Some j -> close depth (j + 1)
          | None -> None)
      | _ -> close depth (i + 1)
  in
  let is_decl i =
    let rest = String.drop_prefix text i in
    List.exists [ "declare-datatypes"; "declare-datatype" ] ~f:(fun cmd ->
        match String.chop_prefix rest ~prefix:"(" with
        | Some r -> (
            match String.chop_prefix (String.lstrip r) ~prefix:cmd with
            | Some r' ->
                String.is_empty r'
                || not (Char.is_alphanum r'.[0] || Char.equal r'.[0] '-')
            | None -> false)
        | None -> false)
  in
  let rec loop acc i =
    let i = skip i in
    if i < n && is_decl i then
      match close 0 i with
      | Some j ->
          for k = i to j - 1 do
            if not (Char.equal text.[k] '\n') then Bytes.set buf k ' '
          done;
          loop (String.sub text ~pos:i ~len:(j - i) :: acc) j
      | None -> List.rev acc
    else List.rev acc
  in
  let decls = loop [] 0 in
  (decls, Bytes.to_string buf)

(* Registers the datatypes a prelude declares in the process-wide
   environment, which the grammar reads to resolve constructors, selectors,
   testers and sorts, and which every later stage (the reductions, Z3's
   conversion) reads in turn.  The declarations are read by the SMT-LIB
   reader, so they mean exactly what they mean in an SMT-LIB file.  Each
   monomorphic datatype's size function ([SizeOf_<name>]) is registered as a
   known function as well, as the constraint reader does for an SMT-LIB
   input: a ranking template over a datatype-sorted argument is built from
   it, and a candidate mentioning a function the environment does not define
   has a free name and is refused.  This runs before any solver domain
   exists. *)
let register_datatypes ~print = function
  | [] -> ()
  | decls ->
      let _, (envs : SMT.Problem.envs) =
        SMT.Smtlib2.from_string ~print ~inline:false
          (String.concat ~sep:"\n" decls)
      in
      LogicOld.update_dtenv envs.dtenv;
      LogicOld.update_fenv @@ Z3Smt.Z3interface.generated_size_function_map
      @@ List.map ~f:LogicOld.Datatype.size_fun_of
      @@ List.filter (Map.Poly.data envs.dtenv)
           ~f:(Fn.non LogicOld.Datatype.is_poly)

let from_text ~print text =
  let decls, text = split_datatype_prelude text in
  match register_datatypes ~print decls with
  | () -> parse_from_lexbuf ~print (Lexing.from_string text)
  | exception exn_ when not (Common.Timer.is_async exn_) ->
      Result.fail
      @@ Error.of_string
           (sprintf "the datatype declarations could not be read: %s"
              (Exn.to_string exn_))

let from_file ~print filename = from_text ~print (In_channel.read_all filename)
let from_string ~print = from_text ~print

let query_from_string ~print =
  Lexing.from_string >> parse_query_from_lexbuf ~print

(* [get_dual_with_pairs muclp]: the dual problem (each fixpoint flipped, each
   body and the query negated with every predicate occurrence complemented),
   and the negations the simplifier made, as pairs (the negation as a formula,
   the simplifier's result), so that a caller can check each is an
   equivalence instead of trusting [Evaluator.simplify_neg]. *)
let get_dual_with_pairs muclp =
  let pvars = List.map muclp.preds ~f:(fun pred -> pred.name) in
  let pvars = Set.Poly.of_list pvars in
  let subst formula = Formula.subst_negs pvars formula in
  let pairs = ref [] in
  let neg phi =
    let phi' = Evaluator.simplify_neg phi in
    pairs := (Formula.mk_neg phi, phi') :: !pairs;
    phi'
  in
  let dual =
    make
      (List.map muclp.preds ~f:(fun pred ->
           {
             pred with
             kind = Predicate.flip_fop pred.kind;
             (* Detached bodies need the Boolean scope stored in pred.args. *)
             body =
               neg
                 (Formula.subst_negs_scoped pvars
                    (Term.complement_bound_nullaries Set.Poly.empty pred.args)
                    pred.body);
           }))
      (neg (subst muclp.query))
  in
  (dual, List.rev !pairs)

(*val get_dual : t -> t*)
let get_dual muclp = fst (get_dual_with_pairs muclp)

(*val get_greatest_approx : t -> t*)
let get_greatest_approx muclp =
  make
    (List.map muclp.preds ~f:(fun pred -> { pred with kind = Predicate.Nu }))
    muclp.query

(* Usage: let query, preds, _ = muclp_of_formula_with_env [] [] [] fml *)
(* Note: bound_tvars: term variables bound by fixpoint predicates *)
let rec of_formula_with_env preds env used_pvars bound_tvars =
  let open Formula in
  function
  | Atom (atom, info) as fml -> (
      match atom with
      | App (Fixpoint def, outer_args, info') ->
          (* (fp pvar(bounds). body)(args) *)
          let new_pvar = avoid_dup def.name used_pvars in
          let used_pvars = new_pvar :: used_pvars in
          let env = (def.name, new_pvar) :: env in
          let bound_tvars = Set.union bound_tvars (Set.Poly.of_list def.args) in
          let body, preds, used_pvars =
            of_formula_with_env preds env used_pvars bound_tvars def.body
          in

          let fvs_of_body = Formula.term_sort_env_of body in
          let additional_params =
            Set.to_list
            @@ Set.diff fvs_of_body
                 (Set.inter bound_tvars (Set.Poly.of_list def.args))
          in

          let new_bounds = def.args @ additional_params in
          let new_outer_args =
            outer_args @ Term.of_sort_env additional_params
          in
          let new_inner_args = Term.of_sort_env new_bounds in
          let new_sorts = List.map ~f:snd new_bounds in

          let new_pvar_app =
            Formula.mk_atom
            @@ Atom.mk_pvar_app new_pvar new_sorts new_inner_args
          in
          let new_arg_names = Pred.tvars_of_list new_bounds in
          let body =
            Formula.subst_preds
              (Map.Poly.singleton def.name (def.args, new_pvar_app))
              body
          in
          ( Formula.mk_atom ~info
            @@ Atom.mk_pvar_app new_pvar new_sorts new_outer_args ~info:info',
            Pred.make def.kind new_pvar new_bounds
              ~arg_original_names:new_arg_names body
            :: preds,
            used_pvars )
      | App (Var (pvar, sorts), args, info') ->
          ( Formula.mk_atom
              (Atom.mk_pvar_app
                 (List.Assoc.find_exn ~equal:Stdlib.( = ) env pvar)
                 sorts args ~info:info')
              ~info,
            preds,
            used_pvars )
      | _ -> (fml, preds, used_pvars))
  | UnaryOp (op, fml, info) ->
      let query, preds, used_pvars =
        of_formula_with_env preds env used_pvars bound_tvars fml
      in
      (Formula.mk_unop op query ~info, preds, used_pvars)
  | BinaryOp (op, lhs, rhs, info) ->
      let left_query, preds, used_pvars =
        of_formula_with_env preds env used_pvars bound_tvars lhs
      in
      let right_query, preds, used_pvars =
        of_formula_with_env preds env used_pvars bound_tvars rhs
      in
      (Formula.mk_binop op left_query right_query ~info, preds, used_pvars)
  | Bind (binder, bounds, body, info) ->
      let query, preds, used_pvars =
        of_formula_with_env preds env used_pvars bound_tvars body
      in
      (Formula.mk_bind binder bounds query ~info, preds, used_pvars)
  | LetRec (letrec_preds, body, _) ->
      let env, used_pvars =
        List.fold ~init:(env, used_pvars) letrec_preds
          ~f:(fun (env, used_pvars) def ->
            let new_pvar = avoid_dup def.name used_pvars in
            let used_pvars = new_pvar :: used_pvars in
            ((def.name, new_pvar) :: env, used_pvars))
      in
      let query, preds, used_pvars =
        of_formula_with_env preds env used_pvars bound_tvars body
      in
      let preds, used_pvars =
        List.fold ~init:(preds, used_pvars) letrec_preds
          ~f:(fun (preds, used_pvars) def ->
            let body, preds, used_pvars =
              of_formula_with_env preds env used_pvars bound_tvars def.body
            in
            ( Pred.make def.kind
                (List.Assoc.find_exn ~equal:Stdlib.( = ) env def.name)
                def.args
                ~arg_original_names:(Pred.tvars_of_list def.args)
                body
              :: preds,
              used_pvars ))
      in
      (query, preds, used_pvars)
  | LetFormula _ -> failwith @@ "'LetFormula' is not supported yet" (* TODO *)

(*val of_formula : Formula.t -> t*)
let of_formula phi =
  let query, preds, _ = of_formula_with_env [] [] [] Set.Poly.empty phi in
  make preds query

let rename_args group =
  let _, a1, _, _ = List.hd_exn group in
  match Set.to_list a1 with
  | [] ->
      List.map group ~f:(fun (senv, ps, ns, phi) ->
          assert (Set.is_empty ps);
          (senv, None, ns, Evaluator.simplify_neg phi))
  | [ Atom.App (Predicate.Var (_, sorts), _args0, _) ] ->
      let new_vars = mk_fresh_sort_env_list sorts in
      let args' = Term.of_sort_env new_vars in
      List.map group ~f:(fun (uni_senv, ps, ns, phi) ->
          match Set.to_list ps with
          | [ Atom.App (Predicate.Var (p, _), args, _) ] ->
              ( Map.force_merge uni_senv @@ Map.of_list_exn
                @@ Logic.of_old_sort_env_list new_vars,
                Some (p, new_vars),
                ns,
                Formula.and_of
                @@ Evaluator.simplify_neg phi
                   :: List.map2_exn args args' ~f:Formula.eq )
          | _ -> assert false)
  | _ -> assert false

(*val of_chc : ?only_pos:bool -> PCSP.Problem.t -> t*)
let of_chc ~print ?(only_pos = true) ?(fixpoints = []) chc =
  ignore print;
  (* A fixpoint-logic problem has no datatype or function environment, so what
     the constraint problem carries in its own would be dropped here and never
     reach the constraint problem this is reduced back to.  Register them in
     the process-wide environments instead, which is where every other front
     end puts them and where the conversion of a term for the solver reads them
     -- without this an input whose constructors are all declared in its own
     file ends in an uncaught failure naming a datatype, because the set the
     lookup searches has size zero.  The merging writer rather than the blind
     one: this runs before any solving, but the blind one would discard
     whatever else the process had registered. *)
  LogicOld.update_dtenv (PCSP.Problem.dtenv_of chc);
  LogicOld.update_fenv (PCSP.Problem.fenv_of chc);
  let chc = PCSP.Problem.(to_cnf @@ to_nnf chc) in
  let groups =
    chc |> PCSP.Problem.clauses_of
    |> Ast.ClauseSet.to_old_clause_set (PCSP.Problem.senv_of chc)
    |> Set.to_list
    |> List.classify (fun (_, ps1, _, _) (_, ps2, _, _) ->
        match (Set.to_list ps1, Set.to_list ps2) with
        | [], [] -> true
        | [ atm1 ], [ atm2 ] ->
            assert (Atom.is_pvar_app atm1 && Atom.is_pvar_app atm2);
            Ident.pvar_equal (Atom.pvar_of atm1) (Atom.pvar_of atm2)
        | _, _ -> false)
    |> List.map ~f:rename_args
  in
  let goals, defs =
    List.partition_tf groups ~f:(function
      | [] -> assert false
      | (_senv, p, _ns, _phi) :: _group -> Option.is_none p)
  in
  let preds =
    List.map defs ~f:(function
      | (_, Some (p, args), _, _) :: _ as group ->
          Pred.make Predicate.Mu p args
            (Normalizer.normalize @@ Evaluator.simplify @@ Formula.or_of
            @@ List.map group ~f:(fun (senv, _, ns, phi) ->
                let phi =
                  Formula.and_of
                  @@ Evaluator.simplify phi
                     :: List.map (Set.to_list ns) ~f:Formula.mk_atom
                in
                let senv =
                  Map.Poly.filter_keys senv ~f:(Set.mem @@ Formula.fvs_of phi)
                in
                let senv, phi =
                  Tuple2.map_snd ~f:Evaluator.simplify_neg
                  @@ Ast.Qelim.elim_free_univ_vars_old
                       (Map.of_list_exn @@ Logic.ExtTerm.of_old_sort_env args)
                       (PCSP.Problem.senv_of chc)
                       (senv, Evaluator.simplify_neg phi)
                in
                let unbound =
                  Map.to_alist @@ Logic.to_old_sort_env_map
                  @@ Map.Poly.filter_keys senv
                       ~f:(Fn.non @@ List.Assoc.mem ~equal:Stdlib.( = ) args)
                in
                Formula.exists unbound phi))
      | _ -> assert false)
  in
  let query =
    match goals with
    | [] -> Formula.mk_false ()
    | [ goals ] ->
        Normalizer.normalize @@ Evaluator.simplify @@ Formula.or_of
        @@ List.map goals ~f:(fun (senv, _, ns, phi) ->
            let senv, phi =
              let phi =
                Formula.and_of
                @@ Evaluator.simplify phi
                   :: List.map (Set.to_list ns) ~f:Formula.mk_atom
              in
              let senv =
                Map.Poly.filter_keys senv
                  ~f:(Set.mem @@ Formula.tvs_of phi (*ToDo:also use pvs?*))
              in
              Tuple2.map_snd ~f:Evaluator.simplify_neg
              @@ Ast.Qelim.elim_free_univ_vars_old Map.Poly.empty
                   (PCSP.Problem.senv_of chc)
                   (senv, Evaluator.simplify_neg phi)
            in
            let unbound =
              Logic.to_old_sort_env_list @@ Map.Poly.to_alist senv
            in
            Formula.exists unbound phi)
    | _ -> assert false
  in
  let fixpoint_names =
    List.map fixpoints ~f:(fun (pred : Pred.t) -> pred.name)
  in
  let undef_preds =
    let def_preds =
      List.map preds ~f:(fun pred -> pred.name) @ fixpoint_names
    in
    PCSP.Problem.senv_of chc
    |> Map.Poly.filter_keys
         ~f:(Ident.tvar_to_pvar >> List.mem def_preds ~equal:Stdlib.( = ) >> not)
    |> Map.Poly.mapi ~f:(fun ~key:(Ident.Tvar n) ~data ->
        let sorts =
          List.map ~f:Logic.ExtTerm.to_old_sort @@ Logic.Sort.args_of data
        in
        let args sorts =
          let flag = ref 0 in
          List.map sorts ~f:(fun sort ->
              flag := !flag + 1;
              (Ident.Tvar ("x" ^ string_of_int !flag), sort))
        in
        Pred.make Predicate.Mu (*ToDo*) (Ident.Pvar n) (args sorts)
          (Formula.mk_false ()))
    |> Map.Poly.data
  in
  (* a predicate a fixpoint definition applies that neither a clause nor a
     definition defines: as for [undef_preds], the least fixpoint [false] *)
  let undef_body_preds =
    let known =
      Set.Poly.of_list
      @@ List.map preds ~f:(fun pred -> pred.name)
      @ List.map undef_preds ~f:(fun pred -> pred.name)
      @ fixpoint_names
    in
    fixpoints
    |> List.concat_map ~f:(fun (pred : Pred.t) ->
        Set.to_list @@ Formula.pred_sort_env_of pred.body)
    |> List.dedup_and_sort ~compare:Stdlib.compare
    |> List.filter ~f:(fun (p, _) -> not (Set.mem known p))
    |> List.map ~f:(fun (p, sorts) ->
        Pred.make Predicate.Mu p
          (List.mapi sorts ~f:(fun i sort ->
               (Ident.Tvar ("x" ^ string_of_int (i + 1)), sort)))
          (Formula.mk_false ()))
  in
  let preds = preds @ undef_preds @ undef_body_preds @ fixpoints in
  if only_pos then get_dual @@ make preds query
  else make preds (Evaluator.simplify_neg query)

(* [of_chc_with_fixpoints ~print ~fixpoints chc] is the fixpoint-logic validity
   problem equivalent to the satisfiability of [chc] when the predicates named
   by [fixpoints] are not unknowns but are interpreted by those least and
   greatest fixpoint definitions, whose bodies may apply the unknowns of [chc]
   and each other.  [Error reason] when the shape the equivalence needs is not
   there; nothing is approximated.

   The equivalence, for each model of the background theory: write U for the
   unknowns and F(U) for the fixpoint predicates as functions of them.  When
   (1) every unknown is ordinary (no kind), (2) every clause has at most one
   positive unknown and no positive fixpoint predicate, and (3) every
   predicate applied in a fixpoint body occurs there positively, the clauses
   with a positive unknown define a monotone operator on U (the fixpoint
   predicates in their bodies are monotone in U by (3)), and the other clauses
   are antitone in U.  So a U satisfying all clauses is a prefixed point of
   the operator and lies above its least fixpoint U*, at which the antitone
   clauses then hold too; conversely U* satisfies the defining clauses.  The
   clauses are satisfiable iff they hold at U*.  The equation system puts the
   unknowns' least-fixpoint equations first, which is outermost, and the
   fixpoint definitions after them, so each fixpoint predicate is read as a
   function of U and U* is the least fixpoint of the composed operator.  The
   definitions are ordered so that a definition precedes the definitions it
   applies, and (4) a least and a greatest definition never apply each other
   mutually, so each mutually recursive group is of one kind and its place
   among the others does not change what it denotes.  Definitions no clause
   reaches are dropped.  The problem is built as [of_chc] builds it, with the
   same dual on the way out. *)
let of_chc_with_fixpoints ~print ~(fixpoints : Pred.t list) chc =
  let open Result.Monad_infix in
  let fpvs = Set.Poly.of_list @@ List.map fixpoints ~f:(fun p -> p.Pred.name) in
  let def_of =
    Map.Poly.of_alist_reduce
      ~f:(fun p _ -> p)
      (List.map fixpoints ~f:(fun p -> (p.Pred.name, p)))
  in
  (match
     List.filter (PCSP.Problem.non_ord_kinds_of chc) ~f:(fun (v, _) ->
         not (Set.mem fpvs (Ident.tvar_to_pvar v)))
   with
    | [] -> Ok ()
    | (v, k) :: _ ->
        Error
          (sprintf "the unknown %s has the kind %s" (Ident.name_of_tvar v)
             (Kind.str_of k)))
  >>= fun () ->
  let clauses =
    let chc = PCSP.Problem.(to_cnf @@ to_nnf chc) in
    chc |> PCSP.Problem.clauses_of
    |> Ast.ClauseSet.to_old_clause_set (PCSP.Problem.senv_of chc)
    |> Set.to_list
  in
  (match
     List.find_map clauses ~f:(fun (_, ps, _, _) ->
         if Set.length ps > 1 then Some "a clause has two positive unknowns"
         else
           Set.find_map ps ~f:(fun atm ->
               if Atom.is_pvar_app atm && Set.mem fpvs (Atom.pvar_of atm) then
                 Some
                   (sprintf
                      "the fixpoint predicate %s occurs positively in a clause"
                      (Ident.name_of_pvar (Atom.pvar_of atm)))
               else None))
   with
    | None -> Ok ()
    | Some reason -> Error reason)
  >>= fun () ->
  (match
     List.find_map fixpoints ~f:(fun (pred : Pred.t) ->
         let negative = ref [] in
         match
           Formula.map_atom_polarity pred.body true ~f:(fun polarity atm ->
               if (not polarity) && Atom.is_pvar_app atm then
                 negative := Atom.pvar_of atm :: !negative;
               Formula.mk_atom atm)
         with
         | exception exn_ when not (Common.Timer.is_async exn_) ->
             Some
               (sprintf "the polarity of the body of %s cannot be read"
                  (Ident.name_of_pvar pred.name))
         | _ -> (
             match !negative with
             | [] -> None
             | p :: _ ->
                 Some
                   (sprintf "%s occurs negatively in the body of %s"
                      (Ident.name_of_pvar p)
                      (Ident.name_of_pvar pred.name))))
   with
    | None -> Ok ()
    | Some reason -> Error reason)
  >>= fun () ->
  let uses p =
    match Map.Poly.find def_of p with
    | None -> Set.Poly.empty
    | Some (pred : Pred.t) -> Set.inter fpvs @@ Formula.pvs_of pred.body
  in
  let reach_from roots =
    let rec go seen = function
      | [] -> seen
      | p :: ps ->
          if Set.mem seen p then go seen ps
          else go (Set.add seen p) (Set.to_list (uses p) @ ps)
    in
    go Set.Poly.empty (Set.to_list roots)
  in
  let reached =
    reach_from @@ Set.inter fpvs @@ Set.Poly.union_list
    @@ List.map clauses ~f:(fun (_, ps, ns, _) ->
        Set.Poly.map ~f:Atom.pvar_of
        @@ Set.filter ~f:Atom.is_pvar_app (Set.union ps ns))
  in
  (match
     Set.find_map reached ~f:(fun p ->
         let kp = (Map.Poly.find_exn def_of p).Pred.kind in
         Set.find_map
           (reach_from (uses p))
           ~f:(fun q ->
             let kq = (Map.Poly.find_exn def_of q).Pred.kind in
             if Stdlib.(kp <> kq) && Set.mem (reach_from (uses q)) p then
               Some
                 (sprintf
                    "%s and %s, of different fixpoint kinds, apply each other"
                    (Ident.name_of_pvar p) (Ident.name_of_pvar q))
             else None))
   with
    | None -> Ok ()
    | Some reason -> Error reason)
  >>= fun () ->
  (* A guard, not a condition of the equivalence: every unknown a reached
     definition applies has a defining clause.  One without is interpreted as
     [false], which is exact for the clauses as given, but every disjunct of a
     definition through it is then vacuous, and that is how a constraint the
     generator lost shows itself: a definition that cannot hold makes the
     goals over it hold, and the answer would be a proof about a problem that
     is not the program's.  Declining costs an answer, never a wrong one. *)
  (let defined =
     Set.Poly.of_list
     @@ List.concat_map clauses ~f:(fun (_, ps, _, _) ->
         List.map ~f:Atom.pvar_of
         @@ List.filter ~f:Atom.is_pvar_app (Set.to_list ps))
   in
   match
     Set.find_map reached ~f:(fun p ->
         Set.find (Formula.pvs_of (Map.Poly.find_exn def_of p).Pred.body)
           ~f:(fun q -> (not (Set.mem fpvs q)) && not (Set.mem defined q))
         |> Option.map ~f:(fun q ->
             sprintf
               "the unknown %s, applied in the definition of %s, has no \
                defining clause"
               (Ident.name_of_pvar q) (Ident.name_of_pvar p)))
   with
   | None -> Ok ()
   | Some reason -> Error reason)
  >>= fun () ->
  (* reverse postorder of the depth-first search along [uses]: a definition
     before the definitions it applies *)
  let ordered =
    let visited = ref Set.Poly.empty in
    let post = ref [] in
    let rec visit p =
      if not (Set.mem !visited p) then (
        visited := Set.add !visited p;
        Set.iter (uses p) ~f:visit;
        post := p :: !post)
    in
    List.iter fixpoints ~f:(fun (pred : Pred.t) ->
        if Set.mem reached pred.name then visit pred.name);
    List.map !post ~f:(Map.Poly.find_exn def_of)
  in
  Ok (of_chc ~print ~fixpoints:ordered chc)

(*val of_lts :
    ?live_vars:(string -> sort_env_set) option ->
    ?cut_points:string Set.Poly.t option ->
    LTS.Problem.t ->
    t*)
let rec of_lts ~print ?(live_vars = None) ?(cut_points = None) = function
  | lts, LTS.Problem.Term -> (
      let ( start,
            (*ignored*) _types,
            (*ignored*) _error,
            (*ignored*) _cutpoint,
            transitions,
            (*ignored*) _buchi ) =
        lts
      in
      let pvar_of s = Ident.Pvar ("state_" ^ s) in
      let tenv_of =
        match live_vars with
        | None ->
            let tenv =
              Set.to_list
              @@ Set.filter
                   ~f:
                     (fst >> Ident.name_of_tvar
                     >> String.is_prefix ~prefix:LTS.Problem.nondet_prefix
                     >> not)
              @@ LTS.Problem.term_sort_env_of lts
            in
            fun _ -> tenv
        | Some live_vars -> (
            fun s ->
              try Set.to_list (live_vars s)
              with Stdlib.Not_found -> failwith ("not found: " ^ s))
      in
      print @@ lazy (sprintf "LTS:\n%s" @@ LTS.Problem.str_of_lts lts);
      (* with COAR_SHARE_CENSUS set, the sharing of the transitions and of
         each step's outputs over all of them (an instrument: the values are
         only held longer) *)
      let census_wp = ref [] and census_simp = ref [] and census_norm = ref [] in
      let census_keep r l =
        if Common.DagCensus.enabled then r := l :: !r;
        l
      in
      let census_keep1 r x = if Common.DagCensus.enabled then r := x :: !r in
      Common.DagCensus.report
        ~items:(List.length transitions)
        "of_lts: transitions" transitions;
      let preds_nu, preds_mu =
        transitions
        |> List.classify (fun (s1, _, _) (s2, _, _) -> String.(s1 = s2))
        |> List.partition_map ~f:(function
          | [] -> assert false
          | (from, c, to_) :: trs -> (
              let next =
                (c, to_) :: List.map trs ~f:(fun (_, c, to_) -> (c, to_))
                |> List.map ~f:(fun (c, to_) ->
                    let pvar = pvar_of to_ in
                    let senv = tenv_of to_ in
                    Common.PhaseTime.with_phase "wp" @@ fun () ->
                    LTS.Problem.wp c
                      (Formula.mk_atom @@ Atom.pvar_app_of_senv pvar senv))
                |> census_keep census_wp
                |> Formula.and_of
                |> fun phi ->
                Common.PhaseTime.with_phase "simplify" @@ fun () ->
                let phi = Evaluator.simplify phi in
                census_keep1 census_simp phi;
                let phi = Normalizer.normalize phi in
                census_keep1 census_norm phi;
                phi
              in
              match cut_points with
              | Some cut_points when not @@ Set.mem cut_points from ->
                  First
                    (let sort_env_list = tenv_of from in
                     let arg_original_names =
                       Pred.tvars_of_list sort_env_list
                     in
                     Pred.make Predicate.MuOrNu (pvar_of from) sort_env_list
                       ~arg_original_names (* Insert metadata around here *)
                       next)
              | _ ->
                  Second
                    (let sort_env_list = tenv_of from in
                     let arg_original_names =
                       Pred.tvars_of_list sort_env_list
                     in
                     Pred.make Predicate.Mu (pvar_of from) sort_env_list
                       ~arg_original_names next)))
      in
      Common.DagCensus.report "of_lts: after wp" !census_wp;
      Common.DagCensus.report "of_lts: after simplify" !census_simp;
      Common.DagCensus.report "of_lts: after normalize" !census_norm;
      match start with
      | None ->
          assert (List.is_empty transitions);
          make [] (Formula.mk_true ())
      | Some start ->
          let undef_preds =
            Set.diff
              (Set.add (Set.Poly.of_list @@ List.map transitions ~f:trd3) start)
              (Set.Poly.of_list @@ List.map transitions ~f:fst3)
            |> Set.Poly.map ~f:(fun from ->
                let sort_env_list = tenv_of from in
                let arg_original_names = Pred.tvars_of_list sort_env_list in
                Pred.make Predicate.MuOrNu (pvar_of from) sort_env_list
                  ~arg_original_names (Formula.mk_true ()))
            |> Set.to_list
          in
          let query =
            let tenv = tenv_of start in
            Formula.mk_forall_if_bounded tenv
            @@ Formula.mk_atom
            @@ Atom.pvar_app_of_senv (pvar_of start) tenv
          in
          (*typeinf ~print:Debug.print
            @@*)
          make (preds_mu @ preds_nu @ undef_preds) query)
  | lts, LTS.Problem.NonTerm ->
      get_dual @@ of_lts ~print ~live_vars ~cut_points (lts, LTS.Problem.Term)
  | lts, LTS.Problem.Safe -> (
      let ( start,
            (*ignored*) _types,
            error,
            (*ignored*) _cutpoint,
            transitions,
            (*ignored*) _buchi ) =
        lts
      in
      let pvar_of s = Ident.Pvar ("state_" ^ s) in
      let tenv_of =
        match live_vars with
        | None ->
            let tenv =
              Set.to_list
              @@ Set.filter
                   ~f:
                     (fst >> Ident.name_of_tvar
                     >> String.is_prefix ~prefix:LTS.Problem.nondet_prefix
                     >> not)
              @@ LTS.Problem.term_sort_env_of lts
            in
            fun _ -> tenv
        | Some live_vars -> (
            fun s ->
              try Set.to_list (live_vars s)
              with Stdlib.Not_found -> failwith ("not found: " ^ s))
      in
      print @@ lazy (sprintf "LTS:\n%s" @@ LTS.Problem.str_of_lts lts);
      let preds_nu, preds_mu =
        transitions
        |> List.classify (fun (s1, _, _) (s2, _, _) -> String.(s1 = s2))
        |> List.partition_map ~f:(function
          | [] -> assert false
          | (from, c, to_) :: trs -> (
              let next =
                (c, to_) :: List.map trs ~f:(fun (_, c, to_) -> (c, to_))
                |> List.map ~f:(fun (c, to_) ->
                    let post =
                      match error with
                      | Some error_state when String.(to_ = error_state) ->
                          Formula.mk_false ()
                      | _ ->
                          let pvar = pvar_of to_ in
                          let senv = tenv_of to_ in
                          Formula.mk_atom @@ Atom.pvar_app_of_senv pvar senv
                    in
                    LTS.Problem.wp c post)
                |> Formula.and_of |> Evaluator.simplify |> Normalizer.normalize
              in
              match cut_points with
              | Some cut_points when not @@ Set.mem cut_points from ->
                  First
                    (let sort_env_list = tenv_of from in
                     let arg_original_names =
                       Pred.tvars_of_list sort_env_list
                     in
                     Pred.make Predicate.MuOrNu (pvar_of from) sort_env_list
                       ~arg_original_names next)
              | _ ->
                  Second
                    (let sort_env_list = tenv_of from in
                     let arg_original_names =
                       Pred.tvars_of_list sort_env_list
                     in
                     Pred.make Predicate.Nu (pvar_of from) sort_env_list
                       ~arg_original_names next)))
      in
      match start with
      | None ->
          assert (List.is_empty transitions);
          make [] (Formula.mk_true ())
      | Some start ->
          let undef_preds =
            Set.diff
              (Set.add (Set.Poly.of_list @@ List.map transitions ~f:trd3) start)
              (Set.Poly.of_list @@ List.map transitions ~f:fst3)
            |> Set.Poly.map ~f:(fun from ->
                let sort_env_list = tenv_of from in
                let arg_original_names = Pred.tvars_of_list sort_env_list in
                Pred.make Predicate.MuOrNu (pvar_of from) sort_env_list
                  ~arg_original_names (Formula.mk_true ()))
            |> Set.to_list
          in
          let query =
            let tenv = tenv_of start in
            Formula.mk_forall_if_bounded tenv
            @@ Formula.mk_atom
            @@ Atom.pvar_app_of_senv (pvar_of start) tenv
          in
          make (preds_mu @ preds_nu @ undef_preds) query)
  | lts, LTS.Problem.NonSafe ->
      get_dual @@ of_lts ~print ~live_vars ~cut_points (lts, LTS.Problem.Safe)
  | lts, LTS.Problem.Buchi ->
      universal_parity ~print ~live_vars ~cut_points ~accepting:Predicate.Nu
        ~rejecting:Predicate.Mu lts
  | lts, LTS.Problem.ExBuchi ->
      (* some run visits B infinitely often iff not every run visits it
         finitely often: the dual of the universal co-Buechi system *)
      get_dual
      @@ universal_parity ~print ~live_vars ~cut_points ~accepting:Predicate.Mu
           ~rejecting:Predicate.Nu lts
  | _, LTS.Problem.(MuCal | Rel) -> failwith "not implemented"

(* [universal_parity ~accepting ~rejecting lts]: the muCLP system stating that
   every run of [lts] from an initial state satisfies the parity condition
   with two priorities, the [BUCHI] locations B at the higher one.  Each
   location l has one predicate [state_l] over its live variables, defined as
   the conjunction over l's transitions of the weakest precondition of the
   successor's predicate (the universal next-state operator); a location
   without transitions is [true], since no run passes it.
   - [~accepting:Nu ~rejecting:Mu]: every run visits B infinitely often
     (Buechi).  The equations of B come first (outermost), as greatest
     fixpoints, those of the other cut points after them as least fixpoints:
     the standard reduction of a parity condition to a hierarchical equation
     system, each location's equation at the location's priority, the higher
     priority outermost.  Max-parity: B at 2, the rest at 1.
   - [~accepting:Mu ~rejecting:Nu]: every run visits B only finitely often
     (co-Buechi; B at 1, the rest at 0).
   Locations that are not cut points are [MuOrNu] and come after every cut
   point: every cycle through one passes a cut point, so it decides no
   run's parity.  This holds only because B is added to the cut points
   (a cycle through a B location then has that location's own equation,
   at the higher priority, on it) and because [LTS.Problem.analyze] keeps
   every B location as a vertex.  The query is [forall x. state_start(x)]. *)
and universal_parity ~print ~live_vars ~cut_points ~accepting ~rejecting lts =
  let start, _types, _error, _cutpoint, transitions, buchi = lts in
  let buchi =
    match buchi with
    | Some b -> Set.Poly.of_list b
    | None ->
        Common.Refusal.refuse
          "a Buechi mode needs a BUCHI line naming the Buechi locations"
  in
  let pvar_of s = Ident.Pvar ("state_" ^ s) in
  let tenv_of =
    match live_vars with
    | None ->
        let tenv =
          Set.to_list
          @@ Set.filter
               ~f:
                 (fst >> Ident.name_of_tvar
                 >> String.is_prefix ~prefix:LTS.Problem.nondet_prefix
                 >> not)
          @@ LTS.Problem.term_sort_env_of lts
        in
        fun _ -> tenv
    | Some live_vars -> (
        fun s ->
          try Set.to_list (live_vars s)
          with Stdlib.Not_found -> failwith ("not found: " ^ s))
  in
  let cut_points = Option.map cut_points ~f:(Set.union buchi) in
  print @@ lazy (sprintf "LTS:\n%s" @@ LTS.Problem.str_of_lts lts);
  let classified =
    transitions
    |> List.classify (fun (s1, _, _) (s2, _, _) -> String.(s1 = s2))
    |> List.map ~f:(function
      | [] -> assert false
      | (from, _, _) :: _ as trs ->
          let body =
            List.map trs ~f:(fun (_, c, to_) ->
                Common.PhaseTime.with_phase "wp" @@ fun () ->
                LTS.Problem.wp c
                  (Formula.mk_atom
                  @@ Atom.pvar_app_of_senv (pvar_of to_) (tenv_of to_)))
            |> Formula.and_of
            |> fun phi ->
            Common.PhaseTime.with_phase "simplify" @@ fun () ->
            Normalizer.normalize @@ Evaluator.simplify phi
          in
          let kind, rank =
            match cut_points with
            | Some cps when not (Set.mem cps from) -> (Predicate.MuOrNu, 2)
            | _ -> if Set.mem buchi from then (accepting, 0) else (rejecting, 1)
          in
          let senv = tenv_of from in
          ( rank,
            Pred.make kind (pvar_of from) senv
              ~arg_original_names:(Pred.tvars_of_list senv) body ))
  in
  let ordered rank =
    List.filter_map classified ~f:(fun (r, p) ->
        if r = rank then Some p else None)
  in
  match start with
  | None ->
      assert (List.is_empty transitions);
      make [] (Formula.mk_true ())
  | Some start ->
      let undef_preds =
        Set.diff
          (Set.add (Set.Poly.of_list @@ List.map transitions ~f:trd3) start)
          (Set.Poly.of_list @@ List.map transitions ~f:fst3)
        |> Set.Poly.map ~f:(fun from ->
            let senv = tenv_of from in
            Pred.make Predicate.MuOrNu (pvar_of from) senv
              ~arg_original_names:(Pred.tvars_of_list senv) (Formula.mk_true ()))
        |> Set.to_list
      in
      let query =
        let tenv = tenv_of start in
        Formula.mk_forall_if_bounded tenv
        @@ Formula.mk_atom
        @@ Atom.pvar_app_of_senv (pvar_of start) tenv
      in
      make (ordered 0 @ ordered 1 @ ordered 2 @ undef_preds) query
