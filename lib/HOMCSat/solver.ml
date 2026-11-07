(* HOMCSat: decides higher-order Boolean satisfiability (and, through it,
   SAT and DQSAT) by higher-order model checking, after Hiroshi Unno, Takeshi
   Tsukada and Jie-Hong Roland Jiang, "Solving Higher-Order Quantified Boolean
   Satisfiability via Higher-Order Model Checking", AAAI 2025.

   [homc_of_hosat] translates the formula into a recursion scheme whose tree
   is the formula's Boolean evaluation tree: a quantifier over [Bool] becomes a
   conjunction or disjunction of its two instances, and a quantifier over a
   function sort enumerates every function of that finite sort with
   generated [Zero]/[Succ]/[IsMax] rules.  The specification is a fixed
   alternating tree automaton whose state [qT] accepts exactly the trees that
   evaluate to true, so the HORS satisfies it iff the formula is true.  The
   answer of the configured model checker is mapped back verbatim; a [Sat]
   SAT answer carries no model, and [incremental_solve] is not implemented. *)
open Core
open Common
open Common.Ext
open Common.Util

module type SolverType = sig
  val solve :
    ?print_sol:bool -> SAT.Problem.t -> SAT.Problem.solution Or_error.t

  val incremental_solve : ?print_sol:bool -> SAT.Problem.t -> SAT.Problem.incsol

  val solve_dqsat :
    ?print_sol:bool -> DQSAT.Problem.t -> DQSAT.Problem.solution Or_error.t

  val solve_hosat :
    ?print_sol:bool -> HOSAT.Problem.t -> HOSAT.Problem.solution Or_error.t

  val homc_of_hosat : HOSAT.Problem.t -> HOMC.Problem.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let solver =
    let open Or_error in
    ExtFile.unwrap config.solver >>= fun cfg -> Ok (HOMCSolver.Solver.make cfg)

  let homc_of_hosat hosat =
    let spec_arity =
      [
        ("tt", 0);
        ("ff", 0);
        ("not", 1);
        ("and", 2);
        ("or", 2);
        ("imply", 2);
        ("iff", 2);
        ("xor", 2);
        ("if", 3);
      ]
    in
    let spec_rules =
      Automata.ATA.make
        [
          ("qT", ("tt", [ [] ]));
          ("qT", ("ff", []));
          ("qT", ("not", [ [ (1, "qF") ] ]));
          ("qT", ("and", [ [ (1, "qT"); (2, "qT") ] ]));
          ("qT", ("or", [ [ (1, "qT") ]; [ (2, "qT") ] ]));
          ("qT", ("imply", [ [ (1, "qF") ]; [ (2, "qT") ] ]));
          ("qT", ("iff", [ [ (1, "qT"); (2, "qT") ]; [ (1, "qF"); (2, "qF") ] ]));
          ("qT", ("xor", [ [ (1, "qT"); (2, "qF") ]; [ (1, "qF"); (2, "qT") ] ]));
          ("qT", ("if", [ [ (1, "qT"); (2, "qT") ]; [ (1, "qF"); (3, "qT") ] ]));
          ("qF", ("tt", []));
          ("qF", ("ff", [ [] ]));
          ("qF", ("not", [ [ (1, "qT") ] ]));
          ("qF", ("and", [ [ (1, "qF") ]; [ (2, "qF") ] ]));
          ("qF", ("or", [ [ (1, "qF"); (2, "qF") ] ]));
          ("qF", ("imply", [ [ (1, "qT"); (2, "qF") ] ]));
          ("qF", ("iff", [ [ (1, "qT"); (2, "qF") ]; [ (1, "qF"); (2, "qT") ] ]));
          ("qF", ("xor", [ [ (1, "qT"); (2, "qT") ]; [ (1, "qF"); (2, "qF") ] ]));
          ("qF", ("if", [ [ (1, "qT"); (2, "qF") ]; [ (1, "qF"); (3, "qF") ] ]));
        ]
    in
    let rules =
      let open Ast.Logic in
      let open HOMC in
      let tt = RSFD.Term (Ast.Ident.Tvar "tt") in
      let ff = RSFD.Term (Ast.Ident.Tvar "ff") in
      let bnot = RSFD.Term (Ast.Ident.Tvar "not") in
      let band = RSFD.Term (Ast.Ident.Tvar "and") in
      let bor = RSFD.Term (Ast.Ident.Tvar "or") in
      let bimply = RSFD.Term (Ast.Ident.Tvar "imply") in
      let biff = RSFD.Term (Ast.Ident.Tvar "iff") in
      let bxor = RSFD.Term (Ast.Ident.Tvar "xor") in
      let bif = RSFD.Term (Ast.Ident.Tvar "if") in
      let rec str_of_sort = function
        | BoolTerm.SBool -> "B"
        | Sort.SArrow (BoolTerm.SBool, c) -> "B" ^ str_of_sort c.val_type
        | Sort.SArrow (s, c) ->
            "L" ^ str_of_sort s ^ "R" ^ str_of_sort c.val_type
        | _ -> failwith "not supported"
      in
      let zero s = Ast.Ident.Tvar ("Zero" ^ str_of_sort s) in
      let ismax s = Ast.Ident.Tvar ("IsMax" ^ str_of_sort s) in
      let ismaxrec s = Ast.Ident.Tvar ("IsMaxRec" ^ str_of_sort s) in
      let succ s = Ast.Ident.Tvar ("Succ" ^ str_of_sort s) in
      let find s = Ast.Ident.Tvar ("Find" ^ str_of_sort s) in
      let carry s = Ast.Ident.Tvar ("Carry" ^ str_of_sort s) in
      let compare s = Ast.Ident.Tvar ("Compare" ^ str_of_sort s) in
      let zero_of s = RSFD.Nonterm (zero s) in
      let ismax_of s = RSFD.Nonterm (ismax s) in
      let ismaxrec_of s = RSFD.Nonterm (ismaxrec s) in
      let succ_of s = RSFD.Nonterm (succ s) in
      let find_of s = RSFD.Nonterm (find s) in
      let carry_of s = RSFD.Nonterm (carry s) in
      let compare_of s = RSFD.Nonterm (compare s) in
      let input = HOSAT.Problem.term_of hosat in
      (* A bound variable becomes a parameter of the generated rules, which
         the model checker reads by its spelling: a parameter spelled like a
         terminal ([and], [or], [xor], ...) would be confused with it, and one
         that is not an identifier of the scheme's syntax (the [#tvar] names
         capture-avoiding substitution draws, a prime) cannot be read at all,
         and one that shadows an enclosing binder of the same name would make
         a rule with two parameters of one name, so the inner reference could
         be read as the outer value.  Such a binder is renamed apart from
         every name of the input; all other names are kept, so the scheme
         stays readable.  Nonterminals are capitalised and cannot coincide
         with a parameter. *)
      let input_names =
        let rec names acc = function
          | Var (x, _) -> Set.add acc x
          | Con _ -> acc
          | App (t1, t2, _) -> names (names acc t1) t2
          | Bin (_, x, _, t, _) -> names (Set.add acc x) t
          | Let (x, _, t1, t2, _) -> names (names (Set.add acc x) t1) t2
          | TyApp (t, _, _) | TyLam (_, t, _) -> names acc t
        in
        names Set.Poly.empty input
      in
      let binder senv tvar t =
        let s = Ast.Ident.name_of_tvar tvar in
        if
          (not (List.Assoc.mem senv ~equal:Ast.Ident.tvar_equal tvar))
          && (not (String.is_empty s))
          && Char.is_lowercase s.[0]
          && String.for_all s ~f:(fun c -> Char.is_alphanum c || Char.equal c '_')
          && not (List.Assoc.mem spec_arity ~equal:String.equal s)
        then (tvar, t)
        else
          let tvar' =
            Ast.Ident.mk_fresh_tvar_avoiding ~prefix:"v"
              ~taken:(Set.mem input_names) ()
          in
          (tvar', Term.rename (Map.Poly.singleton tvar tvar') t)
      in
      (* [aux senv (t, args)] translates the application of [t] to [args]
         under the binders [senv] (outermost first), each of which is a
         parameter of every rule generated below it.  It assumes every
         variable of [t] and [args] is bound in [senv] and that a variable of
         sort [bool] is not applied: the input is closed below, and a variable
         that is free anyway would be printed as a name the scheme does not
         declare, which the model checker reads as an unknown tree constructor
         rather than as a quantified value, so it is refused instead. *)
      let rec aux senv = function
        | Var (x, _), args ->
            (match List.Assoc.find senv ~equal:Ast.Ident.tvar_equal x with
            | None ->
                failwithf "[aux] variable %s is not bound by a quantifier"
                  (Ast.Ident.name_of_tvar x) ()
            | Some BoolTerm.SBool when not (List.is_empty args) ->
                failwithf "[aux] the Boolean variable %s is applied to %d \
                           argument(s)"
                  (Ast.Ident.name_of_tvar x) (List.length args) ()
            | Some _ -> ());
            let ts, ruless, sortss =
              List.unzip3 @@ List.map args ~f:(fun t -> aux senv (t, []))
            in
            ( RSFD.apps (RSFD.Var x) ts,
              List.concat ruless,
              Set.Poly.union_list sortss )
        | Con (BoolTerm.True, _), [] -> (tt, [], Set.Poly.empty)
        | Con (BoolTerm.False, _), [] -> (ff, [], Set.Poly.empty)
        | Con (BoolTerm.Not, _), [ t1 ] ->
            let t1, rules1, sorts1 = aux senv (t1, []) in
            (RSFD.apps bnot [ t1 ], rules1, sorts1)
        | Con (BoolTerm.And, _), [ t1; t2 ] ->
            let t1, rules1, sorts1 = aux senv (t1, []) in
            let t2, rules2, sorts2 = aux senv (t2, []) in
            (RSFD.apps band [ t1; t2 ], rules1 @ rules2, Set.union sorts1 sorts2)
        | Con (BoolTerm.Or, _), [ t1; t2 ] ->
            let t1, rules1, sorts1 = aux senv (t1, []) in
            let t2, rules2, sorts2 = aux senv (t2, []) in
            (RSFD.apps bor [ t1; t2 ], rules1 @ rules2, Set.union sorts1 sorts2)
        | Con (BoolTerm.Imply, info), [ t1; t2 ] ->
            if config.encode_bool_ops then
              (* t1 => t2 -> (not t1 or t2) *)
              aux senv (Con (BoolTerm.Or, info), [ BoolTerm.neg_of t1; t2 ])
            else
              let t1, rules1, sorts1 = aux senv (t1, []) in
              let t2, rules2, sorts2 = aux senv (t2, []) in
              ( RSFD.apps bimply [ t1; t2 ],
                rules1 @ rules2,
                Set.union sorts1 sorts2 )
        | ( ( Con (BoolTerm.Iff, info)
            | TyApp (Con (BoolTerm.Eq, info), BoolTerm.SBool, _) ),
            [ t1; t2 ] ) ->
            if config.encode_bool_ops then
              (* t1 <=> t2 -> (not t1 or t2) and (t1 or not t2) *)
              aux senv
                ( Con (BoolTerm.And, info),
                  [
                    BoolTerm.or_of [ BoolTerm.neg_of t1; t2 ];
                    BoolTerm.or_of [ t1; BoolTerm.neg_of t2 ];
                  ] )
            else
              let t1, rules1, sorts1 = aux senv (t1, []) in
              let t2, rules2, sorts2 = aux senv (t2, []) in
              ( RSFD.apps biff [ t1; t2 ],
                rules1 @ rules2,
                Set.union sorts1 sorts2 )
        | ( ( Con (BoolTerm.Xor, info)
            | TyApp (Con (BoolTerm.Neq, info), BoolTerm.SBool, _) ),
            [ t1; t2 ] ) ->
            if config.encode_bool_ops then
              (* t1 xor t2 -> (t1 or t2) and (not t1 or not t2) *)
              aux senv
                ( Con (BoolTerm.And, info),
                  [
                    BoolTerm.or_of [ t1; t2 ];
                    BoolTerm.or_of [ BoolTerm.neg_of t1; BoolTerm.neg_of t2 ];
                  ] )
            else
              let t1, rules1, sorts1 = aux senv (t1, []) in
              let t2, rules2, sorts2 = aux senv (t2, []) in
              ( RSFD.apps bxor [ t1; t2 ],
                rules1 @ rules2,
                Set.union sorts1 sorts2 )
        | App (t1, t2, _), args -> aux senv (t1, t2 :: args)
        | Bin (Forall, tvar, BoolTerm.SBool, t, _), [] ->
            let tvar, t = binder senv tvar t in
            let senv' = senv @ [ (tvar, BoolTerm.SBool) ] in
            let t, rules, sorts = aux senv' (t, []) in
            let nt = Ast.Ident.mk_fresh_tvar ~prefix:(Some "S") () in
            let cont =
              RSFD.apps (RSFD.Nonterm nt)
                (List.map senv ~f:(fun (x, _) -> RSFD.Term x))
            in
            ( RSFD.apps band [ RSFD.app cont tt; RSFD.app cont ff ],
              (nt, (List.map senv' ~f:fst, t)) :: rules,
              sorts )
        | Bin (Forall, tvar, s, t, _), [] ->
            let tvar, t = binder senv tvar t in
            let senv' = senv @ [ (tvar, s) ] in
            let t, rules, sorts = aux senv' (t, []) in
            let nt = Ast.Ident.mk_fresh_tvar ~prefix:(Some "S") () in
            let cont =
              RSFD.apps (RSFD.Nonterm nt)
                (List.map senv' ~f:(fun (x, _) -> RSFD.Term x))
            in
            let qnt = Ast.Ident.mk_fresh_tvar ~prefix:(Some "Forall") () in
            let qcont =
              RSFD.apps (RSFD.Nonterm qnt)
                (List.map senv ~f:(fun (x, _) -> RSFD.Term x))
            in
            ( RSFD.app qcont (zero_of s),
              ( qnt,
                ( List.map senv' ~f:fst,
                  RSFD.apps band
                    [
                      cont;
                      RSFD.apps bif
                        [
                          RSFD.app (ismax_of s) (RSFD.Term tvar);
                          tt;
                          RSFD.app qcont (RSFD.app (succ_of s) (RSFD.Term tvar));
                        ];
                    ] ) )
              :: (nt, (List.map senv' ~f:fst, t))
              :: rules,
              Set.add sorts s )
        | Bin (Exists, tvar, BoolTerm.SBool, t, _), [] ->
            let tvar, t = binder senv tvar t in
            let senv' = senv @ [ (tvar, BoolTerm.SBool) ] in
            let t, rules, sorts = aux senv' (t, []) in
            let nt = Ast.Ident.mk_fresh_tvar ~prefix:(Some "S") () in
            let body =
              RSFD.apps (RSFD.Nonterm nt)
                (List.map senv ~f:(fun (x, _) -> RSFD.Term x))
            in
            ( RSFD.apps bor [ RSFD.app body tt; RSFD.app body ff ],
              (nt, (List.map senv' ~f:fst, t)) :: rules,
              sorts )
        | Bin (Exists, tvar, s, t, _), [] ->
            let tvar, t = binder senv tvar t in
            let senv' = senv @ [ (tvar, s) ] in
            let t, rules, sorts = aux senv' (t, []) in
            let nt = Ast.Ident.mk_fresh_tvar ~prefix:(Some "S") () in
            let cont =
              RSFD.apps (RSFD.Nonterm nt)
                (List.map senv' ~f:(fun (x, _) -> RSFD.Term x))
            in
            let qnt = Ast.Ident.mk_fresh_tvar ~prefix:(Some "Exists") () in
            let qcont =
              RSFD.apps (RSFD.Nonterm qnt)
                (List.map senv ~f:(fun (x, _) -> RSFD.Term x))
            in
            ( RSFD.app qcont (zero_of s),
              ( qnt,
                ( List.map senv' ~f:fst,
                  RSFD.apps bor
                    [
                      cont;
                      RSFD.apps bif
                        [
                          RSFD.app (ismax_of s) (RSFD.Term tvar);
                          ff;
                          RSFD.app qcont (RSFD.app (succ_of s) (RSFD.Term tvar));
                        ];
                    ] ) )
              :: (nt, (List.map senv' ~f:fst, t))
              :: rules,
              Set.add sorts s )
        | Bin (Lambda, tvar, _, t, _), arg :: args ->
            aux senv (Term.subst (Map.Poly.singleton tvar arg) t, args)
        | ( TyApp (Con (BoolTerm.IfThenElse, info), BoolTerm.SBool, _),
            [ t1; t2; t3 ] ) ->
            (* if t1 then t2 else t3 -> (not t1 or t2) and (t1 or t3) *)
            aux senv
              ( Con (BoolTerm.And, info),
                [
                  BoolTerm.or_of [ BoolTerm.neg_of t1; t2 ];
                  BoolTerm.or_of [ t1; t3 ];
                ] )
        | TyApp (term, _sort, _), args ->
            (* The [else] branch -- ignore the type argument and recurse -- is
               written but switched off, with a note that [sort] ought to be
               used.  Reaching this arm therefore aborts the run, and an
               [assert false] says nothing about why; this names the term, as
               the catch-all arm below does.  Switching the branch on would be a
               semantic decision (is dropping the type argument sound here?),
               so it is left as the developer left it. *)
            if true then
              failwith
              @@ sprintf "[aux] type application is not supported: %s"
                   (ExtTerm.str_of term)
            else aux senv (term, args) (* ToDo: use [sort] *)
        | Let (tvar, _sort, def, body, _), args ->
            (* ToDo *)
            aux senv (Term.subst (Map.Poly.singleton tvar def) body, args)
        | term, args ->
            failwith
            @@ sprintf "[aux] unknown term: %s(%s)" (ExtTerm.str_of term)
                 (String.concat_map_list ~sep:"," args ~f:ExtTerm.str_of)
      in
      (* The sorts of HOSAT are [bool] and arrows between them; two are equal
         when their argument and value sorts are, effects being absent. *)
      let rec is_hosat_sort = function
        | BoolTerm.SBool -> true
        | Sort.SArrow (s, c) -> is_hosat_sort s && is_hosat_sort c.val_type
        | _ -> false
      in
      let rec equal_sort s1 s2 =
        match (s1, s2) with
        | BoolTerm.SBool, BoolTerm.SBool -> true
        | Sort.SArrow (a1, c1), Sort.SArrow (a2, c2) ->
            equal_sort a1 a2 && equal_sort c1.val_type c2.val_type
        | _ -> false
      in
      let rec str_of_hosat_sort = function
        | BoolTerm.SBool -> "bool"
        | Sort.SArrow (s, c) ->
            (if Sort.is_arrow s then sprintf "(%s)" else Fn.id)
              (str_of_hosat_sort s)
            ^ " -> "
            ^ str_of_hosat_sort c.val_type
        | s -> ExtTerm.str_of_sort s
      in
      let bb = Sort.mk_arrow BoolTerm.SBool BoolTerm.SBool in
      let bbb = Sort.mk_arrow BoolTerm.SBool bb in
      (* [sort_of senv t] is the sort of [t] when every variable of [t] is
         bound in [senv] (innermost last) at the sort its binder declares,
         and otherwise refuses the input through [Common.Refusal]:
         - an application [t1(t2)] is accepted only when [t1] has an arrow
           sort whose argument sort equals the sort of [t2], so a head is
           never applied to more arguments than its sort takes, and an
           argument of the wrong sort -- a formula where a function is
           expected, a function of the wrong arity -- is refused with the
           application and both sorts named;
         - a quantifier's binder has a sort of [bool] and arrows, and its body
           is of sort [bool].
         A partial application is checked like any other term, so passing
         one where its (arrow) sort is expected is accepted.  The check reads
         the input and builds nothing, so a well-sorted input reaches [aux]
         unchanged; it does not promise that [aux] can translate every
         well-sorted term (a lambda or a connective passed as an argument
         still is not), only that [aux] never meets an ill-sorted one. *)
      let rec sort_of senv = function
        | Var (x, _) -> (
            match List.Assoc.find senv ~equal:Ast.Ident.tvar_equal x with
            | Some s -> s
            | None ->
                Common.Refusal.refuse
                  "-p hosat: the variable %s is not bound by a quantifier"
                  (Ast.Ident.name_of_tvar x))
        | Con ((BoolTerm.True | BoolTerm.False), _) -> BoolTerm.SBool
        | Con (BoolTerm.Not, _) -> bb
        | Con
            ( ( BoolTerm.And | BoolTerm.Or | BoolTerm.Imply | BoolTerm.Iff
              | BoolTerm.Xor ),
              _ )
        | TyApp
            (Con ((BoolTerm.Eq | BoolTerm.Neq), _), BoolTerm.SBool, _) ->
            bbb
        | TyApp (Con (BoolTerm.IfThenElse, _), BoolTerm.SBool, _) ->
            Sort.mk_arrow BoolTerm.SBool bbb
        | App (t1, t2, _) as t -> (
            match sort_of senv t1 with
            | Sort.SArrow (sarg, c) ->
                let s2 = sort_of senv t2 in
                if equal_sort sarg s2 then c.val_type
                else
                  Common.Refusal.refuse
                    "-p hosat: ill-sorted application %s: its argument %s has \
                     sort %s where %s of sort %s expects %s"
                    (ExtTerm.str_of t) (ExtTerm.str_of t2) (str_of_hosat_sort s2)
                    (ExtTerm.str_of t1)
                    (str_of_hosat_sort (Sort.SArrow (sarg, c)))
                    (str_of_hosat_sort sarg)
            | s1 ->
                Common.Refusal.refuse
                  "-p hosat: ill-sorted application %s: %s has sort %s, which \
                   takes no argument, and is applied to %s of sort %s"
                  (ExtTerm.str_of t) (ExtTerm.str_of t1) (str_of_hosat_sort s1)
                  (ExtTerm.str_of t2)
                  (str_of_hosat_sort (sort_of senv t2)))
        | Bin (((Forall | Exists) as q), x, s, body, _) ->
            if not (is_hosat_sort s) then
              Common.Refusal.refuse
                "-p hosat: the quantified variable %s has sort %s, which is \
                 not built from bool and arrows"
                (Ast.Ident.name_of_tvar x) (str_of_hosat_sort s);
            let sb = sort_of (senv @ [ (x, s) ]) body in
            if not (equal_sort sb BoolTerm.SBool) then
              Common.Refusal.refuse
                "-p hosat: the body of %s %s has sort %s where bool is expected"
                (match q with Forall -> "forall" | _ -> "exists")
                (Ast.Ident.name_of_tvar x) (str_of_hosat_sort sb);
            BoolTerm.SBool
        | Bin (Lambda, x, s, body, _) ->
            if not (is_hosat_sort s) then
              Common.Refusal.refuse
                "-p hosat: the lambda-bound variable %s has sort %s, which is \
                 not built from bool and arrows"
                (Ast.Ident.name_of_tvar x) (str_of_hosat_sort s);
            Sort.mk_arrow s (sort_of (senv @ [ (x, s) ]) body)
        | Let (x, s, def, body, _) ->
            let sd = sort_of senv def in
            if not (equal_sort sd s) then
              Common.Refusal.refuse
                "-p hosat: let %s is declared of sort %s and defined by %s of \
                 sort %s"
                (Ast.Ident.name_of_tvar x) (str_of_hosat_sort s)
                (ExtTerm.str_of def) (str_of_hosat_sort sd);
            sort_of (senv @ [ (x, s) ]) body
        | t ->
            Common.Refusal.refuse "-p hosat: unsupported term %s"
              (ExtTerm.str_of t)
      in
      let closed =
        (* a free variable is quantified existentially outside the formula,
           the convention [HOSAT.Problem.of_sat] and [of_dqsat] already
           follow, at sort [bool]: one that is applied is refused by the sort
           check below *)
        BoolTerm.exists
          (List.map (Set.to_list @@ Term.fvs_of input) ~f:(fun x ->
               (x, BoolTerm.SBool)))
          input
      in
      (let s = sort_of [] closed in
       if not (equal_sort s BoolTerm.SBool) then
         Common.Refusal.refuse
           "-p hosat: the input has sort %s where a formula (bool) is expected"
           (str_of_hosat_sort s));
      let t, rules, sorts = aux [] (closed, []) in
      let sorts =
        let rec expand_sort = function
          | BoolTerm.SBool -> Set.Poly.singleton BoolTerm.SBool
          | Sort.SArrow (sarg, cret) as s ->
              Set.Poly.union_list
                [
                  Set.Poly.singleton s;
                  expand_sort sarg;
                  expand_sort cret.val_type;
                ]
          | _ -> failwith "not supported"
        in
        Set.to_list @@ Set.concat_map sorts ~f:expand_sort
      in
      ((Ast.Ident.Tvar "S", ([], t)) :: rules)
      @ List.concat_map sorts ~f:(fun s ->
            let sargs = Sort.args_of s in
            let args = List.map ~f:fst @@ sort_env_list_of_sorts sargs in
            let x = Ast.Ident.Tvar "x" in
            let xt = RSFD.Term x in
            let y = Ast.Ident.Tvar "y" in
            let yt = RSFD.Term y in
            let z = Ast.Ident.Tvar "z" in
            let zt = RSFD.Term z in
            [
              (zero s, (args, ff));
              ( ismax s,
                ( [ x ],
                  match s with
                  | BoolTerm.SBool -> xt
                  | Sort.SArrow (BoolTerm.SBool, cret) ->
                      let t = ismax_of cret.val_type in
                      RSFD.apps band
                        [
                          RSFD.app t (RSFD.app xt tt);
                          RSFD.app t (RSFD.app xt ff);
                        ]
                  | Sort.SArrow (sarg, _) ->
                      RSFD.apps (ismaxrec_of s) [ xt; zero_of sarg ]
                  | _ -> failwith "not supported" ) );
              ( succ s,
                ( x :: args,
                  match s with
                  | BoolTerm.SBool -> tt
                  | Sort.SArrow (BoolTerm.SBool, cret) ->
                      let x1, xs2 = List.hd_tl args in
                      let t1 = RSFD.Term x1 in
                      let ts2 = List.map xs2 ~f:(fun x -> RSFD.Term x) in
                      let st =
                        RSFD.apps (succ_of cret.val_type) (RSFD.app xt t1 :: ts2)
                      in
                      RSFD.apps bif
                        [
                          RSFD.app (ismax_of cret.val_type) (RSFD.app xt ff);
                          RSFD.apps bif
                            [ t1; st; RSFD.apps (zero_of cret.val_type) ts2 ];
                          RSFD.apps bif [ t1; RSFD.apps xt (t1 :: ts2); st ];
                        ]
                  | Sort.SArrow (sarg, _) ->
                      RSFD.apps (find_of s)
                        (xt :: zero_of sarg
                        :: List.map ~f:(fun x -> RSFD.Term x) args)
                  | _ -> failwith "not supported" ) );
              ( compare s,
                let lt = Ast.Ident.Tvar "lt" in
                let ltt = RSFD.Term lt in
                let eq = Ast.Ident.Tvar "eq" in
                let eqt = RSFD.Term eq in
                let gt = Ast.Ident.Tvar "gt" in
                let gtt = RSFD.Term gt in
                ( (match s with
                  | BoolTerm.SBool -> [ x; y; lt; eq; gt ]
                  | Sort.SArrow (_, _) -> [ x; y; z; lt; eq; gt ]
                  | _ -> failwith "not supported"),
                  match s with
                  | BoolTerm.SBool ->
                      RSFD.apps bif
                        [
                          xt;
                          RSFD.apps bif [ yt; eqt; gtt ];
                          RSFD.apps bif [ yt; ltt; eqt ];
                        ]
                  | Sort.SArrow (sarg, cret) ->
                      (* [Compare x y z lt eq gt] compares the functions [x]
                         and [y] on the arguments from [z] up to the maximal
                         one, the larger argument the more significant digit
                         (the order [Succ] counts in), and continues with [eq]
                         when they agree there.  So the comparison at [z] is
                         the [eq] continuation of the comparison above [z], and
                         at the maximal argument it is the whole answer:
                         answering [eq] there instead skipped the most
                         significant digit, so [Carry] took two different
                         arguments for one and the enumeration of a function
                         sort whose argument is itself a function visited only
                         some of its functions (4 of the 16 of
                         [(bool -> bool) -> bool]). *)
                      let here =
                        RSFD.apps (compare_of cret.val_type)
                          ([ RSFD.app xt zt; RSFD.app yt zt ]
                          @ (match cret.val_type with
                            | Sort.SArrow (s1, _) -> [ zero_of s1 ]
                            | _ -> [])
                          @ [ ltt; eqt; gtt ])
                      in
                      RSFD.apps bif
                        [
                          RSFD.app (ismax_of sarg) zt;
                          here;
                          RSFD.apps (compare_of s)
                            [ xt; yt; RSFD.app (succ_of sarg) zt; ltt; here; gtt ];
                        ]
                  | _ -> failwith "not supported" ) );
            ]
            @
            match s with
            | Sort.SArrow ((Sort.SArrow (_, _) as sarg), cret) ->
                [
                  ( ismaxrec s,
                    ( [ x; y ],
                      RSFD.apps band
                        [
                          RSFD.app (ismax_of cret.val_type) (RSFD.app xt yt);
                          RSFD.apps bif
                            [
                              RSFD.app (ismax_of sarg) yt;
                              tt;
                              RSFD.apps (ismaxrec_of s)
                                [ xt; RSFD.app (succ_of sarg) yt ];
                            ];
                        ] ) );
                  ( find s,
                    ( x :: y :: args,
                      RSFD.apps bif
                        [
                          RSFD.app (ismax_of cret.val_type) (RSFD.app xt yt);
                          RSFD.apps bif
                            [
                              RSFD.app (ismax_of sarg) yt;
                              RSFD.apps (zero_of cret.val_type)
                                (List.map ~f:(fun x -> RSFD.Term x)
                                @@ List.tl_exn args);
                              RSFD.apps (find_of s)
                                (xt
                                :: RSFD.app (succ_of sarg) yt
                                :: List.map ~f:(fun x -> RSFD.Term x) args);
                            ];
                          RSFD.apps (carry_of s)
                            (xt :: yt :: List.map ~f:(fun x -> RSFD.Term x) args);
                        ] ) );
                  ( carry s,
                    ( x :: y :: args,
                      RSFD.apps (compare_of sarg)
                        [
                          yt;
                          RSFD.Term (List.hd_exn args);
                          zero_of
                            (match sarg with
                            | Sort.SArrow (s1, _) -> s1
                            | _ -> failwith "not supported");
                          RSFD.apps xt (List.map ~f:(fun x -> RSFD.Term x) args);
                          RSFD.apps
                            (RSFD.app (succ_of cret.val_type)
                               (RSFD.app xt (RSFD.Term (List.hd_exn args))))
                            (List.map ~f:(fun x -> RSFD.Term x)
                            @@ List.tl_exn args);
                          RSFD.apps (zero_of cret.val_type)
                            (List.map ~f:(fun x -> RSFD.Term x)
                            @@ List.tl_exn args);
                        ] ) );
                ]
            | _ -> [])
    in
    HOMC.Problem.RSFD
      ([], rules, Automata.TreeAutomaton.ATA (spec_arity, spec_rules))

  let solve_hosat ?(print_sol = false) hosat =
    let open Or_error.Monad_infix in
    solver >>= fun (module HOMCSolver : HOMCSolver.Solver.SolverType) ->
    Debug.print
    @@ lazy
         ("input: " ^ Ast.LogicOld.Formula.str_of
         @@ Ast.Logic.ExtTerm.to_old_fml Map.Poly.empty Map.Poly.empty
              (HOSAT.Problem.term_of hosat));
    let homc = homc_of_hosat hosat in
    HOMCSolver.solve ~print_sol:false homc >>= fun sol ->
    let sol =
      match sol with
      | HOMC.Problem.Sat -> HOSAT.Problem.Sat
      | HOMC.Problem.Unsat -> HOSAT.Problem.Unsat
      | HOMC.Problem.Unknown -> HOSAT.Problem.Unknown
    in
    if print_sol then print_endline (HOSAT.Problem.str_of_solution sol);
    Ok sol

  let solve ?(print_sol = false) cnf =
    let open Or_error.Monad_infix in
    cnf |> HOSAT.Problem.of_sat |> solve_hosat ~print_sol:false >>= fun sol ->
    let sol =
      match sol with
      | HOSAT.Problem.Sat -> SAT.Problem.Sat []
      | HOSAT.Problem.Unsat -> SAT.Problem.Unsat
      | HOSAT.Problem.Unknown -> SAT.Problem.Unknown
    in
    if print_sol then print_endline (SAT.Problem.str_of_solution sol);
    Ok sol

  let incremental_solve ?(print_sol = false) cnf =
    ignore print_sol;
    ignore cnf;
    failwith "not implemented"

  let solve_dqsat ?(print_sol = false) dqbf =
    let open Or_error.Monad_infix in
    dqbf |> HOSAT.Problem.of_dqsat |> solve_hosat ~print_sol:false
    >>= fun sol ->
    let sol =
      match sol with
      | HOSAT.Problem.Sat -> DQSAT.Problem.Sat
      | HOSAT.Problem.Unsat -> DQSAT.Problem.Unsat
      | HOSAT.Problem.Unknown -> DQSAT.Problem.Unknown
    in
    if print_sol then print_endline (DQSAT.Problem.str_of_solution sol);
    Ok sol
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
