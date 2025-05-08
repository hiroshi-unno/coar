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
      let rec aux senv = function
        | Var (x, _), args ->
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
            if true then assert false
            else aux senv (term, args) (* ToDo: use [sort] *)
        | Let (tvar, _sort, def, body, _), args ->
            (* ToDo *)
            aux senv (Term.subst (Map.Poly.singleton tvar def) body, args)
        | term, args ->
            failwith
            @@ sprintf "[aux] unknown term: %s(%s)" (Term.str_of term)
                 (String.concat_map_list ~sep:"," args ~f:Term.str_of)
      in
      let t, rules, sorts =
        aux []
          ( (*Ast.Logic.ExtTerm.simplify_formula Map.Poly.empty Map.Poly.empty
              @@*)
            HOSAT.Problem.term_of hosat,
            [] )
      in
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
                      RSFD.apps bif
                        [
                          RSFD.app (ismax_of sarg) zt;
                          eqt;
                          RSFD.apps (compare_of s)
                            [
                              xt;
                              yt;
                              RSFD.app (succ_of sarg) zt;
                              ltt;
                              RSFD.apps (compare_of cret.val_type)
                                ([ RSFD.app xt zt; RSFD.app yt zt ]
                                @ (match cret.val_type with
                                  | Sort.SArrow (s1, _) -> [ zero_of s1 ]
                                  | _ -> [])
                                @ [ ltt; eqt; gtt ]);
                              gtt;
                            ];
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
