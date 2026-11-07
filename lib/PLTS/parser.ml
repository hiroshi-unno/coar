open Core
open Common.Combinator
open Ast
open Ast.LogicOld

(* [release_consumed_definitions fenv init nexts]: the SMT-LIB reader keeps
   every non-recursive [define-fun] it read in [LogicOld]'s inlined-definition
   table, for the passes that unfold an application of a defined symbol later.
   An integer transition system is written entirely as such definitions (the
   initial and the transition relations, and the [cfg_*] wrappers around
   them), and this reader consumes them: their bodies are taken apart into
   [init] and [nexts], and their names never reach the result.  Left in the
   table, the parsed relations stay reachable for the whole run -- on a 55 MB
   input about 420 MB of live heap after the conversion to muCLP, against a
   converted problem of a few MB -- and every copy a solver forks inherits
   and rewrites them.

   Removes from the table each definition of [fenv] whose name occurs in no
   relation of the result (an application left inside a relation keeps its
   definition, so a later unfolding reads what it read before).  Postcondition:
   the table's other entries are unchanged.  Exact: an entry removed is one no
   formula of the result can apply.  The table is also read whole by the
   Houdini candidate families that instantiate every Boolean definition at an
   unknown's reached terms of each formal's sort; these definitions all take a
   location (an uninterpreted sort) and the unknowns of the converted problem
   take integers and Booleans only, so those families got nothing from them
   before their removal either.  A transition system whose definitions took
   only integer formals would make this removal change the candidates. *)
let release_consumed_definitions fenv (_, _, _, init_rel) nexts =
  let rels =
    init_rel
    :: List.concat_map nexts ~f:(fun (_, _, _, trans) ->
           List.map (Set.to_list trans) ~f:(fun (_, _, rel) -> rel))
  in
  let applied =
    List.fold rels ~init:Set.Poly.empty ~f:(fun acc rel ->
        Set.fold (Formula.funsyms_of rel) ~init:acc ~f:(fun acc -> function
          | FVar (x, _, _) -> Set.add acc x
          | _ -> acc))
  in
  let consumed =
    Set.diff (Map.key_set fenv) applied
  in
  if not (Set.is_empty consumed) then
    LogicOld.set_inlined_defs
    @@ Map.Poly.filter_keys (LogicOld.get_inlined_defs ()) ~f:(fun x ->
           not (Set.mem consumed x))

let parse_from_lexbuf ~print lexbuf =
  let _phis (* assert distict ...*), envs =
    SMT.(Parser.program Lexer.token lexbuf)
    |> SMT.Smtlib2.toplevel ~print ~inline:false []
         {
           (* an ITS file declares its locations with [declare-const l Loc]:
              constants of an uninterpreted sort that are read from
              [exi_senv] below, not unknowns to solve for.  The synthesis
              reading would give each one a predicate kind, and there is no
              kind for a function into an uninterpreted sort, so every such
              file was refused *)
           decl_reading = SMT.Problem.Uninterpreted;
           lifted_universals = Map.Poly.empty;
           candidates = Map.Poly.empty;
           uni_sort = Set.Poly.empty;
           uni_senv = Map.Poly.empty;
           exi_senv = Map.Poly.empty;
           dep_map = Map.Poly.empty;
           kind_map = Map.Poly.empty;
           fenv = Map.Poly.empty;
           dtenv = Map.Poly.empty;
         }
  in
  let _dtenv (* declare-sort *) = envs.dtenv in
  assert (Map.is_empty envs.uni_senv);
  let _kind_map = envs.kind_map in
  let locs (* declare-const *) = Map.key_set envs.exi_senv in
  let inits, nexts =
    Map.Poly.filteri envs.fenv (* define-fun *) ~f:(fun ~key ~data:_ ->
        let f = Ident.name_of_tvar key in
        String.(f <> "cfg_init" && f <> "cfg_trans2" && f <> "cfg_trans3"))
    |> Map.Poly.partition_mapi
         ~f:(fun ~key ~data:(args, ret, def, is_rec, prop) ->
           assert (Term.is_bool_sort ret && (not is_rec) && Formula.is_true prop);
           let phi =
             try T_bool.let_formula def
             with exn_ when not (Common.Timer.is_async exn_) -> Formula.eq def (T_bool.mk_true ())
           in
           let f = Ident.name_of_tvar key in
           let ff = String.sub f ~pos:5 ~len:(String.length f - 5) in
           if String.is_prefix f ~prefix:"init_" then
             let pc, args =
               match args with
               | (pc, _sloc) :: args -> (pc, args)
               | [] -> failwith ""
             in
             let src, rel =
               let t, _, _ = Formula.let_eq phi in
               let f, _, _, args, _ = Term.let_fvar_app t in
               assert (String.(Ident.name_of_tvar f = "cfg_init"));
               match args with
               | [ pc'; src; rel ] ->
                   assert (Ident.tvar_equal pc (Term.tvar_of pc'));
                   ( Ident.name_of_tvar @@ Term.tvar_of src,
                     T_bool.let_formula rel )
               | _ -> failwith ""
             in
             First (ff, args, src, rel)
           else if String.is_prefix f ~prefix:"next_" then (
             let len = List.length args in
             assert (len mod 2 = 0);
             let args1, args2 = List.split_n args (len / 2) in
             let pc1, args1 =
               match args1 with
               | (pc, _sloc) :: args -> (pc, args)
               | [] -> failwith ""
             in
             let pc2, args2 =
               match args2 with
               | (pc, _sloc) :: args -> (pc, args)
               | [] -> failwith ""
             in
             let res =
               (* a [false] disjunct is no transition (a body that is just
                  [false] is a procedure without transitions, where every
                  run stops at once), not a [cfg_trans2] application *)
               Formula.disjuncts_of phi
               |> Set.filter ~f:(Fn.non Formula.is_false)
               |> Set.Poly.map ~f:(fun phi ->
                   let t, _, _ = Formula.let_eq phi in
                   let f, _, _, args, _ = Term.let_fvar_app t in
                   (* [cfg_trans3] is a procedure call (exit, call and return
                      locations); calls are not read, and such a file is
                      refused rather than read without them *)
                   if String.(Ident.name_of_tvar f = "cfg_trans3") then
                     failwith
                       "procedure calls (cfg_trans3) are not supported";
                   assert (String.(Ident.name_of_tvar f = "cfg_trans2"));
                   match args with
                   | [ pc1'; src; pc2'; dst; rel ] ->
                       assert (Ident.tvar_equal pc1 (Term.tvar_of pc1'));
                       assert (Ident.tvar_equal pc2 (Term.tvar_of pc2'));
                       ( Ident.name_of_tvar @@ Term.tvar_of src,
                         Ident.name_of_tvar @@ Term.tvar_of dst,
                         T_bool.let_formula rel )
                   | _ -> failwith "")
             in
             Second (ff, args1, args2, res))
           else failwith @@ sprintf "%s not supported" f)
  in
  let init =
    match Map.Poly.data inits with
    | [ init ] -> init
    | _ -> failwith "exactly one init_ definition is expected"
  in
  let nexts = Map.Poly.data nexts in
  release_consumed_definitions envs.fenv init nexts;
  Ok (locs, init, nexts)

let from_file ~print filename =
  In_channel.with_file filename ~f:(fun channel ->
      parse_from_lexbuf ~print (Lexing.from_channel channel))

let from_string ~print = Lexing.from_string >> parse_from_lexbuf ~print
