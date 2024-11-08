open Core
open Common.Combinator
open Ast
open Ast.LogicOld

let parse_from_lexbuf ~print lexbuf =
  let _phis (* assert distict ...*), envs =
    SMT.(Parser.program Lexer.token lexbuf)
    |> SMT.Smtlib2.toplevel ~print ~inline:false []
         {
           uni_senv = Map.Poly.empty;
           exi_senv = Map.Poly.empty;
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
           let phi = T_bool.let_formula def in
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
               let f, _sorts, args, _ = Term.let_fvar_app t in
               assert (String.(Ident.name_of_tvar f = "cfg_init"));
               match args with
               | [ pc'; src; rel ] ->
                   assert (Ident.tvar_equal pc (fst @@ fst @@ Term.let_var pc'));
                   ( Ident.name_of_tvar @@ fst @@ fst @@ Term.let_var src,
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
               Formula.disjuncts_of phi
               |> Set.Poly.map ~f:(fun phi ->
                      let t, _, _ = Formula.let_eq phi in
                      let f, _sorts, args, _ = Term.let_fvar_app t in
                      assert (String.(Ident.name_of_tvar f = "cfg_trans2"));
                      match args with
                      | [ pc1'; src; pc2'; dst; rel ] ->
                          assert (
                            Ident.tvar_equal pc1
                              (fst @@ fst @@ Term.let_var pc1'));
                          assert (
                            Ident.tvar_equal pc2
                              (fst @@ fst @@ Term.let_var pc2'));
                          ( Ident.name_of_tvar @@ fst @@ fst @@ Term.let_var src,
                            Ident.name_of_tvar @@ fst @@ fst @@ Term.let_var dst,
                            T_bool.let_formula rel )
                      | _ -> failwith "")
             in
             Second (ff, args1, args2, res))
           else failwith @@ sprintf "%s not supported" f)
  in
  let init =
    match Map.Poly.data inits with
    | [ init ] -> init
    | _ -> failwith "parse_from_lexbuf"
  in
  Ok (locs, init, Map.Poly.data nexts)

let from_file ~print =
  In_channel.create >> Lexing.from_channel >> parse_from_lexbuf ~print

let from_string ~print = Lexing.from_string >> parse_from_lexbuf ~print
