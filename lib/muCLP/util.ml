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
  {
    preds =
      List.map muclp.preds ~f:(fun pred ->
          let args, body, _ =
            Formula.mk_forall pred.args pred.body
            |> Typeinf.typeinf_formula ~print
                 ~default:(Some T_int.SInt (*ToDo*))
            |> Formula.let_forall
          in
          { pred with args; body });
    query =
      Typeinf.typeinf_formula ~print ~default:(Some T_int.SInt (*ToDo*))
        muclp.query;
  }

(*val typeinf_query : print:(string lazy_t -> unit) -> query -> query*)
let typeinf_query ~print query =
  Typeinf.typeinf_formula ~print ~default:(Some T_int.SInt (*ToDo*)) query

let parse_from_lexbuf ~print lexbuf =
  try Ok (typeinf ~print @@ Parser.toplevel Lexer.main lexbuf) with
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

let parse_query_from_lexbuf ~print lexbuf =
  try Ok (typeinf_query ~print @@ Parser.query Lexer.main lexbuf) with
  | Parser.Error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error"
              (LexingHelper.get_position_string lexbuf))
  | Lexer.SyntaxError error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error: %s"
              (LexingHelper.get_position_string lexbuf)
              error)

let from_file ~print =
  In_channel.create >> Lexing.from_channel >> parse_from_lexbuf ~print

let from_string ~print = Lexing.from_string >> parse_from_lexbuf ~print

let query_from_string ~print =
  Lexing.from_string >> parse_query_from_lexbuf ~print

(*val get_dual : t -> t*)
let get_dual muclp =
  let pvars = List.map muclp.preds ~f:(fun pred -> pred.name) in
  let subst formula =
    List.fold ~init:formula pvars ~f:(Fn.flip Formula.subst_neg)
  in
  make
    (List.map muclp.preds ~f:(fun pred ->
         {
           pred with
           kind = Predicate.flip_fop pred.kind;
           body = Evaluator.simplify_neg (subst pred.body);
         }))
    (Evaluator.simplify_neg (subst muclp.query))

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
          let body =
            Formula.subst_preds
              (Map.Poly.singleton def.name (def.args, new_pvar_app))
              body
          in
          ( Formula.mk_atom ~info
            @@ Atom.mk_pvar_app new_pvar new_sorts new_outer_args ~info:info',
            Pred.make def.kind new_pvar new_bounds body :: preds,
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
                def.args body
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
let of_chc ~print ?(only_pos = true) chc =
  ignore print;
  let chc = chc |> PCSP.Problem.to_nnf |> PCSP.Problem.to_cnf in
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
                     Pair.map_snd Evaluator.simplify_neg
                     @@ Ast.Qelim.qelim_old
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
                 Pair.map_snd Evaluator.simplify_neg
                 @@ Ast.Qelim.qelim_old Map.Poly.empty
                      (PCSP.Problem.senv_of chc)
                      (senv, Evaluator.simplify_neg phi)
               in
               let unbound =
                 Logic.to_old_sort_env_list @@ Map.Poly.to_alist senv
               in
               Formula.exists unbound phi)
    | _ -> assert false
  in
  let undef_preds =
    let def_preds = List.map preds ~f:(fun pred -> pred.name) in
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
  if only_pos then get_dual @@ make (preds @ undef_preds) query
  else make (preds @ undef_preds) (Evaluator.simplify_neg query)

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
            transitions ) =
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
        List.classify
          (fun (s1, _, _) (s2, _, _) -> String.(s1 = s2))
          transitions
        |> List.partition_map ~f:(function
             | [] -> assert false
             | (from, c, to_) :: trs -> (
                 let next =
                   (c, to_) :: List.map trs ~f:(fun (_, c, to_) -> (c, to_))
                   |> List.map ~f:(fun (c, to_) ->
                          let pvar = pvar_of to_ in
                          let senv = tenv_of to_ in
                          let phi =
                            LTS.Problem.wp c
                              (Formula.mk_atom
                              @@ Atom.pvar_app_of_senv pvar senv)
                          in
                          let nondet_tenv =
                            Set.to_list
                            @@ Set.filter
                                 (Formula.term_sort_env_of phi)
                                 ~f:
                                   (fst >> Ident.name_of_tvar
                                   >> String.is_prefix
                                        ~prefix:LTS.Problem.nondet_prefix)
                          in
                          Formula.mk_forall_if_bounded nondet_tenv phi)
                   |> Formula.and_of |> Evaluator.simplify
                   |> Normalizer.normalize
                 in
                 match cut_points with
                 | Some cut_points when not @@ Set.mem cut_points from ->
                     First
                       (Pred.make Predicate.Fix (pvar_of from) (tenv_of from)
                          next)
                 | _ ->
                     Second
                       (Pred.make Predicate.Mu (pvar_of from) (tenv_of from)
                          next)))
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
                   Pred.make Predicate.Fix (pvar_of from) (tenv_of from)
                     (Formula.mk_true ()))
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
  | _, LTS.Problem.(Safe | NonSafe | MuCal | Rel) -> failwith "not implemented"
