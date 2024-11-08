open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.Ident
open Ast.Logic

let verbose = false

module Debug =
  Debug.Make ((val Debug.Config.(if verbose then enable else disable)))

let _ = Debug.set_module_name "TupleExtracter"

let param_senv_of phi =
  LogicOld.Formula.term_sort_env_of phi
  |> Set.to_list |> of_old_sort_env_list |> Map.Poly.of_alist_exn

let rec replace_tuple_var_to_cons_term tuple_var_map =
  let open LogicOld in
  Term.map_term true ~f:(function
    | Term.Var (v, T_tuple.STuple sorts, _) -> (
        match Hashtbl.Poly.find tuple_var_map v with
        | Some t -> t
        | _ ->
            let tuple =
              T_tuple.mk_tuple_cons sorts
              @@ List.map sorts
                   ~f:
                     (Term.mk_fresh_var
                     >> replace_tuple_var_to_cons_term tuple_var_map)
            in
            Hashtbl.Poly.set ~key:v ~data:tuple tuple_var_map;
            tuple)
    | t -> t)

let extract_tuple tuple_var_map t =
  let open LogicOld in
  let rec inner = function
    | Term.FunApp (T_tuple.TupleCons _, ts, _) -> List.concat_map ts ~f:inner
    | Term.FunApp (T_tuple.TupleSel (_, i), [ te ], _) as t -> (
        match T_tuple.eval_select te i with
        | Some te -> inner te
        | None -> [ t ])
    | Term.Var (_, T_tuple.STuple _, _) -> failwith "unreachable here"
    | t -> [ t ]
  in
  inner @@ replace_tuple_var_to_cons_term tuple_var_map t

(** extract all tuple_cons/tuple_sel/tuple_var terms in phi *)
let extract_tuples tuple_var_map exi_senv fnpvs (param_senv, phi) =
  let open LogicOld in
  let phi =
    ExtTerm.to_old_fml exi_senv (param_senv, phi)
    |> (fun phi ->
         Debug.print_log ~tag:"extract_tuple"
         @@ lazy (sprintf "\n%s\n" @@ Formula.str_of phi);
         phi)
    |> Formula.map_term ~f:(replace_tuple_var_to_cons_term tuple_var_map)
    |> Formula.map_term ~f:Evaluator.simplify_term
  in
  Debug.print_log ~tag:"elimalited tuple variables"
  @@ lazy (sprintf "\n%s\n" @@ Formula.str_of phi);
  let fn_pvs = Hash_set.Poly.create () in
  let exi_senv' = Hashtbl.Poly.create () in
  let phi' =
    Formula.map_atom phi ~f:(fun atm ->
        if Fn.non Atom.is_pvar_app atm then
          match atm with
          | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) ->
              let t1s = extract_tuple tuple_var_map t1 in
              let t2s = extract_tuple tuple_var_map t2 in
              Formula.and_of (List.map2_exn t1s t2s ~f:Formula.eq)
          | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) ->
              let t1s = extract_tuple tuple_var_map t1 in
              let t2s = extract_tuple tuple_var_map t2 in
              Formula.or_of (List.map2_exn t1s t2s ~f:Formula.neq)
          | Atom.App (op, [ t1; t2 ], info) ->
              let t1s = extract_tuple tuple_var_map t1 in
              let t2s = extract_tuple tuple_var_map t2 in
              if List.length t1s = 1 && List.length t2s = 1 then
                Formula.mk_atom @@ Atom.App (op, t1s @ t2s, info)
              else Formula.mk_atom atm
          | _ -> Formula.mk_atom atm
        else
          let pvar, _, ts, _ = Atom.let_pvar_app atm in
          if Set.mem fnpvs (Ident.pvar_to_tvar pvar) then
            let tparams, tsol = List.rest_last ts in
            let tparams =
              List.concat_map tparams ~f:(extract_tuple tuple_var_map)
            in
            let sorts = List.map tparams ~f:Term.sort_of in
            let tsols = extract_tuple tuple_var_map tsol in
            Formula.and_of
            @@ List.foldi tsols ~init:[] ~f:(fun i acc t ->
                   let pf = Tvar (sprintf "%s%d" (name_of_pvar pvar) (i + 1)) in
                   let sorts = sorts @ [ Term.sort_of t; T_bool.SBool ] in
                   Hash_set.Poly.add fn_pvs pf;
                   Hashtbl.Poly.set exi_senv' ~key:pf
                     ~data:(ExtTerm.of_old_sort @@ Sort.mk_fun sorts);
                   (Formula.mk_atom
                   @@ Atom.mk_pvar_app (tvar_to_pvar @@ pf) sorts
                        (tparams @ [ t ]))
                   :: acc)
          else
            let ts' =
              List.fold ts ~init:[] ~f:(fun acc t ->
                  acc @ extract_tuple tuple_var_map t)
            in
            let sorts = List.map ts' ~f:Term.sort_of in
            Hashtbl.Poly.set exi_senv' ~key:(pvar_to_tvar pvar)
              ~data:
                (ExtTerm.of_old_sort @@ Sort.mk_fun (sorts @ [ T_bool.SBool ]));
            Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts ts')
  in
  let exi_senv' = exi_senv' |> Hashtbl.Poly.to_alist |> Map.Poly.of_alist_exn in
  Debug.print_log ~tag:"enimalited all tuple term"
  @@ lazy (sprintf "\n%s\n" @@ Formula.str_of phi');
  ( exi_senv',
    fn_pvs |> Hash_set.Poly.to_list |> Set.Poly.of_list,
    (param_senv_of phi', ExtTerm.of_old_formula phi') )

let extract_tuples pcsp =
  let pcsp = PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf pcsp in
  let phis = PCSP.Problem.formulas_of pcsp in
  let exi_senv = PCSP.Problem.senv_of pcsp in
  let fnpvs = PCSP.Problem.fnpvs_of pcsp in
  Set.Poly.map phis ~f:(extract_tuples (Hashtbl.Poly.create ()) exi_senv fnpvs)
  |> Set.to_list |> List.unzip3
  |> fun (exi_senvs, fnpvss, phis) ->
  let kind_map =
    Set.fold (Set.Poly.union_list fnpvss) ~init:(PCSP.Problem.kind_map_of pcsp)
      ~f:(fun acc p -> Map.Poly.set acc ~key:p ~data:Kind.FN)
  in
  let params =
    {
      (PCSP.Problem.params_of pcsp) with
      senv = Map.force_merge_list exi_senvs;
      kind_map;
    }
  in
  PCSP.Problem.of_formulas ~params @@ Set.Poly.of_list phis
