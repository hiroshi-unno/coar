open Core
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld
open PCSP
open PCSatCommon

type qualifier = sort_env_list * Formula.t

module type QualifierType = sig
  val qualifiers_of: Ident.pvar -> Sort.t list -> (ExAtom.t * int) Set.Poly.t -> (sort_env_map * VersionSpace.examples) -> qualifier Set.Poly.t
  val str_of_domain: string
end

module type GeneratorType = sig
  val generate: Ident.pvar -> sort_env_list -> (ExAtom.t * int) Set.Poly.t -> (sort_env_map * VersionSpace.examples) -> int -> qualifier Set.Poly.t
  val str_of_domain: int -> string
  val num_of_domains: int
end

module Config = struct
  type domain =
    | Null
    | Interval
    | Octagon
    | Octahedron
    | Polyhedron of int
    | Polynomial
    | SVM of int(*approx_level*) * float(*csvm*)
    | NN of int(* dummy parameter for neural network guided qualifier generation *)
    | Union of domain list [@@ deriving yojson]

  type t = {
    domains: domain list;
    extract_pcsp: bool; (** extract qualifiers from pfwCSP *)
    normalize_pcsp: bool; (** normalize pfwCSP for better extraction *)
    add_bool: bool; (** add qualifiers for boolean variables *)
    add_homogeneous: bool; (** add homogeneous qualifiers *)
    add_neg: bool; (** add negation of qualifiers *)
    filter_out_neg: bool;
    filter_out_non_div_mod: bool;
    filter_out_quantified: bool;
    reduce: bool; (** reduce redundant qualifiers *)
  } [@@ deriving yojson]

  let load_ext_file = function
    | ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename)
        >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> Ok (ExtFile.Instance x)
        | Error msg ->
          error_string
          @@ Printf.sprintf
            "Invalid Generator Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (ExtFile.Instance x)

  module type ConfigType = sig val config : t end
end

module Make (Cfg : Config.ConfigType) (PCSP: Problem.ProblemType) : GeneratorType = struct
  let config = Cfg.config
  let pcsp =
    if config.normalize_pcsp then
      Problem.clauses_of PCSP.problem
      |> Set.Poly.map ~f:(Clause.refresh_pvar_args (Problem.senv_of PCSP.problem))
      |> Set.Poly.map ~f:(fun (uni_senv, ps, ns, phi) -> (* this is essential for qualifiers extraction *)
          (* assume that [phi] is alpha-renamed *)
          let phi =
            Normalizer.normalize_let @@
            Logic.ExtTerm.to_old_formula (Problem.senv_of PCSP.problem) uni_senv phi []
          in
          let uni_senv =
            (*Map.force_merge (Logic.Term.let_sort_env_of @@ Logic.ExtTerm.of_old_formula phi)*)
            uni_senv
          in
          let phi =
            Logic.ExtTerm.of_old_formula @@
            (*Z3Smt.Z3interface.simplify (Problem.fenv_of PCSP.problem) @@*)
            Evaluator.simplify @@
            (*Formula.elim_ite @@*)
            (*Formula.equivalent_valid @@*) (*Formula.elim_let*) phi
          in
          let senv = Map.force_merge (Problem.senv_of PCSP.problem) uni_senv in
          let bounds =
            Map.of_set_exn @@ Set.Poly.map ~f:(fun x -> x, Map.Poly.find_exn senv x) @@
            Set.concat_map (Set.Poly.union ps ns) ~f:Logic.Term.fvs_of
          in
          let uni_senv_phi, _, phi = Qelim.qelim bounds (Problem.senv_of PCSP.problem) (uni_senv, [], phi) in
          let uni_senv = Map.force_merge bounds uni_senv_phi in
          let phi' =
            if Set.Poly.length ps + Set.Poly.length ns = 1 then phi
            else
              Logic.ExtTerm.of_old_formula @@
              Normalizer.normalize_let @@
              LogicOld.Formula.or_of @@ Set.Poly.to_list @@
              Set.Poly.map (Set.Poly.union ps ns) ~f:(fun atm ->
                  let bounds =
                    Map.of_set_exn @@ Set.Poly.map ~f:(fun x -> x, Map.Poly.find_exn senv x) @@
                    Logic.Term.fvs_of atm
                  in
                  let uni_senv', _, phi' = Qelim.qelim bounds (Problem.senv_of PCSP.problem) (uni_senv, [], phi) in
                  LogicOld.Formula.alpha_rename_let @@
                  Logic.ExtTerm.to_old_formula (Problem.senv_of PCSP.problem) uni_senv' phi' [])
          in
          uni_senv, ps, ns, phi')
      |> Problem.of_clauses ~params:(Problem.params_of PCSP.problem)
      (*|> (fun pcsp -> print_endline (Problem.str_of pcsp); pcsp)*)
    else PCSP.problem

  let rec module_of_domain = function
    | Config.Null -> (module Null : QualifierType)
    | Interval -> (module Interval : QualifierType)
    | Octagon  -> (module Octagon : QualifierType)
    | Octahedron -> (module Octahedron : QualifierType)
    | Polyhedron ub -> (module Polyhedron.Make (struct let upper_bound = ub end) : QualifierType)
    | Polynomial -> (module Polynomial : QualifierType)
    | SVM (approx_level, csvm) -> (module SVM.Make (struct let approx_level = approx_level let csvm = csvm end) : QualifierType)
    | NN dummy_param -> (module NN.Make (struct let dummy_param = dummy_param end) : QualifierType)
    | Union ds -> (module Union.Make (struct let domains = List.map ds ~f:module_of_domain end) : QualifierType)

  let domains = List.map config.domains ~f:module_of_domain

  let neg (params, phi) = params, Normalizer.normalize @@ Evaluator.simplify_neg phi
  let add_neg quals = Set.Poly.union quals (Set.Poly.map quals ~f:neg)
  let elim_neg quals = Set.Poly.fold quals ~init:Set.Poly.empty ~f:(fun quals q ->
      if Set.Poly.mem quals (neg q) then quals else Set.Poly.add quals q)
  let add_homogeneous quals = Set.Poly.union quals
      (Set.Poly.map quals ~f:(fun (params, phi) -> params, Normalizer.homogenize phi))

  let extract pcsp =
    (*let rec mk_let_to_cond conds bvs fvs tvs lenv =
      let lenv' = Map.Poly.filteri lenv ~f:(fun ~key ~data -> Set.Poly.mem fvs (key, Term.sort_of data)) in
      let conds' = Map.Poly.to_alist lenv' |> List.map ~f:(fun (var, def) -> Formula.eq (Term.mk_var var (Term.sort_of def)) def)  in
      let tvs' = Set.Poly.union tvs (Set.Poly.union_list @@ List.map conds' ~f:(Formula.sort_env_of)) in
      let fvs' = Set.Poly.diff tvs' bvs in
      let conds' = Set.Poly.union conds (Set.Poly.of_list conds') in
      if Set.Poly.length fvs = Set.Poly.length fvs' then tvs', fvs, Set.Poly.to_list conds' |> Formula.and_of
      else mk_let_to_cond conds' bvs fvs' tvs' lenv
      in*)
    let exi_senv = Problem.senv_of pcsp in
    let fenv = Problem.fenv_of pcsp in
    let id = Problem.id_of pcsp in
    Set.Poly.map (Problem.formulas_of pcsp) ~f:(fun (uni_senv, phi) ->
        Logic.ExtTerm.to_old_formula exi_senv uni_senv phi [])
    |> Set.Poly.to_list
    |> List.concat_map ~f:(fun phi ->
        (* print_endline @@ "[extract phi] " ^ Formula.str_of phi; *)
        let atomics, pos_papps, neg_papps = Formula.psym_pvar_apps_of ~simplifier:Evaluator.simplify phi in
        let pos_papp_tvs = List.map pos_papps ~f:(fun a -> a, Atom.term_sort_env_of(*ToDo*) a) in
        let neg_papp_tvs = List.map neg_papps ~f:(fun a -> a, Atom.term_sort_env_of(*ToDo*) a) in
        let bvs = Set.Poly.union_list @@ List.map ~f:snd @@ (pos_papp_tvs @ neg_papp_tvs) in
        (* print_endline @@ "[bvs] " ^ (String.concat_set ~sep:", " (List.map bvs ~f:(fun (v, _) -> Ident.name_of_tvar v))); *)
        (*(* assume that [phi] is alpha-renamed *)
          let lenv = Formula.let_env_of phi in*)
        List.concat_map atomics ~f:(fun atomic ->
            (* print_endline @@ "[extract atom] " ^ Atom.str_of atomic; *)
            let tvs = Atom.sort_env_of atomic in
            (* print_endline @@ "[tvs] " ^ (String.concat_set ~sep:", " (List.map tvs ~f:(fun (v, _) -> Ident.name_of_tvar v))); *)
            let fvs = Set.Poly.diff tvs bvs in
            (* let tvs, fvs, cond = mk_let_to_cond Set.Poly.empty bvs fvs tvs lenv in *)
            (* print_endline @@ "[fvs] " ^ (String.concat_set ~sep:", " (List.map fvs ~f:(fun (v, _) -> Ident.name_of_tvar v))); *)
            (* print_endline @@ "[cond] " ^ (Formula.str_of cond); *)
            if Fn.non Set.Poly.is_empty @@
              Set.Poly.inter (Set.Poly.map ~f:fst tvs) (Map.key_set exi_senv) ||
               Set.Poly.is_subset tvs ~of_:fvs(* tvs and bvs has no common element *) then []
            else
              List.concat_map pos_papp_tvs ~f:(fun (pa, pftv) ->
                  if Set.Poly.is_subset tvs ~of_:(Set.Poly.union pftv fvs)
                  (*&& (Set.Poly.is_empty fvs || match atomic with Atom.App (_, [t; _], _) -> Fn.non Term.is_bool_sort (Term.sort_of t) | _ -> false)*) then
                    (*let _ = print_endline @@ "pos" ^ string_of_int @@ Atom.ast_size atomic in
                      let _ = print_endline @@ "[atomic] " ^ (Atom.str_of atomic) in*)
                    let qual =
                      Z3Smt.Z3interface.qelim ~id fenv @@ Formula.exists (Set.Poly.to_list fvs) @@ Evaluator.simplify @@
                      (*Formula.mk_and cond @@*)
                      Formula.mk_atom @@ Atom.negate atomic in
                    (*print_endline @@ "[pos qual] " ^ (Formula.str_of qual);*)
                    (*ToDo*)if Formula.is_bind qual then [] else
                      let pos, neg = Formula.atoms_of qual in
                      List.map ~f:(fun qual -> pa, Formula.mk_atom qual) @@ Set.Poly.to_list @@ Set.Poly.union pos neg
                  else []) @
              List.concat_map neg_papp_tvs ~f:(fun (pa, pftv) ->
                  if Set.Poly.is_subset tvs ~of_:(Set.Poly.union pftv fvs)
                  (*&& (Set.Poly.is_empty fvs || match atomic with Atom.App (_, [t; _], _) -> Fn.non Term.is_bool_sort (Term.sort_of t) | _ -> false)*) then
                    (*let _ = print_endline @@ "neg" ^ string_of_int @@ Atom.ast_size atomic in
                      let _ = print_endline @@ "[atomic] " ^ (Atom.str_of atomic) in*)
                    let qual =
                      Z3Smt.Z3interface.qelim ~id fenv @@ Formula.forall (Set.Poly.to_list fvs) @@ Evaluator.simplify @@
                      (*Formula.mk_imply cond @@*)
                      Formula.mk_atom @@ atomic in
                    (*print_endline @@ "[neg qual] " ^ (Formula.str_of qual);*)
                    (*ToDo*)if Formula.is_bind qual then [] else
                      let pos, neg = Formula.atoms_of qual in
                      List.map ~f:(fun qual -> pa, Formula.mk_atom qual) @@ Set.Poly.to_list @@ Set.Poly.union pos neg
                  else [])))
    |> (fun quals ->
        if config.filter_out_quantified then
          List.filter quals ~f:(fun (_, phi) -> Fn.non Formula.is_bind @@ Evaluator.simplify phi)
        else quals)
    |> List.sort ~compare:(fun (key, _) (key', _) -> Stdlib.compare key key')
    |> List.group ~break:(fun (pa1, _) (pa2, _) -> Ident.pvar_compare (Atom.pvar_of pa1) (Atom.pvar_of pa2) <> 0)
    |> List.map ~f:(fun lst ->
        let pvar, sorts =
          match List.hd lst with
          | None -> failwith "each group must contains at least one term"
          | Some (pred, _) -> begin
              match pred with
              | Atom.App (Predicate.Var (pvar, sorts), _, _) -> pvar, sorts
              | _ -> assert false
            end
        in
        let params = sort_env_list_of_sorts sorts in
        let bool_quals =
          if config.add_bool then
            Set.Poly.filter_map (Set.Poly.of_list params) ~f:(fun (x, s) ->
                if Term.is_bool_sort s then Some (Set.Poly.empty, Formula.of_bool_var x)
                else None)
          else Set.Poly.empty
        in
        let extracted_quals =
          let terms = Term.of_sort_env params in
          Set.Poly.of_list @@
          List.filter_map lst ~f:(function
              | Atom.App (_, terms', _), atomic -> begin
                  (* assume here that elements of terms' are distinct variables
                     ohterwise no qualifier is extracted *)
                  try
                    let tvars =
                      List.map terms' ~f:(function
                          | Term.Var (x, _, _) -> x
                          | term -> failwith @@
                            Printf.sprintf "invalid term: %s @ Generator.extract" (Term.str_of term))
                    in
                    let tvs = Formula.tvs_of atomic in
                    let t_index_map = Map.Poly.of_alist_exn @@ List.mapi tvars ~f:(fun i x -> x, i) in
                    let ids = Set.Poly.map tvs ~f:(Map.Poly.find_exn t_index_map) in
                    let tsub = Map.Poly.of_alist_exn @@ List.zip_exn tvars terms in
                    let phi = Normalizer.normalize @@ Formula.subst tsub atomic in
                    if Set.Poly.is_empty @@ Formula.fvs_of phi then None else Option.some (ids, phi)
                  with _ -> None
                end
              | atom, _ -> failwith @@
                Printf.sprintf "fail with %s @ Generator.extract" (Atom.str_of ~priority:20 atom))
        in
        pvar, Set.Poly.union bool_quals extracted_quals)

  let qualifier_propagation (quals_map: (Ident.pvar, (int Set.Poly.t * Formula.t) Set.Poly.t) Map.Poly.t) =
    let open Logic in
    let rec same_args_id_of args1 args2 id1 = (** find ids in args1 and args2 of same args between args1 and args2 *)
      match args1 with
      | [] -> [], []
      | arg1::args1' ->
        match List.find_mapi args2 ~f:(fun i arg2 ->
            if Stdlib.(arg1 = arg2) then Some i else None) with 
        | Some id2 -> 
          let ids1, ids2 = same_args_id_of args1' args2 (id1 + 1) in 
          id1::ids1, id2::ids2
        | _ -> (same_args_id_of args1' args2 (id1 + 1))
    in
    let x_i i = Ident.Tvar (Printf.sprintf "x%d" (i + 1)) in
    let pcsp = PCSP.problem in
    let rec inner quals_map =
      (fun quals_map' ->
         if Map.Poly.equal (Set.Poly.equal) quals_map' quals_map then quals_map'
         else inner quals_map') @@
      Set.Poly.fold (Problem.clauses_of pcsp) ~init:quals_map ~f:(fun acc (_, ps, ns, _) ->
          let atms = Set.Poly.union ps ns in
          Set.Poly.fold atms ~init:acc ~f:(fun acc atm1 -> 
              let pvar1, args1 = ExtTerm.let_var_app atm1 in
              let pvar1 = Ident.tvar_to_pvar pvar1 in
              Set.Poly.fold atms ~init:acc ~f:(fun acc atm2 ->
                  let pvar2, args2 = ExtTerm.let_var_app atm2 in
                  let pvar2 = Ident.tvar_to_pvar pvar2 in
                  if Stdlib.(pvar1 = pvar2) then acc
                  else
                    match Map.Poly.find acc pvar2 with
                    | Some quals -> 
                      let ids1, ids2 = same_args_id_of args1 args2 0 in
                      Set.Poly.fold quals ~init:acc ~f:(fun acc (ids, qual) ->
                          if Fn.non Set.Poly.is_empty ids &&
                             Set.Poly.is_subset ids ~of_:(Set.Poly.of_list ids2) then
                            let subs =
                              List.fold2_exn ids1 ids2 ~init:Map.Poly.empty ~f:(fun acc id1 id2 ->
                                  let x1, x2 = x_i id1, x_i id2 in
                                  Map.Poly.update acc x2 ~f:(function None -> [x1] | Some xs -> x1::xs))
                              |> Map.Poly.fold ~init:[] ~f:(fun ~key ~data acc ->
                                  List.fold data ~init:[] ~f:(fun ret x -> 
                                      if List.is_empty acc then 
                                        [(key, x)]::ret 
                                      else 
                                        List.map acc ~f:(List.cons (key, x)) @ ret))
                              |> List.map ~f:(Map.Poly.of_alist_exn)
                            in
                            let quals = List.map subs ~f:(fun sub -> Set.Poly.of_list ids1, Formula.rename sub qual) |> Set.Poly.of_list in
                            Map.Poly.update acc pvar1 ~f:(function
                                | None -> quals
                                | Some data -> Set.Poly.union data quals)
                          else acc)
                    | _ -> acc)))
    in
    inner quals_map

  let extracted_qualifiers =
    if config.extract_pcsp then
      List.fold (extract pcsp) ~init:Map.Poly.empty ~f:(fun map (key, data) ->
          Map.Poly.update map key ~f:(function None -> data | Some data' -> Set.Poly.union data data'))
      |> qualifier_propagation
    else Map.Poly.empty

  let div_mod_filter (_, phi) =
    Fn.non Set.Poly.is_empty @@
    Set.Poly.inter
      (Set.Poly.of_list [T_int.Mod; T_int.Div])
      (Set.Poly.filter ~f:(Fn.non Term.is_fvar_sym) @@ Formula.funsyms_of phi)

  let generate pvar params labeled_atoms examples n =
    match List.nth domains n with
    | None -> failwith "generate"
    | Some (module Q) ->
      let sorts = List.map ~f:snd params in
      let extracted =
        Map.Poly.find extracted_qualifiers pvar
        |> Option.value ~default:Set.Poly.empty
        (* |> Set.Poly.filter ~f:(fun phi ->
           let fvs = Formula.fvs_of phi in
           not @@ Set.Poly.exists fvs ~f:(fun tvar ->
              not @@ List.exists params ~f:(fun (tvar1, _) -> Stdlib.(tvar = tvar1)))) *)
        |> Set.Poly.map ~f:(fun (_, phi) -> params, phi)
        |> (if config.add_neg then add_neg else Fn.id)
      in
      let generated =
        Q.qualifiers_of pvar sorts labeled_atoms examples
        |> (if config.add_homogeneous then add_homogeneous else Fn.id)
      in
      Set.Poly.union extracted generated
      |> (if config.filter_out_non_div_mod then Set.Poly.filter ~f:div_mod_filter else Fn.id)
      |> (if config.filter_out_neg then elim_neg else Fn.id)
  (*|> (fun quals -> if config.reduce then Q.reduce_qualifiers quals neg_ex pos_ex else quals)*)

  let str_of_domain n =
    match List.nth domains n with
    | None -> failwith "str_of_domain"
    | Some (module Q) -> Q.str_of_domain

  let num_of_domains = List.length domains
end