open Common.Util
open Ast
open Ast.LogicOld
open PCSP
open PCSatCommon

type qualifier = SortEnv.t * Formula.t

module type QualifierType = sig
  val qualifiers_of: Ident.pvar -> Sort.t list -> (ExAtom.t * int) Set.Poly.t -> (SortMap.t * VersionSpace.examples) -> qualifier Set.Poly.t
  val str_of_domain: string
end

module type GeneratorType = sig
  val generate: Ident.pvar -> SortEnv.t -> (ExAtom.t * int) Set.Poly.t -> (SortMap.t * VersionSpace.examples) -> int -> qualifier list
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
    rank: bool; (** rank qualifiers *)
  } [@@ deriving yojson]

  let load_ext_file = function
    | ExtFile.Filename filename ->
      begin
        let open Core.Or_error in
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
          let senv = Logic.SortMap.merge (Problem.senv_of PCSP.problem) uni_senv in
          let phi = Logic.ExtTerm.of_old_formula @@ Logic.ExtTerm.to_old_formula senv phi [] in
          let bounds = 
            Logic.SortMap.of_set @@ Set.Poly.map ~f:(fun x -> x, Logic.SortMap.find_exn senv x) @@
            Set.concat_map (Set.Poly.union ps ns) ~f:Logic.Term.fvs_of
          in
          let uni_senv_phi, phi = Qelim.qelim bounds (Problem.senv_of PCSP.problem) (uni_senv, phi) in
          let uni_senv = Logic.SortMap.merge bounds uni_senv_phi in
          let phi' =
            if Set.Poly.length ps + Set.Poly.length ns = 1 then phi
            else
              Logic.BoolTerm.or_of @@ Set.Poly.to_list @@
              Set.Poly.map (Set.Poly.union ps ns) ~f:(fun atm ->
                  let bounds =
                    Logic.SortMap.of_set @@ Set.Poly.map ~f:(fun x -> x, Logic.SortMap.find_exn senv x) @@
                    Logic.Term.fvs_of atm
                  in
                  snd @@ Qelim.qelim bounds (Problem.senv_of PCSP.problem) (uni_senv, phi))
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
    | Union ds -> (module Union.Make (struct let domains = List.map ds ~f:module_of_domain end) : QualifierType)

  let domains = List.map config.domains ~f:module_of_domain

  let neg (params, phi) = params, Normalizer.normalize @@ Evaluator.simplify_neg phi
  let add_neg quals = Set.Poly.union quals (Set.Poly.map quals ~f:neg)
  let elim_neg quals = Set.Poly.fold quals ~init:Set.Poly.empty ~f:(fun quals q ->
      if Set.Poly.mem quals (neg q) then quals else Set.Poly.add quals q)
  let add_homogeneous quals = Set.Poly.union quals
      (Set.Poly.map quals ~f:(fun (params, phi) -> params, Normalizer.homogenize phi))

  let extract pcsp =
    let exi_senv = Problem.senv_of pcsp in
    let fenv = Problem.fenv_of pcsp in
    Set.Poly.map (Problem.formulas_of pcsp) ~f:(fun (uni_senv, phi) ->
        Logic.ExtTerm.to_old_formula (Logic.SortMap.merge exi_senv uni_senv) phi [])
    |> Set.Poly.to_list
    |> List.concat_map ~f:(fun phi ->
        let atomics, pos_papps, neg_papps = Formula.psym_pvar_apps_of phi in
        let pos_papp_tvs = List.map pos_papps ~f:(fun a -> (a, Atom.term_sort_env_of(*ToDo*) a)) in
        let neg_papp_tvs = List.map neg_papps ~f:(fun a -> (a, Atom.term_sort_env_of(*ToDo*) a)) in
        let bvs = Set.Poly.union_list @@ List.map ~f:(fun (_, s) -> s) @@ (pos_papp_tvs @ neg_papp_tvs) in
        List.concat_map atomics ~f:(fun atomic ->
            let tvs = Atom.sort_env_of atomic in
            let fvs = Set.Poly.diff tvs bvs in
            if not @@ Set.Poly.is_empty @@ Set.Poly.inter (Set.Poly.map ~f:fst tvs) (Map.key_set exi_senv) ||
               Set.Poly.is_subset tvs ~of_:fvs(* tvs and bvs has no common element *) then []
            else
              List.filter_map pos_papp_tvs ~f:(fun (pa, pftv) ->
                  if Set.Poly.is_subset tvs ~of_:(Set.Poly.union pftv fvs) (*&&
                                                                             (Set.Poly.is_empty fvs || match atomic with Atom.App (_, [t; _], _) -> Stdlib.(<>) (Term.sort_of t) T_bool.SBool | _ -> false)*) then
                    let qual = Z3Smt.Z3interface.qelim fenv @@ Formula.exists (SortEnv.of_set fvs) @@ Formula.mk_atom @@ Atom.negate atomic in
                    (*ToDo*)if Formula.is_bind qual then None else Some (pa, qual)
                  else None) @
              List.filter_map neg_papp_tvs ~f:(fun (pa, pftv) ->
                  if Set.Poly.is_subset tvs ~of_:(Set.Poly.union pftv fvs) (*&&
                                                                             (Set.Poly.is_empty fvs || match atomic with Atom.App (_, [t; _], _) -> Stdlib.(<>) (Term.sort_of t) T_bool.SBool | _ -> false)*) then
                    let qual = Z3Smt.Z3interface.qelim fenv @@ Formula.forall (SortEnv.of_set fvs) @@ Formula.mk_atom @@ atomic in
                    (*ToDo*)if Formula.is_bind qual then None else Some (pa, qual)
                  else None)))
    |> (fun quals -> if config.filter_out_quantified then (List.filter quals ~f:(fun (_, phi) -> not @@ Formula.is_bind @@ Evaluator.simplify phi)) else quals)
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
        let params = SortEnv.of_sorts sorts in
        let terms = Term.of_sort_env params in
        pvar,
        Set.Poly.union
          (if config.add_bool then
             Set.Poly.filter_map (SortEnv.set_of params) ~f:(fun (x, s) ->
                 if Stdlib.(=) s T_bool.SBool then Some (Formula.of_bool_var x) else None)
           else Set.Poly.empty)
          (Set.Poly.of_list @@
           List.filter_map lst ~f:(function
               | Atom.App (_, terms', _), atomic ->
                 begin
                   (* assume here that elements of terms' are distinct variables
                      ohterwise no qualifier is extracted *)
                   try
                     let tvars =
                       List.map terms' ~f:(function
                           | Term.Var (x, _, _) -> x
                           | term -> failwith @@
                             Printf.sprintf "invalid term: %s @ Generator.extract" (Term.str_of term)) in
                     let tsub = Map.Poly.of_alist_exn @@ List.zip_exn tvars terms in
                     let phi = Normalizer.normalize @@ Formula.subst tsub atomic in
                     if Set.Poly.is_empty @@ Formula.fvs_of phi then None else Option.some phi
                   with _ -> None
                 end
               | atom, _ -> failwith @@
                 Printf.sprintf "fail with %s @ Generator.extract" (Atom.str_of ~priority:20 atom))))

  let extracted_qualifiers =
    if config.extract_pcsp
    then
      List.fold (extract pcsp) ~init:Map.Poly.empty ~f:(fun map (key, data) ->
          Map.Poly.update map key ~f:(function None -> data | Some data' -> Set.Poly.union data data'))
    else Map.Poly.empty

  let div_mod_filter (_, phi) =
    not @@ Set.Poly.is_empty @@
    Set.Poly.inter
      (Set.Poly.of_list [T_int.Mod; T_int.Div])
      (Set.Poly.filter ~f:(fun sym -> not @@ Term.is_fvar_sym sym) @@ Formula.funsyms_of phi)

  let generate pvar params labeled_atoms examples n =
    match List.nth domains n with
    | None -> failwith "generate"
    | Some (module Q) -> 
      let sorts = SortEnv.sorts_of params in
      let extracted =
        Map.Poly.find extracted_qualifiers pvar
        |> Option.value ~default:Set.Poly.empty
        |> Set.Poly.map ~f:(fun phi -> params, phi)
        |> (if config.add_neg then add_neg else Core.ident)
      in
      let generated =
        Q.qualifiers_of pvar sorts labeled_atoms examples
        |> (if config.add_homogeneous then add_homogeneous else Core.ident)
      in
      Set.Poly.union extracted generated
      |> (if config.filter_out_non_div_mod then Set.Poly.filter ~f:div_mod_filter else Core.ident)
      |> (if config.filter_out_neg then elim_neg else Core.ident)
      (*|> (fun quals -> if config.reduce then Q.reduce_qualifiers quals neg_ex pos_ex else quals)*)
      |> if config.rank then Rank.sort_by_rank else Set.Poly.to_list

  let str_of_domain n =
    match List.nth domains n with
    | None -> failwith "str_of_domain"
    | Some (module Q) -> Q.str_of_domain

  let num_of_domains = List.length domains
end