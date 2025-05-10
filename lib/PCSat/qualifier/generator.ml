open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open PCSP
open PCSatCommon

type qualifier = sort_env_list * Formula.t

module type QualifierType = sig
  val qualifiers_of :
    Ident.pvar ->
    Sort.t list ->
    (ExAtom.t * int) Set.Poly.t ->
    sort_env_map * VersionSpace.examples ->
    qualifier Set.Poly.t

  val str_of_domain : string
end

module type GeneratorType = sig
  val generate :
    Ident.pvar ->
    sort_env_list ->
    (ExAtom.t * int) Set.Poly.t ->
    sort_env_map * VersionSpace.examples ->
    int ->
    qualifier Set.Poly.t

  val elim_neg : qualifier Set.Poly.t -> qualifier Set.Poly.t
  val str_of_domain : int -> string
  val num_of_domains : int
end

module Config = struct
  type domain =
    | Null
    | Interval
    | Octagon
    | Octahedron
    | Polyhedron of int
    | Polynomial
    | SVM of int (* approx_level *) * float (* csvm *)
    | NN of
        int (* dummy parameter for neural network guided qualifier generation *)
    | Union of domain list
  [@@deriving yojson]

  type t = {
    verbose : bool;
    domains : domain list;
    extract_pcsp : bool;  (** extract qualifiers from pfwCSP *)
    normalize_pcsp : bool;  (** normalize pfwCSP to enhance extraction *)
    propagate_quals : bool;  (** propagate qualifiers *)
    add_bool : bool;  (** add qualifiers for boolean variables *)
    add_homogeneous : bool;  (** add homogeneous qualifiers *)
    add_neg : bool;  (** add negation of qualifiers *)
    filter_out_neg : bool;
    filter_out_non_div_mod : bool;
    filter_out_quantified : bool;
    reduce : bool;  (** reduce redundant qualifiers *)
  }
  [@@deriving yojson]

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid Generator Configuration (%s): %s" filename msg)

  module type ConfigType = sig
    val config : t
  end
end

module Make (Cfg : Config.ConfigType) (APCSP : Problem.ProblemType) :
  GeneratorType = struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id
  let print_log = false

  let pcsp =
    if config.normalize_pcsp then (
      Debug.print @@ lazy "normalizing pfwCSP for qualifiers extraction";
      let cls =
        Set.Poly.map
          (Problem.clauses_of APCSP.problem)
          ~f:(Clause.refresh_pvar_args (Problem.senv_of APCSP.problem))
      in
      (* normalization is essential for qualifiers extraction *)
      let count = ref 0 in
      Set.Poly.map cls ~f:(fun (uni_senv, ps, ns, phi) ->
          count := !count + 1;
          Debug.print
          @@ lazy
               (sprintf "normalizing %s clause (out of %d)"
                  (Ordinal.string_of @@ Ordinal.make !count)
                  (Set.length cls));
          (* assume that [phi] is alpha-renamed *)
          let phi =
            Normalizer.normalize_let
            @@ Logic.ExtTerm.to_old_fml
                 (Problem.senv_of APCSP.problem)
                 uni_senv phi
          in
          let uni_senv =
            (* Map.force_merge (Logic.Term.let_sort_env_of @@ Logic.ExtTerm.of_old_formula phi) *)
            uni_senv
          in
          let phi =
            Logic.ExtTerm.of_old_formula
            (* Z3Smt.Z3interface.simplify (Problem.fenv_of APCSP.problem) @@ *)
            @@ Evaluator.simplify
            @@
            (* Formula.elim_ite @@
                  Formula.elim_let_equivalid @@
                  Formula.elim_let *)
            phi
          in
          let senv = Map.force_merge (Problem.senv_of APCSP.problem) uni_senv in
          let bounds =
            Map.of_set_exn
            @@ Set.Poly.map ~f:(fun x -> (x, Map.Poly.find_exn senv x))
            @@ Set.concat_map ~f:Logic.Term.fvs_of (Set.union ps ns)
          in
          let uni_senv_phi, _, phi =
            Qelim.qelim bounds
              (Problem.senv_of APCSP.problem)
              (uni_senv, [], phi)
          in
          let uni_senv = Map.force_merge bounds uni_senv_phi in
          ( uni_senv,
            ps,
            ns,
            if Set.length ps + Set.length ns = 1 then phi
            else
              let fvs_phi = Logic.Term.fvs_of phi in
              Logic.ExtTerm.of_old_formula @@ Normalizer.normalize_let
              @@ LogicOld.Formula.or_of (*ToDo*) @@ Set.to_list
              @@ Set.Poly.map (Set.union ps ns) ~f:(fun atm ->
                     let fvs_atm = Logic.Term.fvs_of atm in
                     if Set.is_empty @@ Set.inter fvs_phi fvs_atm then
                       LogicOld.Formula.mk_false ()
                     else (
                       if print_log then (
                         print_endline
                           (sprintf "before QE: %s" @@ Formula.str_of
                           @@ Logic.ExtTerm.to_old_fml
                                (Problem.senv_of APCSP.problem)
                                uni_senv phi);
                         Out_channel.flush stdout);
                       let uni_senv', _, phi' =
                         let bounds =
                           Map.of_set_exn
                           @@ Set.Poly.map fvs_atm ~f:(fun x ->
                                  (x, Map.Poly.find_exn senv x))
                         in
                         Qelim.qelim bounds
                           (Problem.senv_of APCSP.problem)
                           (uni_senv, [], phi)
                       in
                       if print_log then print_endline "after QE";
                       LogicOld.Formula.alpha_rename_let
                       @@ Logic.ExtTerm.to_old_fml
                            (Problem.senv_of APCSP.problem)
                            uni_senv' phi')) ))
      |> Problem.of_clauses ~params:(Problem.params_of APCSP.problem)
      |> fun pcsp ->
      if print_log then print_endline (Problem.str_of pcsp);
      pcsp)
    else APCSP.problem

  let rec module_of_domain = function
    | Config.Null -> (module Null : QualifierType)
    | Interval -> (module Interval : QualifierType)
    | Octagon -> (module Octagon : QualifierType)
    | Octahedron -> (module Octahedron : QualifierType)
    | Polyhedron ub ->
        (module Polyhedron.Make (struct
          let upper_bound = ub
        end) : QualifierType)
    | Polynomial -> (module Polynomial : QualifierType)
    | SVM (approx_level, csvm) ->
        (module SVM.Make (struct
          let approx_level = approx_level
          let csvm = csvm
        end) : QualifierType)
    | NN dummy_param ->
        (module NN.Make (struct
          let dummy_param = dummy_param
        end) : QualifierType)
    | Union ds ->
        (module Union.Make (struct
          let domains = List.map ds ~f:module_of_domain
        end) : QualifierType)

  let domains = List.map config.domains ~f:module_of_domain

  let neg (params, phi) =
    (params, Normalizer.normalize @@ Evaluator.simplify_neg phi)

  let add_neg quals = Set.union quals @@ Set.Poly.map quals ~f:neg

  let elim_neg =
    if config.filter_out_neg then
      Set.fold ~init:Set.Poly.empty ~f:(fun quals q ->
          if Set.mem quals (neg q) then quals else Set.add quals q)
    else Fn.id

  let add_homogeneous quals =
    Set.union quals
    @@ Set.Poly.map quals ~f:(fun (params, phi) ->
           (params, Normalizer.homogenize phi))

  (* let rec mk_let_to_cond conds bvs fvs tvs lenv =
     let lenv' =
       Map.Poly.filteri lenv ~f:(fun ~key ~data ->
           Set.mem fvs (key, Term.sort_of data))
     in
     let conds' =
       Map.Poly.to_alist lenv'
       |> List.map ~f:(fun (var, def) ->
              Formula.eq (Term.mk_var var (Term.sort_of def)) def)
     in
     let tvs' =
       Set.union tvs
         (Set.Poly.union_list @@ List.map conds' ~f:Formula.sort_env_of)
     in
     let fvs' = Set.diff tvs' bvs in
     let conds' = Set.union conds (Set.Poly.of_list conds') in
     if Set.length fvs = Set.length fvs' then
       (tvs', fvs, Set.to_list conds' |> Formula.and_of)
     else mk_let_to_cond conds' bvs fvs' tvs' lenv *)

  let qelim_quals =
    List.map ~f:(fun (pa, quals) ->
        Debug.print
        @@ lazy
             (sprintf "eliminating quantifiers in qualifiers for %s"
                (Ident.name_of_pvar pa));
        ( pa,
          Set.fold quals ~init:Set.Poly.empty ~f:(fun acc (ids, phi) ->
              if false then
                Debug.print
                @@ lazy ("qualifier before qelim: " ^ Formula.str_of phi);
              let fenv = Problem.fenv_of pcsp in
              let phi' =
                (*Normalizer.normalize @@ Evaluator.simplify @@*)
                Z3Smt.Z3interface.qelim ~timeout:(Some 1000)
                  ~id:(Problem.id_of pcsp) ~fenv phi
              in
              if false then
                Debug.print
                @@ lazy ("qualifier after qelim: " ^ Formula.str_of phi');
              if config.filter_out_quantified && Formula.is_bind (*ToDo*) phi'
              then acc
              else
                Set.union acc
                @@ Set.Poly.map ~f:(fun atm ->
                       (ids (*ToDo*), Formula.mk_atom atm))
                @@ uncurry Set.union @@ Formula.atoms_of phi') ))

  let extract pcsp =
    let cls =
      Set.Poly.map (Problem.formulas_of pcsp)
        ~f:(uncurry2 @@ Logic.ExtTerm.to_old_fml (Problem.senv_of pcsp))
    in
    let count = ref 0 in
    Set.fold cls ~init:Set.Poly.empty ~f:(fun acc phi ->
        count := !count + 1;
        Debug.print
        @@ lazy
             (sprintf "extracting from %s clause (out of %d)"
                (Ordinal.string_of @@ Ordinal.make !count)
                (Set.length cls));
        if print_log then
          print_endline @@ sprintf "extract phi: %s" @@ Formula.str_of phi;
        let atomics, pos_papps, neg_papps =
          Formula.psym_pvar_apps_of ~simplifier:Evaluator.simplify phi
        in
        let pos_papp_tvs =
          List.map pos_papps ~f:(fun a -> (a, Atom.term_sort_env_of (*ToDo*) a))
        in
        let neg_papp_tvs =
          List.map neg_papps ~f:(fun a -> (a, Atom.term_sort_env_of (*ToDo*) a))
        in
        let bvs =
          Set.Poly.union_list @@ List.map ~f:snd @@ pos_papp_tvs @ neg_papp_tvs
        in
        if print_log then
          print_endline @@ sprintf "bvs: %s"
          @@ String.concat_map_set ~sep:", " bvs ~f:(fst >> Ident.name_of_tvar);
        (* (* assume that [phi] is alpha-renamed *)
           let lenv = Formula.let_env_of phi in *)
        List.fold atomics ~init:acc ~f:(fun acc atomic ->
            let tvs = Atom.sort_env_of atomic in
            if print_log then (
              print_endline @@ sprintf "extract atom: %s" @@ Atom.str_of atomic;
              print_endline @@ sprintf "tvs: %s"
              @@ String.concat_map_set ~sep:", " tvs
                   ~f:(fst >> Ident.name_of_tvar));
            let fvs = Set.diff tvs bvs in
            (* let tvs, fvs, cond =
                 mk_let_to_cond Set.Poly.empty bvs fvs tvs lenv
               in
               print_endline @@ "fvs: "
               ^ String.concat_map_set ~sep:", " fvs ~f:(fst >> Ident.name_of_tvar);
               print_endline @@ "cond: " ^ Formula.str_of cond; *)
            if
              Fn.non Set.is_empty
              @@ Set.inter (Set.Poly.map ~f:fst tvs)
                   (Map.key_set @@ Problem.senv_of pcsp)
              || Set.is_subset tvs
                   ~of_:fvs (* tvs and bvs has no common element *)
            then acc
            else
              let acc =
                List.fold pos_papp_tvs ~init:acc ~f:(fun acc (pa, pftv) ->
                    if
                      Set.is_subset tvs ~of_:(Set.union pftv fvs)
                      && Set.is_empty
                         @@ Set.inter (Set.Poly.map ~f:fst fvs)
                              (Set.concat_map (Atom.div_rem_of atomic)
                                 ~f:(fun (t1, t2) ->
                                   Set.union (Term.fvs_of t1) (Term.fvs_of t2)))
                    then (
                      if print_log then
                        print_endline
                        @@ sprintf "pos atom (%d): %s" (Atom.ast_size atomic)
                        @@ Atom.str_of atomic;
                      let atm =
                        let cnt = ref 0 in
                        Formula.aconv_tvar_norm (fun () ->
                            cnt := !cnt + 1;
                            Ident.Tvar ("#q" ^ string_of_int !cnt))
                        @@ Formula.exists (Set.to_list fvs)
                        @@ Evaluator.simplify (*Formula.mk_and cond @@*)
                        @@ Formula.mk_atom
                        @@
                        match Atom.negate atomic with
                        | None -> failwith "[extract]"
                        | Some neg_atom -> neg_atom
                      in
                      if print_log then
                        Debug.print
                        @@ lazy (sprintf "exi atomic: %s" @@ Formula.str_of atm);
                      Set.add acc (pa, atm))
                    else acc)
              in
              List.fold neg_papp_tvs ~init:acc ~f:(fun acc (pa, pftv) ->
                  if
                    Set.is_subset tvs ~of_:(Set.union pftv fvs)
                    && Set.is_empty
                       @@ Set.inter (Set.Poly.map ~f:fst fvs)
                            (Set.concat_map (Atom.div_rem_of atomic)
                               ~f:(fun (t1, t2) ->
                                 Set.union (Term.fvs_of t1) (Term.fvs_of t2)))
                  then (
                    if print_log then
                      print_endline
                      @@ sprintf "neg atom (%d): %s" (Atom.ast_size atomic)
                      @@ Atom.str_of atomic;
                    let atm =
                      let cnt = ref 0 in
                      Formula.aconv_tvar_norm (fun () ->
                          cnt := !cnt + 1;
                          Ident.Tvar ("#q" ^ string_of_int !cnt))
                      @@ Formula.forall (Set.to_list fvs)
                      @@ Evaluator.simplify
                      @@
                      (*Formula.mk_imply cond @@*)
                      Formula.mk_atom atomic
                    in
                    if print_log then
                      Debug.print
                      @@ lazy (sprintf "uni atomic: %s" @@ Formula.str_of atm);
                    Set.add acc (pa, atm))
                  else acc)))
    |> Set.group_by ~equiv:(fun (pa1, _) (pa2, _) ->
           Ident.pvar_equal (Atom.pvar_of pa1) (Atom.pvar_of pa2))
    |> List.map ~f:(fun lst ->
           let pvar, sorts =
             match Set.choose lst with
             | None -> failwith "each group must contains at least one term"
             | Some (Atom.App (Predicate.Var (pv, ss), _, _), _) -> (pv, ss)
             | Some (_, _) -> assert false
           in
           let params = sort_env_list_of_sorts sorts in
           let extracted_quals =
             Set.Poly.filter_map lst ~f:(function
               | Atom.App (_, args, _), atomic -> (
                   (* args are assumed to be distinct variables
                      ohterwise no qualifier is extracted *)
                   try
                     let tvars =
                       List.map args ~f:(function
                         | Term.Var (x, _, _) -> x
                         | term ->
                             failwith
                             @@ sprintf "[Generator.extract] invalid term: %s"
                                  (Term.str_of term))
                     in
                     let ids =
                       let t_index_map =
                         Map.Poly.of_alist_exn
                         @@ List.mapi tvars ~f:(fun i x -> (x, i))
                       in
                       Set.Poly.map (Formula.tvs_of atomic)
                         ~f:(Map.Poly.find_exn t_index_map)
                     in
                     if print_log then
                       Debug.print
                       @@ lazy
                            (sprintf "qualifier before sub: %s"
                            @@ Formula.str_of atomic);
                     let phi =
                       let tsub =
                         Map.Poly.of_alist_exn
                         @@ List.zip_exn tvars (Term.of_sort_env params)
                       in
                       Normalizer.normalize @@ Evaluator.simplify
                       @@ Formula.subst tsub atomic
                     in
                     if print_log then
                       Debug.print
                       @@ lazy
                            (sprintf "qualifier after sub: %s"
                            @@ Formula.str_of phi);
                     if Set.is_empty @@ Formula.fvs_of phi then None
                     else Some (ids, phi)
                   with _ -> None)
               | atom, _ ->
                   failwith
                   @@ sprintf "[Generator.extract] fail with %s"
                        (Atom.str_of ~priority:20 atom))
           in
           ( pvar,
             Set.union extracted_quals
               (if config.add_bool then
                  Set.Poly.filter_map (Set.Poly.of_list params)
                    ~f:(fun (x, s) ->
                      if Term.is_bool_sort s then
                        Some (Set.Poly.empty, Formula.of_bool_var x)
                      else None)
                else Set.Poly.empty) ))
    |> qelim_quals

  let qualifier_propagation
      (quals_map :
        (Ident.pvar, (int Set.Poly.t * Formula.t) Set.Poly.t) Map.Poly.t) =
    let open Ast.Logic in
    (* find ids in args1 and args2 of same args between args1 and args2 *)
    let rec same_args_id_of args1 args2 id1 =
      match args1 with
      | [] -> ([], [])
      | arg1 :: args1' -> (
          let ids1, ids2 = same_args_id_of args1' args2 (id1 + 1) in
          match
            List.find_mapi args2 ~f:(fun i arg2 ->
                if Stdlib.(arg1 = arg2) then Some i else None)
          with
          | Some id2 -> (id1 :: ids1, id2 :: ids2)
          | None -> (ids1, ids2))
    in
    let x_i i = Ident.Tvar (sprintf "x%d" (i + 1)) in
    let pairs =
      let cls = Problem.clauses_of APCSP.problem in
      let count = ref 0 in
      Set.fold cls ~init:Set.Poly.empty ~f:(fun acc (uni_senv, ps, ns, _) ->
          count := !count + 1;
          let atms = Set.union ps ns in
          Debug.print
          @@ lazy
               (sprintf
                  "propagating qualifiers across %s clause (out of %d) with %d \
                   atoms"
                  (Ordinal.string_of @@ Ordinal.make !count)
                  (Set.length cls) (Set.length atms));
          Set.fold_distinct_pairs atms ~init:acc ~f:(fun acc atm1 atm2 ->
              if print_log then
                Debug.print
                @@ lazy
                     (sprintf "comparing %s and %s"
                        (Atom.str_of
                        @@ ExtTerm.to_old_atm
                             (Problem.senv_of APCSP.problem)
                             uni_senv atm1)
                        (Atom.str_of
                        @@ ExtTerm.to_old_atm
                             (Problem.senv_of APCSP.problem)
                             uni_senv atm2));
              let pvar1, args1 = ExtTerm.let_var_app atm1 in
              let pvar2, args2 = ExtTerm.let_var_app atm2 in
              if Stdlib.(pvar1 = pvar2) then acc
              else
                let ids1, ids2 = same_args_id_of args1 args2 0 in
                let sub =
                  List.fold2_exn ids1 ids2 ~init:Map.Poly.empty
                    ~f:(fun acc id1 id2 ->
                      let x1, x2 = (x_i id1, x_i id2) in
                      Map.Poly.update acc x2
                        ~f:
                          Set.(
                            function
                            | None -> Poly.singleton x1
                            | Some xs -> add xs x1))
                in
                Set.add acc
                  ( Ident.tvar_to_pvar pvar1,
                    Ident.tvar_to_pvar pvar2,
                    sub,
                    Set.Poly.of_list ids1,
                    Set.Poly.of_list ids2 )))
    in
    let rec inner quals_map =
      let quals_map' =
        let count = ref 0 in
        Set.fold pairs ~init:quals_map
          ~f:(fun acc (pvar1, pvar2, sub, ids1_set, ids2_set) ->
            count := !count + 1;
            match Map.Poly.find acc pvar2 with
            | None -> acc
            | Some (_, _, quals) ->
                if Set.is_empty quals then acc
                else
                  let header = "###_" in
                  let sub =
                    Map.Poly.map sub
                      ~f:
                        (Set.Poly.map ~f:(fun (Ident.Tvar s) ->
                             Ident.Tvar (header ^ s)))
                  in
                  Debug.print
                  @@ lazy
                       (sprintf
                          "propagating %d qualifiers from %s to %s (%d/%d) \
                           (#sub = %d)"
                          (Set.length quals) (Ident.name_of_pvar pvar2)
                          (Ident.name_of_pvar pvar1) !count (Set.length pairs)
                          (Map.Poly.length sub));
                  let qs =
                    let sub1, sub2 =
                      Map.Poly.partition_map sub ~f:(function xs ->
                          if Set.is_singleton xs then First (Set.choose_exn xs)
                          else Second xs)
                    in
                    Set.concat_map quals ~f:(fun (ids, qual) ->
                        if
                          Fn.non Set.is_empty ids
                          && Set.is_subset ids ~of_:ids2_set
                        then
                          let init =
                            Set.Poly.singleton @@ Formula.rename sub1 qual
                          in
                          Set.Poly.map ~f:(fun q ->
                              if print_log then
                                Debug.print
                                @@ lazy (sprintf "qual: %s" @@ Formula.str_of q);
                              (ids1_set, q))
                          @@ Map.Poly.fold sub2 ~init ~f:(fun ~key ~data acc ->
                                 if print_log then
                                   Debug.print
                                   @@ lazy
                                        (sprintf "  %s -> %s"
                                           (Ident.name_of_tvar key)
                                           (String.concat_map_set data ~sep:","
                                              ~f:Ident.name_of_tvar));
                                 if
                                   Set.exists ids
                                     ~f:(x_i >> Ident.tvar_equal key)
                                 then
                                   Set.concat_map data ~f:(fun x ->
                                       let ren = Map.Poly.singleton key x in
                                       Set.Poly.map acc ~f:(Formula.rename ren))
                                 else acc)
                        else Set.Poly.empty)
                  in
                  let qs =
                    Set.Poly.map qs ~f:(fun (ids, q) ->
                        let ren =
                          Map.of_set_exn
                          @@ Set.Poly.map ids ~f:(fun i ->
                                 let xi = x_i i in
                                 ( Ident.Tvar (header ^ Ident.name_of_tvar xi),
                                   xi ))
                        in
                        (ids, Formula.rename ren q))
                  in
                  Map.Poly.update acc pvar1 ~f:(function
                    | None -> (qs, Set.Poly.empty, Set.Poly.empty)
                    | Some (added, processed, work) ->
                        ( Set.union added
                            (Set.diff qs (Set.union processed work)),
                          processed,
                          work )))
      in
      if Map.Poly.for_all quals_map' ~f:(Triple.fst >> Set.is_empty) then
        Map.Poly.map quals_map' ~f:(fun (_, processed, work) ->
            Set.union processed work)
      else
        inner
        @@ Map.Poly.map quals_map' ~f:(fun (added, processed, work) ->
               (Set.Poly.empty, Set.union processed work, added))
    in
    inner
    @@ Map.Poly.map quals_map ~f:(fun quals ->
           ( Set.Poly.empty (*added*),
             Set.Poly.empty (*processed*),
             quals (*work*) ))

  let extracted_qualifiers =
    if config.extract_pcsp then (
      Debug.print @@ lazy "*** extracting qualifiers";
      let extracted =
        List.fold (extract pcsp) ~init:Map.Poly.empty ~f:(fun map (key, d) ->
            Map.Poly.update map key ~f:(function
              | None -> d
              | Some d' -> Set.union d d'))
      in
      if config.propagate_quals then (
        Debug.print @@ lazy "*** propagating qualifiers";
        let propagated =
          Map.Poly.map ~f:elim_neg @@ qualifier_propagation extracted
        in
        Debug.print @@ lazy "done";
        propagated)
      else extracted)
    else Map.Poly.empty

  let div_mod_filter (_, phi) =
    Set.exists (Formula.funsyms_of phi) ~f:(function
      | T_int.(Div _ | Rem _) -> true
      | _ -> false)

  let generate pvar params labeled_atoms examples n =
    match List.nth domains n with
    | None -> failwith "generate"
    | Some (module Q) ->
        let extracted =
          Map.Poly.find extracted_qualifiers pvar
          |> Option.value ~default:Set.Poly.empty
          (* |> Set.filter ~f:(fun phi ->
             not @@ Set.exists (Formula.fvs_of phi) ~f:(fun tvar ->
                not @@ List.exists params ~f:(fun (tvar1, _) -> Stdlib.(tvar = tvar1)))) *)
          |> Set.Poly.map ~f:(fun (_, phi) -> (params, phi))
          |> if config.add_neg then add_neg else Fn.id
        in
        let generated =
          Q.qualifiers_of pvar (List.map ~f:snd params) labeled_atoms examples
          |> if config.add_homogeneous then add_homogeneous else Fn.id
        in
        Set.union extracted generated
        |> (if config.filter_out_non_div_mod then Set.filter ~f:div_mod_filter
            else Fn.id)
        |> Set.Poly.map ~f:(fun (params, phi) ->
               (params, Normalizer.normalize (*@@ Evaluator.simplify_neg*) phi))
        |> elim_neg
  (*|> (fun quals -> if config.reduce then Q.reduce_qualifiers quals neg_ex pos_ex else quals)*)

  let str_of_domain n =
    match List.nth domains n with
    | None -> failwith "str_of_domain"
    | Some (module Q) -> Q.str_of_domain

  let num_of_domains = List.length domains
end
