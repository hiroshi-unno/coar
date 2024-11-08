open Core
open Common.Ext
open Common.Combinator
open Logic

type t = sort_env_map * term Set.Poly.t * term Set.Poly.t * term
(* assume: (ps, ns, phi): for_all (union ps ns) (BoolTerm.is_pvar_app exi_senv) *)

let of_old_clause (uni_senv, pos, neg, phi) =
  ( uni_senv,
    Set.Poly.map pos ~f:ExtTerm.of_old_atom,
    Set.Poly.map neg ~f:ExtTerm.of_old_atom,
    ExtTerm.of_old_formula phi )

let to_old_clause exi_senv (uni_senv, pos, neg, phi) =
  ( uni_senv,
    Set.Poly.map pos ~f:(Fn.flip (ExtTerm.to_old_atom exi_senv uni_senv) []),
    Set.Poly.map neg ~f:(Fn.flip (ExtTerm.to_old_atom exi_senv uni_senv) []),
    ExtTerm.to_old_formula exi_senv uni_senv phi [] )

let to_formula ((_, ps, ns, phi) : t) =
  BoolTerm.or_of
  @@ (phi :: (Set.to_list @@ Set.union ps @@ Set.Poly.map ~f:BoolTerm.neg_of ns))

let to_old_formula exi_senv (uni_senv, ps, ns, phi) =
  ExtTerm.to_old_formula exi_senv uni_senv
    (to_formula (uni_senv, ps, ns, phi))
    []

let lift exi_senv f = of_old_clause @@ f @@ to_old_clause exi_senv
let unlift exi_senv f = to_old_clause exi_senv @@ f @@ of_old_clause
let sort_env_of ((senv, _, _, _) : t) = senv
let to_senv_formula c = (sort_env_of c, to_formula c)

let svs_of ((_, ps, ns, phi) : t) =
  Set.Poly.union_list
    [
      Term.svs_of ExtTerm.svs_of_sym ExtTerm.svs_of_sort phi;
      Set.concat_map ~f:(Term.svs_of ExtTerm.svs_of_sym ExtTerm.svs_of_sort) ps;
      Set.concat_map ~f:(Term.svs_of ExtTerm.svs_of_sym ExtTerm.svs_of_sort) ns;
    ]

let pvs_of ((_, ps, ns, _) : t) =
  Set.union
    (Set.Poly.map ps ~f:Term.pvar_of_atom)
    (Set.Poly.map ns ~f:Term.pvar_of_atom)

let fvs_of ((_, ps, ns, phi) : t) =
  Set.Poly.union_list
    [
      Term.fvs_of phi;
      Set.concat_map ~f:Term.fvs_of ps;
      Set.concat_map ~f:Term.fvs_of ns;
    ]

let is_goal ((_, ps, _, _) : t) = Set.is_empty ps

let is_definite pvar ((_, ps, _, _) : t) =
  Set.is_singleton ps
  &&
  match Set.choose ps with
  | None -> assert false
  | Some atm -> Stdlib.(pvar = Term.pvar_of_atom atm)

let is_co_definite pvar ((_, _, ns, _) : t) =
  Set.is_singleton ns
  &&
  match Set.choose ns with
  | None -> assert false
  | Some atm -> Stdlib.(pvar = Term.pvar_of_atom atm)

let pos_pvars ((_, ps, _, _) : t) = Set.Poly.map ps ~f:Term.pvar_of_atom
let neg_pvars ((_, _, ns, _) : t) = Set.Poly.map ns ~f:Term.pvar_of_atom

let pred_of_definite exi_senv (uni_senv, pos, neg, phi) =
  assert (Set.is_singleton pos);
  match Set.choose pos with
  | None -> assert false
  | Some atm ->
      let tvar, args = Term.let_var_app atm in
      let env =
        mk_fresh_sort_env_list @@ Sort.args_of
        @@ Map.Poly.find_exn exi_senv tvar
      in
      let neqs =
        List.map2_exn args env ~f:(fun arg (x, sort) ->
            Term.mk_apps (BoolTerm.mk_neq sort) [ arg; Term.mk_var x ])
      in
      let map = Map.of_list_exn env in
      let _, _, phi' =
        Qelim.qelim map exi_senv
        @@ ( Map.force_merge map uni_senv,
             [],
             BoolTerm.or_of @@ (phi :: neqs)
             @ List.map ~f:BoolTerm.neg_of
             @@ Set.to_list neg )
      in
      ( tvar,
        ( env,
          BoolTerm.(
            exists (Map.Poly.to_alist uni_senv) @@ nnf_of @@ neg_of phi') ) )

let pred_of_co_definite exi_senv (uni_senv, pos, neg, phi) =
  assert (Set.is_singleton neg);
  match Set.choose neg with
  | None -> assert false
  | Some atm ->
      let tvar, args = Term.let_var_app atm in
      let env =
        mk_fresh_sort_env_list @@ Sort.args_of
        @@ Map.Poly.find_exn exi_senv tvar
      in
      let neqs =
        List.map2_exn args env ~f:(fun arg (x, sort) ->
            Term.mk_apps (BoolTerm.mk_neq sort) [ arg; Term.mk_var x ])
      in
      let map = Map.of_list_exn env in
      let _, _, phi' =
        Qelim.qelim map exi_senv
        @@ ( Map.force_merge map uni_senv,
             [],
             BoolTerm.or_of @@ (phi :: neqs) @ Set.to_list pos )
      in
      (tvar, (env, BoolTerm.forall (Map.Poly.to_alist uni_senv) phi'))

(*let str_of cls = ExtTerm.str_of @@ to_formula cls*)
let str_of exi_senv (c : t) =
  ExtTerm.str_of_formula exi_senv (sort_env_of c) (to_formula c)

let simplify_with positive negative ((senv, c_pos, c_neg, c_phi) : t) =
  (* ToDo: improve this to exploit parametric examples *)
  let positive = Set.Poly.map ~f:snd positive in
  let negative = Set.Poly.map ~f:snd negative in
  if
    Set.is_empty (Set.inter positive c_pos)
    && Set.is_empty (Set.inter negative c_neg)
  then Some (senv, Set.diff c_pos negative, Set.diff c_neg positive, c_phi)
  else None

(* param_senv and uni_senv are disjoint *)
let resolve_one_step ~print mode (param_senv, (papp : term)) exi_senv
    ((uni_senv, c_pos, c_neg, c_phi) as cl : t) =
  print @@ lazy ("cl: " ^ str_of exi_senv cl);
  let atm1 =
    LogicOld.Atom.alpha_rename_let
    @@ ExtTerm.to_old_atom exi_senv param_senv papp []
  in
  let uni_senv' = Map.force_merge uni_senv param_senv in
  (if Stdlib.(mode = `Forward) then
     let _ = print @@ lazy "forward:" in
     c_neg
   else
     let _ = print @@ lazy "backward:" in
     c_pos)
  |> Set.Poly.filter_map ~f:(fun papp' ->
         let atm2 = ExtTerm.to_old_atom exi_senv uni_senv' papp' [] in
         print @@ lazy ("atm1: " ^ LogicOld.Atom.str_of atm1);
         print @@ lazy ("atm2: " ^ LogicOld.Atom.str_of atm2);
         let open Option.Monad_infix in
         LogicOld.Atom.unify (Map.key_set exi_senv) atm2 atm1
         >>= fun theta (*ToDo*) ->
         let theta = Map.Poly.map ~f:ExtTerm.of_old_term theta in
         let c_pos' =
           Set.Poly.map
             (if Stdlib.(mode = `Backward) then Set.remove c_pos papp'
              else c_pos)
             ~f:
               (ExtTerm.subst theta
               >> Fn.flip (ExtTerm.to_old_atom exi_senv uni_senv') []
               >> Normalizer.normalize_let_atom >> Normalizer.normalize
               >> ExtTerm.of_old_formula)
         in
         let c_neg' =
           Set.Poly.map
             (if Stdlib.(mode = `Forward) then Set.remove c_neg papp' else c_neg)
             ~f:
               (ExtTerm.subst theta
               >> Fn.flip (ExtTerm.to_old_atom exi_senv uni_senv') []
               >> Normalizer.normalize_let_atom >> Normalizer.normalize
               >> ExtTerm.of_old_formula)
         in
         let c_phi' =
           ExtTerm.subst theta c_phi
           |> Fn.flip (ExtTerm.to_old_formula exi_senv uni_senv') []
           |> Evaluator.simplify |> ExtTerm.of_old_formula
         in
         let cl' = (uni_senv', c_pos', c_neg', c_phi') in
         print @@ lazy ("cl': " ^ str_of exi_senv cl');
         Some
           ( cl',
             Map.Poly.map theta
               ~f:(Fn.flip (ExtTerm.to_old_term exi_senv uni_senv') []) ))

(* val resolve: Atom.t Set.Poly.t -> Atom.t Set.Poly.t -> t -> t Set.Poly.t *)
let resolve_one_step_all ~print positive negative exi_senv (c : t) =
  let cs_b =
    Set.Poly.map negative ~f:(fun neg ->
        resolve_one_step ~print `Backward neg exi_senv c)
  in
  let cs_f =
    Set.Poly.map positive ~f:(fun pos ->
        resolve_one_step ~print `Forward pos exi_senv c)
  in
  Set.union cs_b cs_f |> Set.concat
  |> Set.filter ~f:(fun ((_, _, _, t), _) -> Fn.non BoolTerm.is_true t)

let has_only_pure ((_, pos, neg, _) : t) = Set.is_empty pos && Set.is_empty neg
let is_unit ((_, pos, neg, _) : t) = Set.length pos + Set.length neg = 1

let is_query wfpvs fnpvs ((_, pos, _, _) : t) =
  Set.for_all pos ~f:(fun atm ->
      let p = BoolTerm.pvar_of_atom atm in
      Set.mem wfpvs p || Set.mem fnpvs p)

let refresh_pvar_args exi_senv ((senv, ps, ns, phi) : t) =
  let ps', pres =
    Set.unzip
    @@ Set.Poly.map ps ~f:(fun atm ->
           let pvar, args = Term.let_var_app atm in
           let env =
             mk_fresh_sort_env_list @@ Sort.args_of
             @@ Map.Poly.find_exn exi_senv pvar
           in
           ( Term.mk_var_app pvar @@ List.map env ~f:(fst >> Term.mk_var),
             ( env,
               List.map2_exn args env ~f:(fun arg (x, s) ->
                   Term.mk_apps (BoolTerm.mk_neq s) [ Term.mk_var x; arg ]) ) ))
  in
  let xss1, pneqss = Set.unzip pres in
  let ns', nres =
    Set.unzip
    @@ Set.Poly.map ns ~f:(fun atm ->
           let pvar, args = Term.let_var_app atm in
           let env =
             mk_fresh_sort_env_list @@ Sort.args_of
             @@ Map.Poly.find_exn exi_senv pvar
           in
           ( Term.mk_var_app pvar @@ List.map env ~f:(fst >> Term.mk_var),
             ( env,
               List.map2_exn args env ~f:(fun arg (x, s) ->
                   Term.mk_apps (BoolTerm.mk_neq s) [ Term.mk_var x; arg ]) ) ))
  in
  let xss2, nneqss = Set.unzip nres in
  let senv' =
    Map.force_merge senv
      (Map.of_set_exn
      @@ Set.concat_map ~f:Set.Poly.of_list (Set.union xss1 xss2))
  in
  ( senv',
    ps',
    ns',
    BoolTerm.or_of
    @@ (phi :: List.concat (Set.to_list pneqss))
    @ List.concat (Set.to_list nneqss) )

(*val refresh_tvar: (Atom.t list * Atom.t list * t) -> (Atom.t list * Atom.t list * t)*)
let refresh_tvar ((senv, ps, ns, phi) : t) =
  let map =
    Map.of_set_exn
    @@ Set.Poly.map (Map.key_set senv) ~f:(fun x -> (x, Ident.mk_fresh_tvar ()))
  in
  ( Map.rename_keys_map map senv,
    Set.Poly.map ~f:(Term.rename map) ps,
    Set.Poly.map ~f:(Term.rename map) ns,
    Term.rename map phi )

let fvs_new (_, ps, ns, phi) =
  Set.Poly.union_list
  @@ (ExtTerm.fvs_of phi :: List.map (Set.to_list ps) ~f:ExtTerm.fvs_of)
  @ List.map (Set.to_list ns) ~f:ExtTerm.fvs_of

let reduce_sort_map (senv, ps, ns, phi) =
  let ftvs = fvs_new (senv, ps, ns, phi) in
  (Map.Poly.filter_keys senv ~f:(Set.mem ftvs), ps, ns, phi)

let rename ren ((uni_senv, ps, ns, phi) : t) =
  ( uni_senv,
    Set.Poly.map ~f:(BoolTerm.rename ren) ps,
    Set.Poly.map ~f:(BoolTerm.rename ren) ns,
    phi )

let subst exi_senv sub ((uni_senv, ps, ns, phi) : t) : t =
  let ps1, ps2 =
    Set.partition_tf ~f:(BoolTerm.is_pvar_app exi_senv uni_senv)
    @@ Set.Poly.map ps ~f:(Term.subst sub)
  in
  let ns1, ns2 =
    Set.partition_tf ~f:(BoolTerm.is_pvar_app exi_senv uni_senv)
    @@ Set.Poly.map ns ~f:(Term.subst sub)
  in
  ( uni_senv,
    ps1,
    ns1,
    BoolTerm.or_of @@ Set.to_list
    @@ Set.Poly.union_list
         [
           ps2;
           Set.Poly.map ~f:BoolTerm.neg_of ns2;
           Set.Poly.singleton @@ Term.subst sub phi;
         ] )

let equal (c1 : sort_env_map * term Set.Poly.t * term Set.Poly.t * term) c2 =
  let env1, ps1, ns1, phi1 = c1 in
  let env2, ps2, ns2, phi2 = c2 in
  Map.Poly.equal Stdlib.( = ) env1 env2
  && Set.equal ps1 ps2 && Set.equal ns1 ns2
  && Stdlib.(phi1 = phi2)

let normalize_uni_senv ((senv, ps, ns, phi) : t) =
  (*Debug.print @@ lazy "a";*)
  let vars =
    List.map ~f:fst
    @@ List.sort
         ~compare:
           (curry @@ function
            | (_, Some n1), (_, Some n2) -> Int.compare n1 n2
            | (v1, _), (v2, _) ->
                String.compare (Ident.name_of_tvar v1) (Ident.name_of_tvar v2))
    @@
    let reg_number = Str.regexp "[^0-9]*" in
    List.map (Map.Poly.keys senv) ~f:(fun x ->
        ( x,
          try
            Some
              (Int.of_string
              @@ Str.global_replace reg_number ""
              @@ Ident.name_of_tvar x)
          with _ -> None ))
  in
  (*Debug.print @@ lazy "b";*)
  let sub =
    Map.Poly.of_alist_exn
    @@ List.mapi vars ~f:(fun i tvar -> (tvar, Ident.Tvar (sprintf "x%d" i)))
  in
  ( Map.rename_keys_and_drop_unused senv ~f:(Map.Poly.find sub),
    Set.Poly.map ps ~f:(ExtTerm.rename sub),
    Set.Poly.map ns ~f:(ExtTerm.rename sub),
    ExtTerm.rename sub phi )

let normalize_uni_senv_formula (senv, phi) =
  let senv, _, _, phi =
    normalize_uni_senv (senv, Set.Poly.empty, Set.Poly.empty, phi)
  in
  (senv, phi)

let ast_size_of ((_, ps, ns, phi) : t) =
  Set.fold ps ~init:0 ~f:(fun acc t -> 1 + acc + ExtTerm.ast_size t)
  + 1
  + Set.fold ns ~init:0 ~f:(fun acc t -> 1 + acc + ExtTerm.ast_size t)
  + 1 + ExtTerm.ast_size phi

let must_be_satisfied ?(print = fun _ -> ()) target_pvars
    pvars_the_target_pvar_depends_on clause =
  let pvars_of_the_clause_related_to_target_pvars =
    Set.Poly.filter_map (pvs_of clause) ~f:(fun clause_pvar ->
        Set.find target_pvars ~f:(Ident.is_related_tvar clause_pvar))
  in
  print
  @@ lazy
       (sprintf "check: [%s] <= [%s]"
          (Ident.str_of_tvars ~sep:","
             pvars_of_the_clause_related_to_target_pvars)
          (Ident.str_of_tvars ~sep:"," pvars_the_target_pvar_depends_on));
  (* if the following condition holds, (any non-dependent predicate variable never occurs negatively in the clause and thus)
      the candidate will never be qualified as a partial solution for the target pvar *)
  Set.is_subset pvars_of_the_clause_related_to_target_pvars
    ~of_:pvars_the_target_pvar_depends_on

let simplify exi_senv ((senv, ps, ns, phi) : t) =
  (senv, ps, ns, ExtTerm.simplify_formula exi_senv senv phi)
