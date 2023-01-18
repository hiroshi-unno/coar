open Core
open Typedtree
open Common
open Common.Ext
open Ast
open Ast.Ident
open Ast.LogicOld
open Ast.ConstDatatype

module Make (Config : Config.ConfigType) = struct
  let config = Config.config

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))
  let _ = Debug.set_module_name "Cgen"
  module MBcgen = MBcgen.Make (Config)
  module MBcsol = MBcsol.Make (Config)

  type constr = Formula.t
  type item =
    | Skip
    | Constraints of constr Set.Poly.t
    (* [@@@smtlib2 "some smtlib2 code"] *)
    | Smtlib of Formula.t Set.Poly.t(* phis *) *
                (pvar * Sort.t list) Set.Poly.t(* pvs *) *
                (pvar * Sort.t list) Set.Poly.t(* fnpvs *) *
                (pvar * Sort.t list) Set.Poly.t(* wfpvs *)
    (* [@@@assert "type_of(main) <: int -> unit "] *)
    | Check of (tvar * Problem.assertion) list

  (** Refinement Type Inference *)

  let cgen_subeff_temp ~config renv ((x1, phi1), (y1, psi1)) ((x2, phi2), (y2, psi2)) =
    let open Rtype in
    if config.Rtype.enable_temp_eff then begin
      Debug.print @@ lazy
        (sprintf "[rcaml:cgen_subeff_temp]\n%s\n  |- (%s)  <:  (%s)"
           (Env.str_of ~config renv) (str_of_temp_eff ((x1, phi1), (y1, psi1)))
           (str_of_temp_eff ((x2, phi2), (y2, psi2))));
      let constrs =
        Set.Poly.of_list
          [Formula.mk_imply
             (Evaluator.simplify @@ constr_of ~print:Debug.print ~config @@ Env.add_phi renv @@
              snd @@ Formula.split_exists @@ Formula.rename (Map.Poly.singleton x1 x2) phi1)
             (Evaluator.simplify phi2);
           Formula.mk_imply
             (Evaluator.simplify @@ constr_of ~print:Debug.print ~config @@ Env.add_phi renv @@
              snd @@ Formula.split_exists @@ Formula.rename (Map.Poly.singleton y1 y2) psi1)
             (Evaluator.simplify psi2)]
      in
      Debug.print @@ lazy
        (sprintf "[rcaml:cgen_subeff_temp] constraints:\n  %s\n"
           (String.concat_set ~sep:"\n  " @@ Set.Poly.map constrs ~f:Formula.str_of));
      constrs
    end else Set.Poly.empty
  let rec cgen_subeff_cont ~config renv t es s1 s2 = let open Rtype in
    if config.enable_temp_eff then
      Debug.print @@ lazy
        (sprintf "[rcaml:cgen_subeff_cont]\n%s\n| %s & %s\n  |- %s  <:  %s"
           (Env.str_of ~config renv) (str_of_val ~config t)
           (str_of_temp_eff @@ compose_temp_eff es)
           (str_of_cont_eff ~config s1) (str_of_cont_eff ~config s2))
    else
      Debug.print @@ lazy
        (sprintf "[rcaml:cgen_subeff_cont]\n%s\n| %s \n  |- %s  <:  %s"
           (Env.str_of ~config renv) (str_of_val ~config t)
           (str_of_cont_eff ~config s1) (str_of_cont_eff ~config s2));
    let constrs =
      match s1, s2 with
      | Pure, Pure -> Set.Poly.empty
      | Eff (x1, c11, c12), Eff (x2, c21, c22) ->
        let c11 = rename_comp_type (Map.Poly.singleton x1 x2) c11 in
        let renv' = Env.disj_union renv @@ Env.singleton_ty x2 t in
        Set.Poly.union (cgen_subtype_comp ~config renv' c21 c11) @@
        cgen_subtype_comp ~config renv c12 c22
      | Pure, Eff (x, c1, c2) ->
        let renv' = Env.disj_union renv @@ Env.singleton_ty x t in
        Set.Poly.union
          (cgen_subtype_comp ~config renv' (compose_temp_comp es c1) c2) @@
        if config.Rtype.enable_temp_eff then begin
          let _, (y, phi) = compose_temp_eff es in
          Set.Poly.singleton @@ Formula.mk_imply
            (Evaluator.simplify @@ constr_of ~print:Debug.print ~config @@ Env.add_phi renv @@
             snd @@ Formula.split_exists(*ToDo*) phi)
            (Evaluator.simplify @@ nu_of_comp y c2)
        end else Set.Poly.empty
      | _ ->
        failwith @@ sprintf "[rcaml:cgen_subeff_cont] %s and %s "
          (str_of_cont_eff ~config s1) (str_of_cont_eff ~config s2)
    in
    Debug.print @@ lazy
      (sprintf "[rcaml:cgen_subeff_cont] constraints:\n  %s\n"
         (String.concat_set ~sep:"\n  " @@ Set.Poly.map constrs ~f:Formula.str_of));
    constrs
  and cgen_subtype_opsig ~config renv (o1: Rtype.o) (o2: Rtype.o) =
    let open Rtype in
    Debug.print @@ lazy
      (sprintf "[rcaml:cgen_subtype_opsig]\n%s\n  |- %s  <:  %s"
         (Env.str_of ~config renv) (str_of_opsig ~config o1) (str_of_opsig ~config o2));
    let constrs =
      let _lefts, boths, rights = Common.Util.ALMap.split_lbr o1 o2 in
      if (* List.is_empty lefts && *) List.is_empty rights then
        Set.Poly.union_list @@ List.map boths ~f:(fun (_op, (t1, t2)) ->
            cgen_subtype_val ~config renv t1 t2)
      else
        failwith @@ sprintf "[rcaml:cgen_subtype_opsig] %s and %s"
          (str_of_opsig ~config o1) (str_of_opsig ~config o2)
    in
    Debug.print @@ lazy
      (sprintf "[rcaml:cgen_subtype_opsig] constraints:\n  %s\n"
         (String.concat_set ~sep:"\n  " @@ Set.Poly.map constrs ~f:Formula.str_of));
    constrs
  and cgen_subtype_comp ~config renv
      ((o1, t1, e1, s1) as c1 : Rtype.c)
      ((o2, t2, e2, s2) as c2 : Rtype.c) = let open Rtype in
    Debug.print @@ lazy
      (sprintf "[rcaml:cgen_subtype_comp]\n%s\n  |- %s  <:  %s"
         (Env.str_of ~config renv) (str_of_comp ~config c1) (str_of_comp ~config c2));
    let constrs =
      Set.Poly.union_list
        [cgen_subtype_val ~config renv t1 t2;
         cgen_subtype_opsig ~config renv o2 o1;
         cgen_subeff_temp ~config renv e1 e2;
         cgen_subeff_cont ~config renv t1 [e1] s1 s2]
    in
    Debug.print @@ lazy
      (sprintf "[rcaml:cgen_subtype_comp] constraints:\n  %s\n"
         (String.concat_set ~sep:"\n  " @@ Set.Poly.map constrs ~f:Formula.str_of));
    constrs
  and cgen_subtype_val ~config renv (t1:Rtype.t) (t2:Rtype.t) = let open Rtype in
    Debug.print @@ lazy
      (sprintf "[rcaml:cgen_subtype_val]\n%s\n  |- %s  <:  %s"
         (Env.str_of ~config renv) (str_of_val ~config t1) (str_of_val ~config t2));
    let imply (v1, phi1) (v2, phi2) =
      Formula.mk_imply
        (Evaluator.simplify @@ constr_of ~print:Debug.print ~config @@ Env.add_phi renv @@
         snd @@ Formula.split_exists(*ToDo*) @@ Formula.rename (Map.Poly.singleton v1 v2) phi1)
        (Evaluator.simplify phi2)
    in
    let constrs =
      match t1, t2 with
      | RGeneral (params1, _sort1, pred1), RGeneral (params2, _sort2, pred2)
        when List.length params1 = List.length params2 ->
        Set.Poly.add
          (** assume type parameters are all invariant *)
          (Set.Poly.union_list @@
           (List.map2_exn params1 params2 ~f:(cgen_subtype_val ~config renv) @
            List.map2_exn params2 params1 ~f:(cgen_subtype_val ~config renv)))
          (imply pred1 pred2)
      | RTuple (ts1, pred1), RTuple (ts2, pred2) ->
        Set.Poly.add
          (Set.Poly.union_list @@ List.map2_exn ts1 ts2 ~f:(cgen_subtype_val ~config renv))
          (imply pred1 pred2)
      | RArrow (v1, t1, c1, pred1), RArrow (v2, t2, c2, pred2) ->
        let c1' =
          subst_comp_type (Map.Poly.singleton v1 @@ Term.mk_var v2 @@ sort_of_val t2) c1
        in
        Set.Poly.add
          (Set.Poly.union
             (cgen_subtype_val ~config renv t2 t1)
             (cgen_subtype_comp ~config (Env.disj_union renv @@ Env.singleton_ty v2 t2) c1' c2))
          (imply pred1 pred2)
      (*| RForall (_penv1, _phis1, _c1), RForall (_penv2, _phis2, _c2) -> failwith "not supported"
        (* ToDo: forall penv2 exists penv1. phis2 => phis1 /\ cgen_subtype_comp renv c1 c2 *)*)
      | _ ->
        Debug.print @@ lazy ("[rcaml:cgen_subtype_val] env:\n" ^ Env.str_of ~config renv);
        failwith @@ sprintf "[rcaml:cgen_subtype_val] %s <: %s"
          (str_of_val ~config t1) (str_of_val ~config t2)
    in
    Debug.print @@ lazy
      (sprintf "[rcaml:cgen_subtype_val] constraints:\n  %s\n"
         (String.concat_set ~sep:"\n  " @@ Set.Poly.map constrs ~f:Formula.str_of));
    constrs

  let rec compose_cont_eff ~config = let open Rtype in function
      | [] ->(*ToDo:reachable here?*) Set.Poly.empty, Pure
      | [_, _, _, First _] -> Set.Poly.empty, Pure
      | [_, _, _, Second s] -> Set.Poly.empty, s

      | [(pat1, _renv1, _t1, Second (Eff (x1, c1, c2))); (_pat2, renv2, t2, First es)] ->
        (* renv2, x2 : t2 |- es c3 <: [pat1/x1]c1
           renv2 |- es^nu => [pat1/x1]c1^nu
           --------------------------------------------------
           renv2 | t2 & es |- Pure <: (x2. c3) => [pat1/x1]c1 *)
        let c1 =
          let tsub = Map.Poly.singleton x1 @@ Pattern.term_of pat1 in
          subst_comp_type tsub c1
        in
        let x2 = mk_fresh_tvar_with "x2_" in
        let renv2' = Env.set_ty renv2 x2 t2 (* [t2] can depend on x2 *) in
        let constrs, c3 =
          if true then
            let c3 =
              let dom = Env.dep_args_of renv2' in
              (*Debug.print @@ lazy ("renv: " ^ Env.str_of ~config renv');*)
              let opsig, sort, cont = full_sort_of_comp c1 in
              comp_type_of ~config ~temp:true ~opsig:(`Sort opsig) ~cont dom @@
              val_type_of_sort ~config dom sort
            in
            cgen_subtype_comp ~config renv2' (compose_temp_comp es c3) c1,
            c3
          else
            (* the following avoids introducing a fresh predicate variable but imcomplete *)
            compose_temp_comp_inv ~print:Debug.print ~config renv2' (compose_temp_eff es) c1
        in
        Debug.print @@ lazy
          (sprintf "composed cont eff: %s\n" @@ str_of_cont_eff ~config @@ Eff (x2, c3, c2));
        Set.Poly.union constrs @@
        (if config.enable_temp_eff then
           let _, (y, phi) = compose_temp_eff es in
           Set.Poly.singleton @@ Formula.mk_imply
             (Evaluator.simplify @@ constr_of ~print:Debug.print ~config @@ Env.add_phi renv2 @@
              snd @@ Formula.split_exists(*ToDo*) phi)
             (Evaluator.simplify @@ nu_of_comp y c1)
         else Set.Poly.empty),
        (* we can omit existential quantification over x2 in c1
           because the type is only used by cgen_subeff negatively *)
        Eff (x2, c3, c2)

      | (_, _, _, First es1) :: (pat2, renv2, t2, First es2) :: ss -> (*ToDo*)
        compose_cont_eff ~config @@ (pat2, renv2, t2, First (es1 @ es2)) :: ss
      | ((_, _, _, Second _) as s1) ::
        (_, _, _, First es1) :: (pat2, renv2, t2, First es2) :: ss -> (*ToDo*)
        compose_cont_eff ~config @@ s1 :: (pat2, renv2, t2, First (es1 @ es2)) :: ss

      | (_pat1, renv1, _t1, First es) :: (pat2, renv2, t2, Second (Eff (x, c1, c2))) :: ss ->
        (* renv1, pat1 : t1 |- es c2 <: c3    renv1 |- es^nu => c3^nu
           -------------------------------------------------------
                 renv1 | t1 & es |- Pure <: (pat1. c2) => c3 *)
        let c3 = compose_temp_comp es c2 in
        (* we can omit existential quantification over pat1 in c3
           because the type is only used by cgen_subeff negatively *)
        let s = Eff (x, c1, c3) in
        let constrs, s = compose_cont_eff ~config @@ (pat2, renv2, t2, Second s) :: ss in
        Set.Poly.union constrs @@
        (if config.enable_temp_eff then
           let _, (y, phi) = compose_temp_eff es in
           Set.Poly.singleton @@ Formula.mk_imply
             (Evaluator.simplify @@ constr_of ~print:Debug.print ~config @@ Env.add_phi renv1 @@
              snd @@ Formula.split_exists(*ToDo*) phi)
             (Evaluator.simplify @@ nu_of_comp y c3)
         else Set.Poly.empty),
        s
      | ((_, _, _, Second _) as s1) ::
        (_pat1, renv1, _t1, First es) :: (pat2, renv2, t2, Second (Eff (x, c1, c2))) :: ss ->
        let c3 = compose_temp_comp es c2 in
        (* we can omit existential quantification over pat1 in c3
           because the type is only used by cgen_subeff negatively *)
        let s = Eff (x, c1, c3) in
        let constrs, s =
          compose_cont_eff ~config @@ s1 :: (pat2, renv2, t2, Second s) :: ss
        in
        Set.Poly.union constrs @@
        (if config.enable_temp_eff then
           let _, (y, phi) = compose_temp_eff es in
           Set.Poly.singleton @@ Formula.mk_imply
             (Evaluator.simplify @@ constr_of ~print:Debug.print ~config @@ Env.add_phi renv1 @@
              snd @@ Formula.split_exists(*ToDo*) phi)
             (Evaluator.simplify @@ nu_of_comp y c3)
         else Set.Poly.empty),
        s

      | (pat1, _renv1, _t1, Second (Eff (x1, c11, c12))) ::
        (pat2, renv2, t2, Second (Eff (x2, c21, c22))) :: ss ->
        let c11 =
          let tsub = Map.Poly.singleton x1 @@ Pattern.term_of pat1 in
          subst_comp_type tsub c11
        in
        let constrs, s =
          compose_cont_eff ~config ((pat2, renv2, t2, Second (Eff (x2, c21, c12))) :: ss)
        in
        Set.Poly.union constrs @@ cgen_subtype_comp ~config renv2 c22 c11,
        s
      | _ -> failwith "compose_cont_eff"
  let cgen_compose_temp_eff ~config renv es e = let open Rtype in
    if config.enable_temp_eff then
      [cgen_subeff_temp ~config renv (compose_temp_eff es) e]
    else []
  let cgen_compose_cont_eff ~config renv ss (t, es) s =
    let constrs, s' = compose_cont_eff ~config ss in
    constrs :: [cgen_subeff_cont ~config renv t es s' s]

  let cgen_subeff ~config renv rev_tys t' (o, t, e, s) = let open Rtype in
    let tys = List.rev rev_tys in
    Debug.print @@ lazy
      (sprintf "[rcaml:cgen_subeff]\n%s" @@
       List.fold_right tys ~init:(str_of_comp ~config (o, t, e, s))
         ~f:(fun (pat, _renv, c) str ->
             sprintf "let %s : %s in\n%s"
               (Pattern.str_of pat) (str_of_comp ~config c) str));
    let constrs =
      (* assume that all opsigs in [tys] are empty or the same as [o]
        (i.e. they are supertypes of [o]) *)
      let es = List.map tys ~f:(fun (_, _, (_, _, e, _)) -> e) in
      let ss = List.map tys ~f:(fun (pat, renv, (_, t, e, s)) ->
          pat, renv, t, match s with Pure -> First [e] | Eff _ -> Second s) in
      Set.Poly.union_list @@
      cgen_compose_temp_eff ~config renv es e @
      cgen_compose_cont_eff ~config renv ss (t', es) s
    in
    Debug.print @@ lazy
      (sprintf "[rcaml:cgen_subeff] constraints:\n  %s\n"
         (String.concat_set ~sep:"\n  " @@ Set.Poly.map constrs ~f:Formula.str_of));
    constrs

  let cgen_check_pure ~config renv (o, t, e, s) =
    Debug.print @@ lazy
      (sprintf "[rcaml:cgen_check_pure] %s" @@ Rtype.str_of_comp ~config (o, t, e, s));
    let e_val = Rtype.mk_temp_eff_val () in
    (* o can be any opsig because empty opsig is a supertype of any opsig *)
    let constrs =
      Set.Poly.union
        (cgen_subeff_temp ~config renv e_val e)
        (cgen_subeff_cont renv ~config t [e_val] Pure s)
    in
    Debug.print @@ lazy
      (sprintf "[rcaml:cgen_check_pure] constraints:\n  %s\n"
         (String.concat_set ~sep:"\n  " @@ Set.Poly.map constrs ~f:Formula.str_of));
    constrs

  (** assume [pat] is instantiated to [sort_of_val rty] *)
  let rec pattern_match_with ~config (pat:Pattern.t) (renv, term, (rty:Rtype.t)) =
    match pat, rty with
    | PAny _, _ ->
      Rtype.Env.mk_empty (),
      Set.Poly.empty,
      (* always match *)Formula.mk_false ()
    | PVar (x, _), _ ->
      (*assert Stdlib.(sort = Rtype.sort_of_val rty);*)
      Rtype.Env.add_phi (Rtype.Env.singleton_ty x rty) @@
      Formula.eq term @@ Term.mk_var x @@ Rtype.sort_of_val rty,
      Set.Poly.empty,
      (* always match *)Formula.mk_false ()
    | PTuple pats, RTuple (ts, _pred) ->
      let sorts = List.map ~f:Rtype.sort_of_val ts in
      let renvs, constrss, not_matched =
        List.unzip3 @@ List.map2i (fun i pi ti ->
            pattern_match_with ~config pi (renv, T_tuple.mk_tuple_sel sorts term i, ti))
          pats ts
      in
      Rtype.Env.disj_union_list renvs (* assume renvs are distinct *),
      Set.Poly.union_list constrss,
      Formula.or_of @@ (Formula.mk_atom @@ T_tuple.mk_is_not_tuple sorts term) :: not_matched
    | PCons (dt, cons_name, pats), RGeneral (params, _, _pred) ->
      (*Debug.print @@ lazy cons_name;*)
      let cty(* may contain a predicate variable *), constrs =
        let cty = Rtype.of_constructor ~print:Debug.print ~config cons_name dt in
        (* ToDo: cty has already been instantiated? *)
        Rtype.instantiate_val ~print:Debug.print ~config Map.Poly.empty cty @@
        LogicOld.Sort.mk_fun @@ List.map ~f:Pattern.sort_of pats @ [Rtype.sort_of_val rty]  
      in
      let args, ret =
        let args, ret = Rtype.args_ret_of_val_type @@ Rtype.aconv_val_type Map.Poly.empty cty in
        let sub =
          Map.Poly.of_alist_exn @@
          List.mapi args ~f:(fun i (x, _) -> x, T_dt.mk_sel_by_cons dt cons_name i term)
        in
        List.map args ~f:(fun (_, t) -> Rtype.subst_val_type sub t), Rtype.subst_val_type sub ret
      in
      let constrs', phi_ret =
        let params_ret, _, (v_ret, phi_ret) = Rtype.let_rgeneral ret in
        (* assume type parameters are all invariant *)
        Set.Poly.union_list @@
        (List.map2_exn params params_ret ~f:(cgen_subtype_val ~config renv) @
         List.map2_exn params_ret params ~f:(cgen_subtype_val ~config renv)),
        Formula.subst (Map.Poly.singleton v_ret term) phi_ret
      in
      let renvs, constrss, not_matched =
        List.unzip3 @@ List.map2i (fun i pi ti ->
            pattern_match_with ~config pi (renv, T_dt.mk_sel_by_cons dt cons_name i term, ti))
          pats args
      in
      Rtype.Env.add_phi (Rtype.Env.disj_union_list (* assume distinct *)renvs) @@
      Formula.mk_and phi_ret (Formula.mk_atom @@ T_dt.mk_is_cons dt cons_name term),
      Set.Poly.union_list @@ constrs :: constrs' :: constrss,
      Formula.or_of @@ (Formula.mk_atom @@ T_dt.mk_is_not_cons dt cons_name term) :: not_matched
    | _ -> failwith "[rcaml:pattern_match_with] unsupported pattern"
  let cgen_pattern_match ~config (x, c_matched, is_bound) pats (nexts, conts) =
    let open Rtype in
    fun maps renv_matched c ->
      let ropsig = opsig_of c in
      match pats, nexts, conts with
      | [Pattern.PVar (x', sort)], [next], [cont] ->
        let renv_branch, c_matched, sort_matched, c =
          let sort_matched = sort_of_comp c_matched in
          if true(*ToDo*) || Stdlib.(sort = sort_matched) then
            let renv_branch, map =
              Env.update_with renv_matched (Env.singleton_ty x' @@ val_type_of c_matched)
            in
            renv_branch, rename_comp_type map c_matched, sort_matched,
            rename_comp_type (Map.Poly.singleton x x') @@ rename_comp_type map c
          else
            failwith @@ sprintf "[cgen_pattern_match] %s and %s"
              (Term.str_of_sort sort) (Term.str_of_sort sort_matched)
        in
        let is_impure_pure =
          Fn.non Sort.is_pure @@ cont_of_cont_eff @@ cont_eff_of c_matched && Sort.is_pure cont
        in
        let c_branch =
          let dom = Env.dep_args_of renv_branch in
          comp_type_of ~config ~temp:true ~opsig:(`Refined ropsig) ~cont dom @@
          if is_impure_pure then val_type_of_sort ~config dom @@ sort_of_comp c
          else val_type_of c
        in
        let rev_comp_effs =
          [(Pattern.PAny (sort_of_comp c_branch), renv_branch, c_branch);
           (Pattern.PVar (x', sort_matched), renv_matched, c_matched)]
        in
        Set.Poly.union_list @@
        [if is_impure_pure then
           cgen_subtype_val ~config renv_branch (val_type_of c_branch) (val_type_of c)
         else Set.Poly.empty;
         cgen_subeff ~config renv_matched rev_comp_effs (val_type_of c_branch) c;
         next maps renv_branch c_branch]
      | _ ->
        let renv =
          if is_bound then (*x is bound in renv_matched*) renv_matched
          else (*x is not bound in renv_matched*)
            Env.disj_union renv_matched @@ Env.singleton_ty x @@ val_type_of c_matched
        in
        let sort_matched = sort_of_comp c_matched in
        let renv_not_matched, constrs =
          List.fold ~init:(renv, Set.Poly.empty) (List.zip3_exn pats nexts conts)
            ~f:(fun (renv, constrs) (pat, next, cont) ->
                let is_impure_pure =
                  Fn.non Sort.is_pure @@ cont_of_cont_eff @@ cont_eff_of c_matched &&
                  Sort.is_pure cont
                in
                let pat_renv, constrs_params, not_matched =
                  pattern_match_with ~config pat
                    (renv, Term.mk_var x sort_matched, val_type_of c_matched)
                in
                Debug.print @@ lazy
                  (sprintf "[rcaml:cgen_pattern_match] pattern: %s\nrenv:\n%s\nconstraints: %s"
                     (Pattern.str_of pat)
                     (Env.str_of ~config pat_renv)
                     (String.concat_set ~sep:"\n" @@
                      Set.Poly.map ~f:Formula.str_of constrs_params));

                Env.add_phi renv not_matched,

                let renv_branch, c_matched, c =
                  let renv_branch, map = Env.update_with renv pat_renv in
                  renv_branch, rename_comp_type map c_matched, rename_comp_type map c
                in
                let c_branch =
                  let dom = Env.dep_args_of renv_branch in
                  comp_type_of ~config ~temp:true ~opsig:(`Refined ropsig) ~cont dom @@
                  if is_impure_pure then val_type_of_sort ~config dom @@ sort_of_comp c
                  else val_type_of c
                in
                let rev_comp_effs =
                  [(Pattern.PAny (sort_of_comp c_branch), renv_branch, c_branch);
                   (Pattern.PVar (x, sort_matched), renv_matched, c_matched)]
                in
                Set.Poly.union_list
                  [if is_impure_pure then
                     cgen_subtype_val ~config renv_branch (val_type_of c_branch) (val_type_of c)
                   else Set.Poly.empty;
                   cgen_subeff ~config renv_matched rev_comp_effs (val_type_of c_branch) c;
                   next maps renv_branch c_branch;
                   constrs_params; constrs])
        in
        Set.Poly.union_list
          [constrs;
           Set.Poly.singleton @@ Formula.mk_imply
             (Evaluator.simplify @@ constr_of ~print:Debug.print ~config renv_not_matched)
             (Formula.mk_false ())]

  let rec env_and_rty_of_pat ~config ?(is_top_level=false) dep_args = function
    | Pattern.PAny _, sort ->
      Rtype.Env.mk_empty (), Rtype.val_type_of_sort ~config dep_args sort
    | Pattern.PVar (x, _sort), sort ->
      let rty =
        Rtype.val_type_of_sort ~config
          ~name:(if is_top_level then Some (name_of_tvar x) else None)
          dep_args sort
      in
      Rtype.Env.singleton_ty x rty, rty
    | Pattern.PTuple pats as pat, (T_tuple.STuple sorts as sort) ->
      let renvs, rtys =
        List.unzip @@ List.map (List.zip_exn pats sorts) ~f:(env_and_rty_of_pat ~config dep_args)
      in
      let tup_ty, phi =
        let v = Rtype.mk_fresh_tvar_with "v" in
        let terms, sorts = List.unzip dep_args in
        let pvar = mk_fresh_pvar () in
        Rtype.mk_rtuple v rtys @@ Formula.mk_atom @@
        Atom.mk_pvar_app pvar (sorts @ [sort]) (terms @ [Term.mk_var v sort]),
        Formula.mk_atom @@ Atom.mk_pvar_app pvar (sorts @ [sort]) (terms @ [Pattern.term_of pat])
      in
      Rtype.Env.add_phi (Rtype.Env.disj_union_list renvs (* assume renvs are distinct *)) phi,
      tup_ty
    | Pattern.PCons _, _ ->
      failwith "[env_and_rty_of_pat] not reachable here because [let T x = ... in ...] is parsed as [match ... with T x -> ...]"
    | _ -> failwith "[env_and_rty_of_pat] unsupported pattern"
  let pvar_eliminator =
    PCSat.PvarEliminator.make
      (PCSat.PvarEliminator.Config.make
         false(*config.verbose*)
         Int.max_value(* [fixpoint] assumes that any intermediate predicate variables are eliminated for GFP predicate generation*)
         4 false)
  let pcsp_of ?(skolem_pred=false) ?(sol_space=Map.Poly.empty)
      (phis, pvs, fnpvs, wfpvs) fenv dtenv constrs =
    (*Debug.print @@ lazy (sprintf "\n*** original:" );
      Debug.print @@ lazy (String.concat_map_list ~sep:"\n" constrs ~f:Formula.str_of);*)
    let phis =
      List.map (Set.Poly.to_list phis @ constrs) ~f:(fun phi ->
          let phi = Evaluator.simplify phi in
          let tvs = Formula.term_sort_env_of(*ToDo: use sort_env_of instead?*) phi in
          Formula.mk_forall_if_bounded (Set.Poly.to_list tvs) phi)
    in
    (*Debug.print @@ lazy (sprintf "\n*** simplified:" );
      Debug.print @@ lazy (String.concat_map_list ~sep:"\n" phis ~f:Formula.str_of);*)
    let phis = Typeinf.typeinf ~to_sus:true phis in
    (*Debug.print @@ lazy (sprintf "\n*** type inferred:" );
      Debug.print @@ lazy (String.concat_map_list ~sep:"\n" phis ~f:Formula.str_of);*)
    let pcsp =
      (*print_endline @@ "before:" ^ String.concat_set ~sep:"," @@ Set.Poly.map ~f:Ident.name_of_pvar @@ Set.Poly.map pvs ~f:fst;*)
      let pvs = Set.Poly.union_list @@ pvs :: List.map phis ~f:Formula.pred_sort_env_of in
      (*print_endline @@ "after:" ^ String.concat_set ~sep:"," @@ Set.Poly.map ~f:Ident.name_of_pvar @@ Set.Poly.map pvs ~f:fst;*)
      let fenv = Map.Poly.filter fenv ~f:(fun (_, _, _, is_rec, _) -> is_rec) in
      PCSP.Problem.make ~skolem_pred (phis, Set.Poly.empty, pvs, fnpvs, wfpvs, fenv, dtenv)
    in
    PCSP.Problem.update_params_sol_space pcsp sol_space
  let mu_preds = ref Map.Poly.empty (*ToDo*)
  let nu_preds = ref Map.Poly.empty (*ToDo*)
  let fixpoint fenv dtenv bpvs pvmap constrs =
    Debug.print @@ lazy (sprintf "\n*** %d constraints generated:" @@ Set.Poly.length constrs);
    Debug.print @@ lazy
      (String.concat_map_set ~sep:"\n" constrs ~f:Formula.str_of);
    pvar_eliminator |> fun (module PvarEliminator : PCSat.PvarEliminator.PvarEliminatorType) ->
    let pcsp0 =
      pcsp_of (*ToDo*)(Set.Poly.empty, Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
        fenv dtenv @@ Set.Poly.to_list constrs
    in
    let mu_pvmap = Map.Poly.filter_map pvmap ~f:(function `LFP pv -> Some pv | _ -> None) in
    let nu_pvmap = Map.Poly.filter_map pvmap ~f:(function `GFP pv -> Some pv | _ -> None) in
    let mu_pvs_dummy = Set.Poly.of_list @@ Map.Poly.data mu_pvmap in
    let nu_pvs_dummy = Set.Poly.of_list @@ Map.Poly.data nu_pvmap in
    let pvs_dummy = Set.Poly.union_list [mu_pvs_dummy; nu_pvs_dummy] in
    let _, pcsp =
      let bpvs = Set.Poly.map ~f:Ident.pvar_to_tvar @@ Set.Poly.union_list [bpvs; pvs_dummy] in
      PvarEliminator.preprocess pcsp0 ~bpvs
    in
    let clauses1, clauses2 =
      Set.Poly.partition_tf (PCSP.Problem.clauses_of pcsp) ~f:(fun c ->
          Set.Poly.is_empty @@ Set.Poly.inter pvs_dummy @@
          Set.Poly.map ~f:Ident.tvar_to_pvar @@ Clause.pvs_of c)
    in
    Debug.print @@ lazy "";
    let theta_mu =
      (*if Fn.non Map.Poly.is_empty mu_pvmap then*)
      Debug.print @@ lazy "*** inductive predicates extracted:";
      Debug.print @@ lazy "";
      Map.Poly.mapi mu_pvmap ~f:(fun ~key:pvar' ~data:pvar ->
          let env, t =
            ClauseSet.pred_of_pos (PCSP.Problem.senv_of pcsp0) clauses2 @@
            Ident.pvar_to_tvar pvar in
          let phi =
            Logic.ExtTerm.to_old_formula (PCSP.Problem.senv_of pcsp)
              (Map.Poly.of_alist_exn env) t []
          in
          assert (Set.Poly.is_empty @@ Set.Poly.inter (Formula.pvs_of phi) pvs_dummy);
          let env = Logic.to_old_sort_env_list Logic.ExtTerm.to_old_sort env in
          Debug.print @@ lazy
            (Printf.sprintf "%s(%s) =mu\n  %s\n"
               (Ident.name_of_pvar pvar')
               (LogicOld.str_of_sort_env_list LogicOld.Term.str_of_sort env)
               (LogicOld.Formula.str_of phi));
          env, phi)
    in
    mu_preds := Map.force_merge !mu_preds theta_mu;
    let theta_nu =
      (*if Fn.non Map.Poly.is_empty mu_pvmap then*)
      Debug.print @@ lazy "*** coinductive predicates extracted:";
      Debug.print @@ lazy "";
      Map.Poly.mapi nu_pvmap ~f:(fun ~key:pvar' ~data:pvar ->
          let env, t =
            ClauseSet.pred_of_pos (PCSP.Problem.senv_of pcsp0) clauses2 @@
            Ident.pvar_to_tvar pvar
          in
          let phi =
            Logic.ExtTerm.to_old_formula (PCSP.Problem.senv_of pcsp)
              (Map.Poly.of_alist_exn env) t []
          in
          assert (Set.Poly.is_empty @@ Set.Poly.inter (Formula.pvs_of phi) pvs_dummy);
          let env = Logic.to_old_sort_env_list Logic.ExtTerm.to_old_sort env in
          Debug.print @@ lazy
            (Printf.sprintf "%s(%s) =nu\n  %s\n"
               (Ident.name_of_pvar pvar')
               (LogicOld.str_of_sort_env_list LogicOld.Term.str_of_sort env)
               (LogicOld.Formula.str_of phi));
          env, phi)
    in
    nu_preds := Map.force_merge !nu_preds theta_nu;
    let constrs =
      Set.Poly.map clauses1 ~f:(fun c ->
          let uni_senv, t = Clause.sort_env_of c, Clause.to_formula c in
          Logic.ExtTerm.to_old_formula (PCSP.Problem.senv_of pcsp) uni_senv t [])
    in
    Debug.print @@ lazy "*** predicate constraints extracted:";
    Debug.print @@ lazy "";
    Debug.print @@ lazy (String.concat_map_set ~sep:"\n" constrs ~f:Formula.str_of);
    Debug.print @@ lazy "";
    constrs
  let generalize ~config renv pat_renv constrs =
    (*ToDo: note that nu_preds and mu_preds can be type-polymorphic as well!*)
    let pvs_preds = Set.Poly.of_list @@ (Map.Poly.keys !mu_preds @ Map.Poly.keys !nu_preds) in
    let penv_renv = Rtype.Env.pred_sort_env_of ~bpvs:pvs_preds renv in
    let penv_dtrenv =
      Set.Poly.map ~f:fst @@ Set.Poly.union_list @@
      List.map ~f:(Rtype.pred_sort_env_of_val ~bpvs:pvs_preds) @@ Map.Poly.data !Rtype.dtrenv
    in
    let penv_constrs = Set.concat_map ~f:(Formula.pred_sort_env_of ~bpvs:pvs_preds) constrs in
    Map.Poly.map pat_renv ~f:(fun t ->
        let penv =
          let penv_val =
            let pvs_constrs = Set.Poly.map ~f:fst penv_constrs in
            Rtype.pred_sort_env_of_val ~bpvs:pvs_preds t
            (*ToDo*)|> Set.Poly.filter ~f:(fun (pvar, _) -> not (Set.Poly.mem pvs_constrs pvar))
          in
          let penv_set =
            Set.Poly.filter (Set.Poly.union penv_val penv_constrs) ~f:(fun (pvar, _) ->
                not (Map.Poly.mem penv_renv pvar) && not (Set.Poly.mem penv_dtrenv pvar))
          in
          try Map.of_set_exn penv_set
          with _ ->
            failwith @@ sprintf "duplicate: %s" @@
            LogicOld.str_of_pred_sort_env_set Term.str_of_sort penv_set
        in
        let svs =
          Set.Poly.diff (Term.svs_of_sort @@ Rtype.sort_of_val t) (Rtype.Env.svs_of renv)
        in
        Rtype.mk_type_poly ~config svs @@ Rtype.comp_type_of ~config [] @@
        Rtype.mk_pred_poly ~config penv constrs @@ Rtype.comp_type_of ~config [] t)
  let cgen_let ~config ~is_top_level ?ropsig fenv dtenv is_rec
      pats (pures, next1s, opsig1s, sort1s, cont1s) maps renv = let open Rtype in
    let pat_renvs, cs =
      List.unzip @@ List.map2_exn pats (List.zip4_exn pures opsig1s sort1s cont1s)
        ~f:(fun pat (pure, opsig, sort, cont) ->
            let dom = Env.dep_args_of renv in
            let temp = if pure then (assert (Sort.is_pure cont); false) else true in
            let pat_renv, t = env_and_rty_of_pat ~config ~is_top_level dom (pat, sort) in
            let opsig =
              match ropsig with
              | Some ropsig -> `Refined ropsig
              | None -> `Sort opsig
            in
            pat_renv, comp_type_of ~config ~temp ~opsig ~cont dom(*ToDo*) t)
    in
    let renv_bound, constrss =
      let renv_bound, map =
        if is_rec then Env.update_with renv @@ Env.disj_union_list (* assume distinct *)pat_renvs
        else renv, Map.Poly.empty
      in
      let cs', pvmap =
        let cs', pvmapss =
          List.unzip @@ List.map cs ~f:(fun (o, t, e, s) ->
              let t', pvmap = fresh_eff_pvars_val ~print:Debug.print t in
              rename_comp_type map (o, t', e, s), pvmap)
        in
        cs', Map.force_merge_list pvmapss
      in
      let pvs_preds = Set.Poly.of_list @@ Map.Poly.keys !mu_preds @ Map.Poly.keys !nu_preds in
      let pvs_renv =
        Set.Poly.of_list @@ Map.Poly.keys @@ Env.pred_sort_env_of(*ToDo*) ~bpvs:pvs_preds renv
      in
      let cs_pvs =
        Set.Poly.union_list @@ List.map cs ~f:(fun c ->
            Set.Poly.map ~f:fst @@ pred_sort_env_of_comp(*ToDo*) ~bpvs:pvs_preds c)
      in
      renv_bound,
      List.map3_exn pats next1s (List.zip_exn cs' cs) ~f:(fun pat next (c', c) ->
          (*if is_top_level then*)
          Debug.print @@ lazy
            (sprintf ">>>>>>>>> predicate constraint generation for %s with\n  %s\n"
               (Pattern.str_of pat) (Rtype.str_of_comp ~config c'));
          let constrs = next maps renv_bound c' in
          let pren =
            let penv_constrs =
              Set.concat_map constrs ~f:(Formula.pred_sort_env_of ~bpvs:pvs_preds)
            in
            let pvs_dtrenv =
              Set.Poly.map ~f:fst @@ Set.Poly.union_list @@
              List.map ~f:(Rtype.pred_sort_env_of_val ~bpvs:pvs_preds) @@
              Map.Poly.data !Rtype.dtrenv
            in
            Map.of_set_exn @@
            Set.Poly.filter_map penv_constrs ~f:(fun (Ident.Pvar name, sorts) ->
                if Set.Poly.mem pvs_dtrenv (Ident.Pvar name) then
                  let name_inst =
                    name ^ "[" ^
                    (String.concat_map_list ~sep:"," sorts ~f:Term.str_of_sort) ^ "]"
                  in
                  Some ((name, sorts), Ident.Pvar name_inst)
                else None)
          in
          let constrs = Set.Poly.map constrs ~f:(Formula.rename_sorted_pvars pren) in
          let constrs =
            let bpvs =
              Set.Poly.union_list
                [pvs_preds; pvs_renv; Set.Poly.of_list @@ Map.Poly.data pren;
                 if is_rec then cs_pvs
                 else Set.Poly.map ~f:fst @@ pred_sort_env_of_comp(*ToDo*) ~bpvs:pvs_preds c]
            in
            fixpoint fenv dtenv bpvs pvmap constrs
          in
          (*if is_top_level then*)
          Debug.print @@ lazy "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n";
          constrs)
    in
    let generalizable =
      List.for_all pures ~f:Fn.id &&
      List.for_all pats ~f:(fun pat -> Sort.is_arrow @@ Pattern.sort_of pat)
    in
    let renv_body, map =
      Env.update_with renv @@
      Env.disj_union_list(* assume the following are distinct *) @@
      if is_rec then
        let constrs = Set.Poly.union_list constrss in
        if generalizable then
          List.map pat_renvs ~f:(fun (pat_renv, phis(* must be empty *)) ->
              generalize ~config renv pat_renv constrs, phis)
        else pat_renvs
      else
        List.map2_exn pat_renvs constrss
          ~f:(fun (pat_renv, phis(* must be empty *)) constrs ->
              (if generalizable then generalize ~config renv pat_renv constrs else pat_renv),
              phis)
    in
    List.map cs ~f:(rename_comp_type map), renv_bound,
    (if generalizable then Set.Poly.empty else Set.Poly.union_list constrss), renv_body, map
  let subst_all_either maps = function
    | First (pure, next, sort, cont) ->
      First (pure, next, Term.subst_sort maps sort, Term.subst_cont maps cont)
    | Second (x, sort) ->
      Second (x, Term.subst_sort maps sort)
  let subst_all_opt maps = function
    | Some (next, cont) ->
      Some (next, Term.subst_cont maps cont)
    | None -> None
  let cgen_either ~config ~ropsig renv maps = let open Rtype in
    function
    | First (pure, next, sort, cont) ->
      let x = mk_fresh_tvar_with "dummy_" in
      let c =
        let dom = Env.dep_args_of renv in
        let temp = if pure then (assert (Sort.is_pure cont); false) else true in
        comp_type_of ~config ~temp ~opsig:(`Refined ropsig) ~cont dom @@
        val_type_of_sort ~config dom sort
      in
      (x, c, false), next maps renv c
    | Second (x, sort) ->
      let c, constrs =
        match Env.look_up renv x with
        | Some xty ->
          let xty, constrs =
            instantiate_val ~print:Debug.print ~config Map.Poly.empty xty sort
          in
          comp_type_of ~config [] @@
          val_rtype_of_term ~config (Term.mk_var x sort) xty,
          constrs
        | None -> failwith @@
          (sprintf "[rcaml:cgen_either] unbound variable: %s : %s\nrenv = %s"
             (name_of_tvar x) (Term.str_of_sort sort) (Env.str_of ~config renv))
      in
      (x, c, true), constrs
  let cgen_expr ~config fenv dtenv senv (expr:expression) = let open Rtype in
    MBcgen.fold_expr dtenv senv expr ~f:(object
      method f_annot (attrs, next) = fun maps renv ty ->
        let c =
          let c_annot_rty_opt =
            MBcgen.find_comp_attrs ~config ~renv ~dtenv ~attr_name:"annot_rty" attrs in
          let c_annot_opt =
            MBcgen.find_comp_attrs ~config ~renv ~dtenv ~attr_name:"annot" attrs in
          match c_annot_rty_opt, c_annot_opt with
          | Some c, _ | None, Some c -> c
          | None, None -> assert false
        in
        Debug.print @@ lazy
          (sprintf "[rcaml:annot] %s <: %s\n" (str_of_comp ~config c) (str_of_comp ~config ty));
        Set.Poly.union_list
          [cgen_subtype_comp ~config renv c ty;
           next maps renv c]
      method f_var (x, sort) = fun maps renv ty ->
        let sort = Term.subst_sort maps sort in
        (**)
        (*print_endline @@ Ident.name_of_tvar x ^ ": " ^ Term.str_of_sort sort;*)
        let xty, constrs =
          match Env.look_up renv x with
          | Some xty ->
            let xty, constrs =
              instantiate_val ~print:Debug.print ~config Map.Poly.empty xty sort
            in
            val_rtype_of_term ~config (Term.mk_var x sort) xty, constrs
          | None ->
            failwith @@ sprintf "[rcaml:var] unbound variable: %s : %s\nrenv = %s"
              (name_of_tvar x) (str_of_comp ~config ty) (Env.str_of ~config renv)
        in
        Debug.print @@ lazy
          (sprintf "[rcaml:var] %s : %s <: %s\n"
             (name_of_tvar x) (str_of_val ~config xty) (str_of_comp ~config ty));
        Set.Poly.union_list
          [constrs;
           cgen_subtype_comp ~config renv (comp_type_of ~config [] xty) ty]
      method f_const term = fun maps renv ty ->
        let term = Term.subst_all maps term in
        (**)
        let cty, constrs =
          let cty = of_term ~print:Debug.print ~config term in
          instantiate_val ~print:Debug.print ~config Map.Poly.empty cty @@ sort_of_comp ty
        in
        Debug.print @@ lazy
          (sprintf "[rcaml:const] %s : %s <: %s\n"
             (Term.str_of term) (str_of_val ~config cty) (str_of_comp ~config ty));
        Set.Poly.union_list
          [constrs;
           cgen_subtype_comp ~config renv (comp_type_of ~config [] cty) ty]
      method f_construct dt cons_name nexts_either = fun maps renv ty ->
        let dt = Datatype.subst maps dt in
        let nexts_either = List.map nexts_either ~f:(subst_all_either maps) in
        (**)
        let cty, constrs =
          let sorts = List.map nexts_either ~f:(function First (_, _, sort, _) | Second (_, sort) -> sort) in
          let cty = of_constructor ~print:Debug.print ~config cons_name dt in
          Debug.print @@ lazy
            (sprintf "[rcaml:constructor] (%s : %s) (...) <: %s\n"
               cons_name (str_of_val ~config cty) (str_of_comp ~config ty));
          (* ToDo: cty has already been instantiated?*)
          instantiate_val ~print:Debug.print ~config Map.Poly.empty cty @@
          LogicOld.Sort.mk_fun @@ sorts @ [sort_of_comp ty]
        in
        let ropsig = opsig_of ty in
        let res, constrss =
          List.unzip @@ List.map nexts_either ~f:(cgen_either ~config ~ropsig renv maps)
        in
        let cs = List.map res ~f:snd3 in
        let cs', fun_ty =
          let ts = List.map cs ~f:val_type_of in
          let xs = List.map cs ~f:(fun _ -> mk_fresh_tvar_with "x"(* dummy *)) in
          (*cause no temporal effect*)of_args_ret ~config [] xs ts @@ val_type_of ty
        in
        let rev_comp_effs =
          List.map ~f:(fun c -> Pattern.PAny (sort_of_comp c), renv, c) @@
          (List.rev cs') @ comp_type_of ~config [] fun_ty :: cs
        in
        Set.Poly.union_list @@
        [constrs;
         cgen_subeff ~config renv rev_comp_effs (val_type_of ty) ty;
         cgen_subtype_val renv ~config cty fun_ty] @
        constrss
      method f_apply (next1, cont1s, cont1) next2s_either  = fun maps renv ty ->
        let cont1s = List.map cont1s ~f:(Term.subst_cont maps) in
        let cont1 = Term.subst_cont maps cont1 in
        let next2s_either = List.map next2s_either ~f:(subst_all_either maps) in
        (**)
        Debug.print @@ lazy (sprintf "[rcaml:apply] %s\n" @@ str_of_comp ~config ty);
        let ropsig = opsig_of ty in
        let res, constrss =
          List.unzip @@ List.map next2s_either ~f:(cgen_either ~config ~ropsig renv maps)
        in
        let cs = List.map res ~f:snd3 in
        let cs', fun_ty =
          let ts = List.map cs ~f:val_type_of in
          let xs = List.map cs ~f:(fun _ -> mk_fresh_tvar_with "x"(* dummy *)) in
          let dom = Env.dep_args_of renv in
          of_args_ret ~config
            ~temp:true ~ropsig ~cont:(Some cont1s) dom xs ts @@ val_type_of ty
        in
        let fun_ty =
          let dom = Env.dep_args_of renv in
          comp_type_of ~config ~temp:true ~opsig:(`Refined ropsig) ~cont:cont1 dom fun_ty
        in
        (*assert Stdlib.(sort1 = sort_of_val fun_ty);*)
        let rev_comp_effs =
          List.map ~f:(fun c -> Pattern.PAny (sort_of_comp c), renv, c) @@
          (List.rev cs') @ fun_ty :: cs
        in
        Set.Poly.union_list @@
        [cgen_subeff ~config renv rev_comp_effs (val_type_of ty) ty;
         next1 maps renv fun_ty] @
        constrss
      method f_tuple nexts_either = fun maps renv ty ->
        let nexts_either = List.map nexts_either ~f:(subst_all_either maps) in
        (**)
        Debug.print @@ lazy (sprintf "[rcaml:tuple] %s\n" @@ str_of_comp ~config ty);
        let ropsig = opsig_of ty in
        let res, constrss =
          List.unzip @@ List.map nexts_either ~f:(cgen_either ~config ~ropsig renv maps)
        in
        let cs = List.map res ~f:snd3 in
        let renv', tup_ty =
          let sorts = List.map nexts_either ~f:(function First (_, _, sort, _) | Second (_, sort) -> sort) in
          let ts = List.map cs ~f:val_type_of in
          let xs = List.map cs ~f:(fun _ -> mk_fresh_tvar_with "x"(* dummy *)) in
          let v = mk_fresh_tvar_with "v" in
          Env.disj_union renv @@ Env.of_list @@ List.zip_exn xs ts,
          mk_rtuple v ts @@ Formula.eq (Term.mk_var v @@ T_tuple.STuple sorts) @@
          T_tuple.mk_tuple_cons sorts @@ List.map2_exn xs sorts ~f:Term.mk_var
        in
        let rev_comp_effs = List.map ~f:(fun c -> Pattern.PAny (sort_of_comp c), renv, c) cs in
        Set.Poly.union_list @@
        [cgen_subeff ~config renv rev_comp_effs tup_ty ty;
         cgen_subtype_val ~config renv' tup_ty (val_type_of ty)] @
        constrss
      method f_function pats (nexts, conts) = fun maps renv ty ->
        let conts = List.map conts ~f:(Term.subst_cont maps) in
        (**)
        Debug.print @@ lazy (sprintf "[rcaml:function] %s\n" @@ str_of_comp ~config ty);
        Set.Poly.union (cgen_check_pure ~config renv ty) @@
        match val_type_of ty with
        | RArrow (x, t, c, pred) ->
          let x' = mk_fresh_tvar_with "matched_" in
          let t' = rename_val_type (Map.Poly.singleton x x') t in
          let c' = rename_comp_type (Map.Poly.singleton x x') c in
          Set.Poly.union_list
            [if config.gen_ref_pred_for_fun_types then
               Set.Poly.singleton @@ Formula.mk_imply
                 (Evaluator.simplify @@ constr_of ~print:Debug.print ~config renv)
                 (snd pred(*ToDo: the first element is ignored*))
             else (assert (is_trivial pred); Set.Poly.empty);
             cgen_pattern_match ~config (x', comp_type_of ~config [] t', false)
               pats (nexts, conts) maps renv c']
        | _ -> failwith "f_function"
      method f_ite (next1, cont1) (next2, cont2) next3_opt = fun maps renv ty ->
        let cont1 = Term.subst_cont maps cont1 in
        let cont2 = Term.subst_cont maps cont2 in
        let next3_opt = subst_all_opt maps next3_opt in
        (**)
        Debug.print @@ lazy (sprintf "[rcaml:ite] %s\n" @@ str_of_comp ~config ty);
        let ropsig = opsig_of ty in
        let c_cond =
          let dom = Env.dep_args_of renv in
          comp_type_of ~config ~temp:true ~opsig:(`Refined ropsig) ~cont:cont1 dom @@
          val_type_of_sort ~config ~name:(Some (name_of_tvar @@ mk_fresh_tvar_with "cond"))
            dom T_bool.SBool
        in
        let x_cond = Ident.mk_fresh_tvar () in
        let renv_then, renv_else =
          let renv = Env.set_ty renv x_cond @@ val_type_of c_cond in
          Env.add_phi renv @@ Formula.eq (Term.mk_var x_cond T_bool.SBool) (T_bool.mk_true ()),
          Env.add_phi renv @@ Formula.eq (Term.mk_var x_cond T_bool.SBool) (T_bool.mk_false ())
        in
        let is_impure_pure_then = Fn.non Sort.is_pure cont1 && Sort.is_pure cont2 in
        let c_then =
          let dom_then = Env.dep_args_of renv_then in
          comp_type_of ~config ~temp:true ~opsig:(`Refined ropsig) ~cont:cont2 dom_then @@
          if is_impure_pure_then then val_type_of_sort ~config dom_then @@ sort_of_comp ty
          else val_type_of ty
        in
        let rev_comp_effs_then =
          [(Pattern.PAny (sort_of_comp c_then), renv_then, c_then);
           (Pattern.PVar (x_cond, sort_of_comp c_cond), renv, c_cond)]
        in
        Set.Poly.union_list @@
        [next1 maps renv c_cond;
         if is_impure_pure_then then
           cgen_subtype_val ~config renv_then (val_type_of c_then) (val_type_of ty)
         else Set.Poly.empty;
         cgen_subeff ~config renv rev_comp_effs_then (val_type_of ty) ty;
         next2 maps renv_then c_then] @
        match next3_opt with
        | Some (next3, cont3) ->
          let is_impure_pure_else = Fn.non Sort.is_pure cont1 && Sort.is_pure cont3 in
          let c_else =
            let dom_else = Env.dep_args_of renv_else in
            comp_type_of ~config ~temp:true ~opsig:(`Refined ropsig) ~cont:cont3 dom_else @@
            if is_impure_pure_else then val_type_of_sort ~config dom_else @@ sort_of_comp ty
            else val_type_of ty
          in
          let rev_comp_effs_else =
            [(Pattern.PAny (sort_of_comp c_else), renv_else, c_else);
             (Pattern.PVar (x_cond, sort_of_comp c_cond), renv, c_cond)]
          in
          [if is_impure_pure_else then
             cgen_subtype_val ~config renv_else (val_type_of c_else) (val_type_of ty)
           else Set.Poly.empty;
           cgen_subeff ~config renv rev_comp_effs_else (val_type_of ty) ty;
           next3 maps renv_else c_else]
        | None -> []
      method f_match next1_either pats (nexts, effs) = fun maps renv ty ->
        let effs = List.map effs ~f:(Term.subst_cont maps) in
        let next1_either = subst_all_either maps next1_either in
        (**)
        let ropsig = opsig_of ty in
        let matched, constrs1 = cgen_either ~config ~ropsig renv maps next1_either in
        Debug.print @@ lazy
          (sprintf "[rcaml:match] match %s : %s with ... : %s\n"
             (name_of_tvar @@ fst3 matched) (str_of_comp ~config @@ snd3 matched)
             (str_of_comp ~config ty));
        Set.Poly.union_list
          [constrs1;
           cgen_pattern_match ~config matched pats (nexts, effs) maps renv ty]
      method f_assert (next_opt, cont) = fun maps renv ty ->
        let cont = Term.subst_cont maps cont in
        (**)
        Debug.print @@ lazy (sprintf "[rcaml:assert] %s\n" @@ str_of_comp ~config ty);
        let ropsig = opsig_of ty in
        match next_opt with
        | None ->
          Set.Poly.singleton @@ Formula.mk_imply
            (Evaluator.simplify @@ constr_of ~print:Debug.print ~config renv)
            (Formula.mk_false ())
        | Some next ->
          let c_cond, renv_then, renv_else =
            let dom = Env.dep_args_of renv in
            let t_cond =
              val_type_of_sort ~config ~name:(Some (name_of_tvar @@ mk_fresh_tvar_with "cond"))
                dom T_bool.SBool
            in
            let params, _, (x, phi) = let_rgeneral t_cond in
            assert (List.is_empty params);
            comp_type_of ~config ~temp:true ~opsig:(`Refined ropsig) ~cont dom t_cond,
            Env.add_phi renv @@ Formula.subst (Map.Poly.singleton x @@ T_bool.mk_true ()) phi,
            Env.add_phi renv @@ Formula.subst (Map.Poly.singleton x @@ T_bool.mk_false ()) phi
          in
          let rev_comp_effs = [Pattern.PAny (sort_of_comp c_cond), renv, c_cond] in
          let ty_then =
            mk_simple_val_rtype ~config @@ Datatype.sort_of @@ ConstDatatype.unit_dt
          in
          Set.Poly.union_list
            [next maps renv c_cond;
             cgen_subeff ~config renv_then rev_comp_effs ty_then ty;
             cgen_subtype_val ~config renv_then ty_then @@ val_type_of ty;
             Set.Poly.singleton @@ Formula.mk_imply
               (Evaluator.simplify @@ constr_of ~print:Debug.print ~config renv_else)
               (Formula.mk_false ())]
      method f_let_and is_rec pats defs (next2, cont2) =
        fun maps renv ty ->
        let defs =
          let pure1s, next1s, sort1s, cont1s = defs in
          let opsig1s = List.map sort1s ~f:(fun _ -> Sort.empty_closed_opsig(*dummy*)) in
          let sort1s = List.map sort1s ~f:(Term.subst_sort maps) in
          let cont1s = List.map cont1s ~f:(Term.subst_cont maps) in
          pure1s, next1s, opsig1s, sort1s, cont1s
        in
        let cont2 = Term.subst_cont maps cont2 in
        (**)
        Debug.print @@ lazy (sprintf "[rcaml:let_and] %s\n" @@ str_of_comp ~config ty);
        let ropsig = opsig_of ty in
        let cs, renv_bound, constrs, renv_body, map =
          cgen_let ~config ~is_top_level:false ~ropsig fenv dtenv is_rec pats defs maps renv
        in
        let ty = rename_comp_type map ty in
        let is_impure_pure =
          let _, _, _, _, cont1s = defs in
          List.exists cont1s ~f:(Fn.non Sort.is_pure) && Sort.is_pure cont2
        in
        let c_body =
          let dom = Env.dep_args_of renv_body in
          comp_type_of ~config ~temp:true ~opsig:(`Refined ropsig) ~cont:cont2 dom @@
          if is_impure_pure then val_type_of_sort ~config dom @@ sort_of_comp ty
          else val_type_of ty
        in
        let rev_comp_effs =
          (Pattern.PAny (sort_of_comp c_body), renv_body, c_body) ::
          (List.rev @@ List.map2_exn pats cs ~f:(fun pat c -> pat, renv_bound, c))
        in
        Set.Poly.union_list
          [if is_impure_pure then
             cgen_subtype_val ~config renv_body (val_type_of c_body) (val_type_of ty)
           else Set.Poly.empty;
           constrs;
           cgen_subeff ~config renv rev_comp_effs (val_type_of ty) ty;
           next2 maps renv_body c_body]
      method f_sequence (next1, sort1, cont1) (next2, cont2) = fun maps renv ty ->
        let sort1 = Term.subst_sort maps sort1 in
        let cont1 = Term.subst_cont maps cont1 in
        let cont2 = Term.subst_cont maps cont2 in
        (**)
        Debug.print @@ lazy (sprintf "[rcaml:sequence] %s\n" @@ str_of_comp ~config ty);
        let ropsig = opsig_of ty in
        let dom = Env.dep_args_of renv in
        let c1 =
          comp_type_of ~config ~temp:true ~opsig:(`Refined ropsig) ~cont:cont1 dom @@
          mk_simple_val_rtype ~config sort1
        in
        let c2 =
          comp_type_of ~config ~temp:true ~opsig:(`Refined ropsig) ~cont:cont2 dom @@
          val_type_of ty
        in
        let rev_comp_effs =
          [(Pattern.PAny (sort_of_comp c2), renv, c2);
           (Pattern.PAny sort1, renv, c1)]
        in
        Set.Poly.union_list
          [cgen_subeff ~config renv rev_comp_effs (val_type_of ty) ty;
           next1 maps renv c1;
           next2 maps renv c2]
      method f_shift0 (x_opt, sort) (next2, opsig2, sort2, cont2) = fun maps renv ty ->
        let sort = Term.subst_sort maps sort in
        let opsig2 = Term.subst_opsig maps opsig2 in
        let sort2 = Term.subst_sort maps sort2 in
        let cont2 = Term.subst_cont maps cont2 in
        (**)
        Debug.print @@ lazy (sprintf "[rcaml:shift0] %s\n" @@ str_of_comp ~config ty);
        match sort with
        | Sort.SArrow (sort_t, (opsig1, sort1, cont1)) -> begin
            let t = val_type_of_sort ~config (Env.dep_args_of renv) sort_t in
            let y = mk_fresh_tvar_with "y" in
            let renv1 = Env.set_ty(*assume y is not bound by renv*) renv y t in
            let c1 =
              let dom = Env.dep_args_of renv1 in
              comp_type_of ~config ~temp:true ~opsig:(`Sort opsig1) ~cont:cont1 dom @@
              val_type_of_sort ~config dom sort1
            in
            let c2 =
              let dom = Env.dep_args_of renv in
              comp_type_of ~config ~temp:true ~opsig:(`Sort opsig2) ~cont:cont2 dom @@
              val_type_of_sort ~config dom sort2
            in
            let rty = empty_opsig, t, mk_temp_eff_val (), Eff (y, c1, c2) in
            let renv2 =
              match x_opt with
              | None -> renv
              | Some x ->
                Env.set_ty(*assume x is not bound by renv*) renv
                  x (mk_rarrow y t c1 @@ mk_fresh_trivial_pred ())
            in
            Set.Poly.union_list
              [cgen_subtype_comp ~config renv rty ty;
               next2 maps renv2 c2]
          end
        | _ -> failwith "f_shift0"
      method f_reset (next1, sort1) = fun maps renv ty ->
        let sort1 = Term.subst_sort maps sort1 in
        (**)
        Debug.print @@ lazy (sprintf "[rcaml:reset] %s\n" @@ str_of_comp ~config ty);
        let c1 = (*ToDo:refactor*)
          let dom = Env.dep_args_of renv in
          let t1 = val_type_of_sort ~config dom sort1 in
          empty_opsig,
          t1,
          (if (*ToDo*)config.Rtype.enable_temp_eff then mk_temp_eff_fresh ~config dom
           else mk_temp_eff_val ()),
          let x = mk_fresh_tvar_with "x" in
          let t1' = val_rtype_of_term ~config (Term.mk_var x @@ sort_of_val t1) t1 in
          Eff (x,
               comp_type_of ~config
                 ~temp:false
                 ~opsig:(`Refined empty_opsig)
                 ~cont:Sort.Pure [] t1',
               ty)
        in
        next1 maps renv c1
      method f_perform attrs name sort_op_applied nexts_either = fun maps renv ty ->
        let sort_op_applied = Term.subst_sort maps sort_op_applied in
        let nexts_either = List.map nexts_either ~f:(subst_all_either maps) in
        (**)
        Debug.print @@ lazy (sprintf "[rcaml:perform] %s\n" @@ str_of_comp ~config ty);
        let ropsig = opsig_of ty in
        let res, constrss =
          List.unzip @@ List.map nexts_either ~f:(cgen_either ~config ~ropsig renv maps)
        in
        let c_args = List.map res ~f:snd3 in
        let t_args = List.map c_args ~f:val_type_of in
        let x_args = List.map c_args ~f:(fun _ -> mk_fresh_tvar_with "x"(* dummy *)) in

        let dom = Env.dep_args_of renv in
        let t_op_applied = val_type_of_sort ~config dom sort_op_applied in
        let _, t_op = of_args_ret ~config ~temp:true dom x_args t_args t_op_applied in
        let c_pfm, t_pfm =
          match t_op_applied with
          | RArrow (_, RArrow (y, t_y, c1, _(*ToDo*)), c2, _(*ToDo*)) ->
            (ropsig, t_y, mk_temp_eff_val (), Eff (y, c1, c2)), t_y
          | _ -> failwith "f_perform"
        in

        let rev_comp_effs =
          List.map ~f:(fun c -> Pattern.PAny (sort_of_comp c), renv, c) @@
          c_pfm :: c_args
        in
        let t_op_o = Common.Util.ALMap.find_exn name @@ ropsig in

        let t_op_annot_opt =
          match List.hd attrs with
          | None -> None
          | Some attr ->
            let content =
              match attr.Parsetree.attr_payload with
              | Parsetree.PStr ps ->
                let ts, _, _, _, _ = Typemod.type_structure (Compmisc.initial_env ()) ps in
                begin match (List.hd_exn @@ List.rev ts.str_items).str_desc with
                  | Tstr_eval (expr, _) ->
                    begin match expr.exp_desc with
                      | Texp_constant (Const_string (str, _, _)) -> str
                      | _ -> failwith "unsupported"
                    end
                  | _ -> failwith "unsupported"
                end
              | _ -> failwith "unsupported"
            in
            match attr.Parsetree.attr_name.txt with
            | "annot" ->
              let renv = RefTypParser.val_ty_env RefTypLexer.token @@ Lexing.from_string content in
              let ty = Env.look_up_exn renv (Tvar "perform") in
              Debug.print @@ lazy (sprintf "[rcaml:perform] annot: %s\n" @@ str_of_val ~config ty);
              Some ty
            | _ -> failwith "unknown attribute"
        in
        let constr_o =
          match t_op_annot_opt with
          | Some t_op_annot ->
            Set.Poly.union_list [ (* ? *)
              cgen_subtype_val ~config renv t_op_o t_op_annot;
              cgen_subtype_val ~config renv t_op_annot t_op;
            ]
          | None -> cgen_subtype_val ~config renv t_op_o t_op
        in

        Set.Poly.union_list @@
        [constr_o;
         cgen_subtype_val ~config renv t_pfm (val_type_of ty);
         cgen_subeff ~config renv rev_comp_effs t_pfm ty] @
        constrss
      method f_handling (next_b, sort_b) (next_r, xr, opsig_r, sort_r, cont_r) op_names nexts clauses = fun maps renv ty ->
        let sort_b = Term.subst_sort maps sort_b in
        let opsig_r = Term.subst_opsig maps opsig_r in
        let sort_r = Term.subst_sort maps sort_r in
        let cont_r = Term.subst_cont maps cont_r in
        let clauses =
          List.map clauses ~f:(fun (x_args_opt, sort_args, k_opt, sort_k, (opsig, sort, cont)) ->
              let sort_args = List.map ~f:(Term.subst_sort maps) sort_args in
              let sort_k = Term.subst_sort maps sort_k in
              let opsig = Term.subst_opsig maps opsig in
              let sort = Term.subst_sort maps sort in
              let cont = Term.subst_cont maps cont in
              (x_args_opt, sort_args, k_opt, sort_k, (opsig, sort, cont)))
        in
        (**)
        Debug.print @@ lazy (sprintf "[rcaml:handling] %s\n" @@ str_of_comp ~config ty);
        let dom = Env.dep_args_of renv in

        let t_b = val_type_of_sort ~config dom sort_b in

        let renv_r = Env.set_ty renv xr t_b in
        let dom_r = Env.dep_args_of renv_r in
        let t_r = val_type_of_sort ~config dom_r sort_r in
        let c_r = comp_type_of ~config ~temp:true ~opsig:(`Sort opsig_r) ~cont:cont_r dom_r t_r in
        let constr_r = next_r maps renv_r c_r in

        let constrs, t_ops =
          List.zip_exn nexts clauses
          |> List.map ~f:(fun (next, (x_args, sort_args, k_opt, sort_k, (opsig, sort, cont))) ->
              let t_args = List.map ~f:(val_type_of_sort ~config dom) sort_args in
              let renv' =
                List.fold2_exn x_args t_args ~init:renv ~f:(fun renv x t -> Env.set_ty renv x t)
              in
              let dom' = Env.dep_args_of renv' in

              let t_k = val_type_of_sort ~config dom' sort_k in
              let renv'', k =
                match k_opt with
                | Some k -> Env.set_ty renv' k t_k, k
                | None -> renv', mk_fresh_tvar ~prefix:(Some "k") () (*dummy*)
              in
              let dom'' = Env.dep_args_of renv'' in

              let t = val_type_of_sort ~config dom'' sort in
              let c = comp_type_of ~config ~temp:true ~opsig:(`Sort opsig) ~cont dom'' t in

              next maps renv'' c,
              let _, rty =
                of_args_ret ~config [] x_args t_args
                  (mk_rarrow k t_k c @@ mk_fresh_trivial_pred ())
              in
              rty)
          |> List.unzip
        in

        let c_b = (
          Common.Util.ALMap.of_alist_exn @@ List.zip_exn op_names t_ops,
          t_b,
          (if config.Rtype.enable_temp_eff then mk_temp_eff_fresh ~config dom
           else mk_temp_eff_val ()),
          Eff (xr, c_r, ty)
        ) in
        let constr_b = next_b maps renv c_b in

        Set.Poly.union_list @@ constr_b :: constr_r :: constrs
    end)

  let solve senv eff_constrs opsig_constrs =
    Debug.print (lazy "==== MB type template:");
    Map.Poly.iteri senv ~f:(fun ~key ~data ->
        Debug.print @@ lazy (Ident.name_of_tvar key ^ ": " ^ Term.str_of_sort data));
    Debug.print (lazy "==== eff constraints:");
    Set.Poly.iter eff_constrs ~f:(fun (effs, eff) ->
        Debug.print @@ lazy
          (sprintf "%s <: %s"
             (String.concat_map_list ~sep:" " effs ~f:Term.str_of_cont)
             (Term.str_of_cont eff)));
    Debug.print (lazy "==== opsig constraints:");
    Set.Poly.iter opsig_constrs ~f:(fun (o1, o2) ->
        Debug.print @@ lazy (Term.str_of_opsig o1 ^ " <: " ^ Term.str_of_opsig o2));
    let sol = MBcsol.solve eff_constrs opsig_constrs in
    let sub = sol.subst_purest in
    let eqc = List.concat_map ~f:(fun (e, es) -> List.map es ~f:(fun e' -> e', e)) @@ Map.Poly.to_alist sol.ev_equiv in
    sub.otheta, sub.stheta,
    Map.Poly.of_alist_exn @@
    List.dedup_and_sort ~compare:Stdlib.compare @@
    List.map (Map.Poly.to_alist sub.etheta) ~f:(fun (e, s) ->
        try List.Assoc.find_exn ~equal:Stdlib.(=) eqc e, s with _ -> assert false)

  (** Constraint Generation *)

  let _ = Compmisc.init_path ()
  let of_struct_item ~config (fenv, dtenv, renv) item =
    let print_load_info str =
      Debug.print @@ lazy (sprintf "==================== processing %s ====================" str)
    in
    match item.str_desc with
    | Tstr_eval (_expr, _) -> failwith "expression not supported"
    | Tstr_value (is_rec, vbs) ->
      let open Rtype in
      let is_rec =
        let defs =
          String.concat_map_list ~sep:" and " vbs ~f:(fun vb -> Pattern.str_of @@ MBcgen.pattern_of dtenv vb.vb_pat)
        in
        match is_rec with
        | Recursive -> print_load_info @@ "let rec " ^ defs; true
        | Nonrecursive -> print_load_info @@ "let " ^ defs; false
      in
      let pures, pats, defs =
        List.unzip3 @@ List.map vbs ~f:(fun vb ->
            let pat = MBcgen.pattern_of dtenv vb.vb_pat in
            let expr = vb.vb_expr in
            let attrs = vb.vb_attributes in
            let t_annot_MB_opt =
              MBcgen.find_val_attrs ~config ~renv ~dtenv ~attr_name:"annot_MB" attrs in
            let t_annot_opt =
              MBcgen.find_val_attrs ~config ~renv ~dtenv ~attr_name:"annot" attrs in
            let rty_annotated =
              List.exists attrs ~f:(fun attr -> Stdlib.(attr.attr_name.txt = "annot_rty"))
              || Option.is_some t_annot_opt
            in
            if rty_annotated then
              failwith "rtype annotations on let-bindings are not supported"; (*todo*)
            let sort =
              match t_annot_MB_opt, t_annot_opt with
              | Some t, _ | None, Some t -> sort_of_val t
              | None, None -> MBcgen.sort_of_expr ~lift:true dtenv expr
            in
            let evar = Sort.mk_fresh_evar () in
            let ovar = Sort.mk_fresh_empty_open_opsig () in
            let pat_senv = Pattern.senv_of pat sort in
            MBcgen.is_pure expr.exp_desc,
            pat,
            (pat_senv, expr, ovar, sort, evar))
      in
      let maps, next1s =
        let senv = Env.to_sort_env renv in
        let senv_bounds =
          if is_rec then
            let pat_senvs =
              List.map defs(* assume distinct *) ~f:(fun (pat_senv, _, _, _, _) -> pat_senv)
            in
            Map.update_with_list(*shadowing*) @@ senv :: pat_senvs
          else senv
        in
        let eff_constrss, opsig_constrss, next1s =
          List.unzip3 @@ List.map defs ~f:(fun (_, expr, ovar, sort, evar) ->
              cgen_expr ~config fenv dtenv senv_bounds expr (ovar, sort, evar))
        in
        let omap, smap, emap =
          solve senv_bounds (Set.Poly.union_list eff_constrss) (Set.Poly.union_list opsig_constrss)
        in
        (*let senv_body =
          let pat_senvs =
            List.map defs(* assume distinct *) ~f:(fun (pat_senv, _, _, _, _) -> pat_senv)
          in
          let generalizable =
            List.for_all pures ~f:Fn.id &&
            List.for_all pats ~f:(fun pat -> Sort.is_arrow @@ Pattern.sort_of pat)
          in
          Map.update_with_list(*shadowing*) @@
          senv ::
          if generalizable then
            List.map pat_senvs ~f:(Map.Poly.map ~f:(Typeinf.generalize senv))
          else pat_senvs
          in*)
        let emap' = Map.Poly.map emap ~f:(Term.subst_sorts_cont smap)(*ToDo*) in
        let omap' =
          Map.Poly.map ~f:(Term.subst_conts_opsig emap') @@
          Map.Poly.map ~f:(Term.subst_sorts_opsig smap) omap
        in
        (omap', smap, emap'), next1s
      in
      let opsig1s, sort1s, cont1s =
        List.unzip3 @@ List.map defs ~f:(fun (_, _, opsig, sort, cont) ->
            Term.subst_opsig maps opsig, Term.subst_sort maps sort, Term.subst_cont maps cont)
      in
      (**)
      Debug.print (lazy "");
      let cs, _renv_bound(*ToDo*), constrs, renv_body, _map(*ToDo*) =
        cgen_let ~config ~is_top_level:true fenv dtenv is_rec
          pats (pures, next1s, opsig1s, sort1s, cont1s) maps renv
      in
      (match List.find cs ~f:(Fn.non @@ Rtype.is_pure_comp ~config) with
       | None ->
         Debug.print @@ lazy (sprintf "updated renv:\n%s" @@ Env.str_of ~config renv_body);
         (fenv, dtenv, renv_body),
         Constraints constrs
       | Some c ->
         failwith @@ "[of_struct_item] impure top-level computation not supported: " ^ Rtype.str_of_comp ~config c)
    | Tstr_primitive vd ->
      let name = vd.val_name.txt in
      print_load_info "external";
      let renv', _ =
        let sort = MBcgen.sort_of_type_expr dtenv vd.val_desc.ctyp_type in
        let sort = Sort.mk_poly (Term.svs_of_sort sort) sort in
        Rtype.Env.update_with renv @@
        Rtype.Env.singleton_ty (Tvar name) @@
        (*Rtype.val_type_of_sort ~config ~name:(Some name)
           (Rtype.Env.dep_args_of @@ Rtype.Env.mk_empty ()) @@*)
        Rtype.mk_simple_val_rtype ~config sort
      in
      Debug.print @@ lazy (sprintf "updated renv:\n%s" @@ Rtype.Env.str_of ~config renv');
      (fenv, dtenv, renv'),
      Skip
    | Tstr_type (_, types) ->
      print_load_info "type";
      let dttypes, ustypes =
        List.partition_tf types ~f:(fun ty ->
            Debug.print @@ lazy
              (sprintf "[of_struct_item] processing a type declaration: %s" ty.typ_name.txt);
            match ty.typ_kind with
            | Ttype_variant _ -> Debug.print @@ lazy ("\t is a variant type"); true
            | Ttype_abstract -> Debug.print @@ lazy ("\t is an abstract type"); false
            | Ttype_open -> failwith "unsupported type_declaration kind: Ttype_open"
            | Ttype_record _ ->
              if Stdlib.(ty.typ_name.txt = "effect_handler" || ty.typ_name.txt = "handler")
              then false
              else failwith "unsupported type_declaration kind: Ttype_record")
      in
      let datatypes' =
        let sel_of datatypes dtenv sel_name (ct:core_type) =
          match ct.ctyp_desc with
          | Ttyp_constr (ret_name, _, args) -> begin
              match
                List.find datatypes ~f:(fun dt ->
                    Stdlib.(Path.name ret_name = Datatype.name_of_dt dt)) with
              | Some dt ->
                Datatype.mk_insel sel_name (Datatype.name_of_dt dt) @@
                List.map args ~f:(MBcgen.sort_of_core_type dtenv)
              | None ->
                Datatype.mk_sel sel_name @@ MBcgen.sort_of_core_type dtenv ct
            end
          | _ -> Datatype.mk_sel sel_name @@ MBcgen.sort_of_core_type dtenv ct
        in
        let sels_of datatypes dtenv cons_name = function
          | Cstr_tuple cts ->
            List.mapi cts ~f:(fun i -> sel_of datatypes dtenv (name_of_sel cons_name i))
          | Cstr_record _ ->
            failwith "[sels_of] Cstr_record is not supported as an argument of a constructor"
        in
        let cons_of datatypes dtenv (cons:Typedtree.constructor_declaration) =
          let cons_name = cons.cd_name.txt in
          let sels = sels_of datatypes dtenv cons_name cons.cd_args in
          let cons' = Datatype.mk_cons cons_name ~sels in
          Debug.print @@ lazy ("[cons_of] " ^ Datatype.str_of_cons cons');
          cons'
        in
        let dtenv =
          List.fold_left ustypes ~init:dtenv ~f:(fun dtenv ty ->
              DTEnv.update_dt dtenv @@
              match ty.typ_manifest with
              | Some core_type ->
                Datatype.mk_alias ty.typ_name.txt @@ MBcgen.sort_of_core_type dtenv core_type
              | None -> Datatype.mk_uninterpreted_datatype ty.typ_name.txt)
        in
        let datatypes =
          List.map dttypes ~f:(fun t ->
              Datatype.mk_dt t.typ_name.txt @@
              List.map t.typ_params ~f:(fun (ct, _) -> MBcgen.sort_of_core_type dtenv ct))
        in
        List.map2_exn datatypes dttypes ~f:(fun dt ty ->
            match ty.typ_kind with
            | Ttype_variant tds -> { dt with conses = List.map tds ~f:(cons_of datatypes dtenv) }
            | Ttype_abstract -> failwith "unsupported type_declaration kind: Ttype_abstract"
            | Ttype_open -> failwith "unsupported type_declaration kind: Ttype_abstract"
            | Ttype_record _ -> failwith "unsupported type_declaration kind: Ttype_record")
      in
      let dtenv' =
        List.fold_left datatypes' ~init:dtenv ~f:(fun dtenv dt ->
            DTEnv.update_dt dtenv @@
            Datatype.create (Datatype.name_of_dt dt) datatypes' Datatype.FDt)
      in
      Debug.print @@ lazy (sprintf "[of_struct_item] dtenv:\n%s" @@ DTEnv.str_of dtenv');
      update_ref_dtenv dtenv';
      (fenv, dtenv', renv),
      Skip
    | Tstr_typext _ -> failwith "type extension not supported"
    | Tstr_exception _ -> failwith "exception not supported"
    | Tstr_module _ -> failwith "module not supported"
    | Tstr_recmodule _ -> failwith "recursive module not supported"
    | Tstr_modtype _ -> failwith "module type not supported"
    | Tstr_open _ -> failwith "open not supported"
    | Tstr_class _ -> failwith "class not supported"
    | Tstr_class_type _ -> failwith "class type not supported"
    | Tstr_include _ -> failwith "include not supported"
    | Tstr_attribute attr ->
      print_load_info "attribute";
      Envs.cgen_config := config; Envs.renv := renv; Envs.denv := dtenv;
      let content =
        match attr.Parsetree.attr_payload with
        | Parsetree.PStr ps ->
          (* Debug.print @@ lazy
             (sprintf "parse structure:\n%s" (str_of_parse_structure ps)); *)
          let ts, _, _, _, _ = Typemod.type_structure (Compmisc.initial_env ()) ps in
          (* Debug.print @@ lazy
             (sprintf "attr typedtree:%s" (str_of_typedtree_structure tstr)); *)
          (match (List.hd_exn @@ List.rev ts.str_items).str_desc with
           | Tstr_eval (expr, _) -> begin
               match expr.exp_desc with
               | Texp_constant (Const_string (str, _, _)) -> str
               | Texp_constant (Const_int _) -> failwith "Const_int"
               | Texp_constant (Const_char _) -> failwith "Const_char"
               | Texp_constant (Const_float _) -> failwith "Const_float"
               | Texp_constant (Const_int32 _) -> failwith "Const_int32"
               | Texp_constant (Const_int64 _) -> failwith "Const_int64"
               | Texp_constant (Const_nativeint _) -> failwith "Const_nativeint"
               | _ -> failwith "Tstr_eval"
             end
           | _ -> failwith "unsupported")
        | _ -> failwith "unsupported"
      in
      match attr.Parsetree.attr_name.txt with
      | "constraints" ->
        (fenv, dtenv, renv),
        let constrs =
          Set.Poly.of_list @@ RefTypParser.constraints RefTypLexer.token @@
          Lexing.from_string content
        in
        Constraints constrs
      | "smtlib2" ->
        let constrs, _, pvs, fnpvs, wfpvs, fenv', dtenv' =
          SMT.Smtlib2.from_string ~fenv ~dtenv content
        in
        update_ref_dtenv dtenv';
        update_ref_fenv fenv';
        (fenv', dtenv', renv),
        Smtlib (Set.Poly.of_list constrs, pvs, fnpvs, wfpvs)
      | "rtype" -> (* e.g. [@@@rtype "main :: (x:{v : int | v > 0}) -> unit"] *)
        let renv' = RefTypParser.val_ty_env RefTypLexer.token @@ Lexing.from_string content in
        Debug.print @@ lazy ("[rtype] " ^ Rtype.Env.str_of ~config renv');
        (fenv, dtenv, Rtype.Env.set_with renv renv'),
        Skip
      | "check" | "assert" ->
        Debug.print @@ lazy ("[check] " ^ content);
        (fenv, dtenv, renv),
        Check (RefTypParser.assertions RefTypLexer.token @@ Lexing.from_string content)
      | name ->
        Debug.print @@ lazy ("unknown annotation: " ^ name);
        (fenv, dtenv, renv),
        Skip
  let rec top_level_aux ~config (constrs, pvs, fnpvs, wfpvs) envs = function
    | [] ->
      Debug.print @@ lazy
        "======================== Constraints Generated ========================"; []
    | item :: tl ->
      let envs', item = of_struct_item ~config envs item in
      match item with
      | Skip -> top_level_aux ~config (constrs, pvs, fnpvs, wfpvs) envs' tl
      | Constraints constrs' ->
        top_level_aux ~config
          (Set.Poly.union constrs @@ Set.Poly.map ~f:Typeinf.typeinf_formula(*ToDo*) constrs',
           pvs, fnpvs, wfpvs)
          envs' tl
      | Smtlib (constrs', pvs', fnpvs', wfpvs') ->
        top_level_aux ~config
          (Set.Poly.union constrs' constrs,
           Set.Poly.union pvs' pvs,
           Set.Poly.union fnpvs' fnpvs,
           Set.Poly.union wfpvs' wfpvs)
          envs' tl
      | Check asserts ->
        let fenv, dtenv, renv = envs in
        List.map asserts ~f:(function
            | tvar, Problem.Type rty ->
              let rty_def, constrs =
                match Rtype.Env.look_up renv tvar with
                | Some rty_def ->
                  Rtype.instantiate_val ~print:Debug.print ~config
                    Map.Poly.empty rty_def (Rtype.sort_of_val rty)
                | None -> failwith @@ Ident.name_of_tvar tvar ^ " not defined"
              in
              let pcsp =
                pcsp_of (constrs, pvs, fnpvs, wfpvs) fenv dtenv @@ Set.Poly.to_list @@
                Set.Poly.union (cgen_subtype_val ~config renv rty_def rty) constrs
              in
              Debug.print @@ lazy "\n*** constraints generated:\n";
              sprintf "type_of(%s) <: %s" (name_of_tvar tvar) (Rtype.str_of_val ~config rty),
              Problem.PAssertion (!mu_preds, !nu_preds, pcsp)
            | tvar, Problem.FinEff eff ->
              Debug.print @@ lazy
                (sprintf "fin_eff_of(%s) <: %s"
                   (name_of_tvar tvar) (Grammar.RegWordExp.str_of Fn.id eff));
              assert false
            | tvar, Problem.InfEff eff ->
              Debug.print @@ lazy
                (sprintf "inf_eff_of(%s) <: %s"
                   (name_of_tvar tvar) (Grammar.RegWordExp.str_of Fn.id eff));
              assert false) @
        top_level_aux ~config (constrs, pvs, fnpvs, wfpvs) envs' tl
  let top_level ~config ps =
    try
      let ts, _, _, _, _ = Typemod.type_structure (Compmisc.initial_env ()) ps in
      (* Debug.print @@ lazy
         (sprintf "typedtree structure:\n%s" (str_of_typedtree_structure ts)); *)
      let _ = mu_preds := Map.Poly.empty(*ToDo*) in
      let _ = nu_preds := Map.Poly.empty(*ToDo*) in
      Ok (top_level_aux ~config
            (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
            (Map.Poly.empty, init_dtenv (), Rtype.Env.mk_empty ())
            ts.str_items)
    with
    | Typemod.Error (loc, env, err) ->
      failwith @@ "Typemod.Error:\n" ^ MBcgen.str_of_stdbuf ~f:Location.print_report @@
      Typemod.report_error ~loc env err
    | Env.Error err ->
      failwith @@ "Env.Error:" ^ MBcgen.str_of_stdbuf ~f:Env.report_error err
    | Typecore.Error (loc, env, err) ->
      failwith @@ "Typecore.Error:\n" ^ MBcgen.str_of_stdbuf ~f:Location.print_report @@
      Typecore.report_error ~loc env err

  let from_ml_file config file =
    file
    |> In_channel.create
    |> Lexing.from_channel
    |> Parse.implementation
    |> top_level ~config
end
