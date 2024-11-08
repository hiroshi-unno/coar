open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.Ident
open Ast.Logic
open Ast.AffineTerm

module type OptimalityCheckerType = sig
  val check :
    ?only_simple:bool ->
    Messenger.t option * int option ->
    Ident.tvar ->
    PCSP.Problem.t ->
    sort_env_map ->
    term_subst_map ->
    CHCOpt.Problem.solution
end

let verbose = false

module Debug =
  Debug.Make ((val Debug.Config.(if verbose then enable else disable)))

let _ = Debug.set_module_name "OptimalityChecker"
let pwf = Tvar "WF"
let pnc (Tvar ident) i = Tvar (sprintf "%s_%d" ident i)
let pnt (Tvar ident) (Tvar t) = Tvar (sprintf "%s_%s" ident t)
let pn (Tvar ident) i = Tvar (sprintf "%s%d" ident i)
let base_pf = pn (Tvar "FN")
let base_ptseitin = pn (Tvar "PTsetin_")
let id = Atomic.make None

let set_id new_id =
  Atomic.set id new_id;
  Debug.set_id new_id

let is_ptseitin (Tvar var) = String.is_prefix ~prefix:"PTsetin" var

let mk_tseitin_pred_clause ?(enable = true) i (args, sargs) exi_senv phiss =
  let size = List.length phiss in
  if size <= 1 then (exi_senv, List.concat @@ phiss)
  else if not enable then
    (exi_senv, [ ExtTerm.or_of @@ List.map phiss ~f:ExtTerm.and_of ])
  else
    let pvars = Array.init size ~f:(fun j -> pn (base_ptseitin i) j) in
    let phis =
      List.mapi phiss ~f:(fun i phis ->
          ExtTerm.imply_of (ExtTerm.mk_var_app pvars.(i) args)
          @@ ExtTerm.and_of phis)
    in
    let exi_senv =
      Array.fold pvars ~init:exi_senv ~f:(fun acc p ->
          Map.Poly.add_exn ~key:p
            ~data:(Sort.mk_fun @@ sargs @ [ ExtTerm.SBool ])
            acc)
    in
    let tseitin_phi =
      ExtTerm.or_of
      @@ List.init size ~f:(fun i -> ExtTerm.mk_var_app pvars.(i) args)
    in
    (exi_senv, tseitin_phi :: phis)

let mk_fresh_args sort =
  let senv = mk_fresh_sort_env_list @@ Sort.args_of sort in
  let args = List.map senv ~f:(fst >> ExtTerm.mk_var) in
  (args, senv)

let simple_check ~is_max p exi_senv theta =
  let sol = Map.Poly.find_exn theta p in
  let sort = Map.Poly.find_exn exi_senv p in
  let args, param_senv = mk_fresh_args sort in
  let phi = ExtTerm.beta_reduction (Term.mk_apps sol args) in
  let phi =
    ExtTerm.to_old_fml exi_senv (Map.Poly.of_alist_exn param_senv, phi)
  in
  let phi = if is_max then phi else LogicOld.Formula.mk_neg phi in
  try Z3Smt.Z3interface.is_valid ~id:(Atomic.get id) Map.Poly.empty phi
  with _ -> false

let dnf_clause_to_formula (ps, ns, phi) =
  let open LogicOld in
  Formula.and_of
  @@ phi
     :: (Set.to_list
        @@ Set.union
             (Set.Poly.map ps ~f:Formula.mk_atom)
             (Set.Poly.map ns ~f:(Formula.mk_atom >> Formula.mk_neg)))

let merge_get_leq pure_phi =
  (* assume [pure_phi] is a conjunction *)
  let open LogicOld in
  let ps, _ = Formula.atoms_of pure_phi in
  let ps = Set.Poly.map ps ~f:Normalizer.normalize_atom in
  let subst =
    Set.fold ps ~init:Map.Poly.empty ~f:(fun acc -> function
      | Atom.App (Predicate.Psym T_int.Geq, [ t1; t2 ], info) as atm
        when is_affine t1 ->
          let neg_atm =
            Atom.App (Predicate.Psym T_int.Leq, [ t1; t2 ], info)
            |> Normalizer.normalize_atom
          in
          if Set.mem ps neg_atm then
            let eq_atm =
              Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], info)
            in
            Map.Poly.set acc ~key:atm ~data:eq_atm
            |> Map.Poly.set ~key:neg_atm ~data:eq_atm
          else acc
      | _ -> acc)
  in
  Set.Poly.map ps ~f:(fun atm ->
      match Map.Poly.find subst atm with
      | Some atm -> Formula.mk_atom atm
      | None -> Formula.mk_atom atm)
  |> Set.to_list |> Formula.and_of

let dnf_of_pure_formula exi_senv pure_phi =
  let open LogicOld in
  let rec inner acc = function
    | Formula.BinaryOp (Or, phi1, phi2, _) ->
        Set.union (inner acc phi1) (inner acc phi2)
    | phi -> Set.add acc phi
  in
  pure_phi |> Formula.nnf_of
  |> Formula.dnf_of ~process_pure:true exi_senv
  |> Set.Poly.map ~f:dnf_clause_to_formula
  |> Set.fold ~init:Set.Poly.empty ~f:inner
  |> Set.Poly.map ~f:merge_get_leq
(* |> Set.Poly.map ~f:(Z3Smt.Z3interface.simplify ~id:(Atomic.get id) (LogicOld.get_fenv ()) ~timeout:(Some 20000)) *)

(* assume phi is pure formula*)
let apply_qelim_on_pure_formula bound exi_senv uni_senv phi =
  let open LogicOld in
  let open Formula in
  let call_qelim phi =
    Qelim.qelim_old bound exi_senv (uni_senv, nnf_of @@ mk_neg phi)
    |> snd |> mk_neg |> nnf_of |> Evaluator.simplify
  in
  let phi' =
    ExtTerm.to_old_fml exi_senv (uni_senv, phi)
    |> Formula.nnf_of |> Evaluator.simplify
    |> dnf_of_pure_formula (to_old_sort_env_map exi_senv)
    |> Set.Poly.map ~f:call_qelim |> Set.to_list |> Formula.or_of
  in
  let fvs =
    Formula.term_sort_env_of phi'
    |> Set.filter ~f:(fun (v, _) -> not @@ Map.Poly.mem bound v)
    |> Set.to_list
    |> List.sort ~compare:Stdlib.compare
  in
  let phi'' =
    Z3Smt.Z3interface.qelim ~id:(Atomic.get id) ~fenv:(LogicOld.get_fenv ())
    @@ Formula.mk_exists fvs phi'
  in
  assert (Fn.non Formula.is_bind phi'');
  let fvs =
    Formula.term_sort_env_of phi''
    |> Set.filter ~f:(fun (v, _) -> not @@ Map.Poly.mem bound v)
    |> Set.to_list
    |> List.sort ~compare:Stdlib.compare
  in
  Debug.print_log ~tag:"apply_qelim_on_pure_formula"
  @@ lazy (Formula.str_of phi'');
  (fvs, ExtTerm.of_old_formula phi'')

let eqs_of sorts x y =
  ExtTerm.and_of @@ List.map3_exn sorts x y ~f:ExtTerm.eq_of

let neqs_of sorts x y =
  ExtTerm.or_of @@ List.map3_exn sorts x y ~f:ExtTerm.neq_of

let apply_pred theta p args =
  ExtTerm.beta_reduction (Term.mk_apps (Map.Poly.find_exn theta p) args)

let mk_fvs_fns fvs uni_senv pf params params_sorts =
  List.unzip
  @@ List.mapi fvs ~f:(fun i v ->
         let sort = Map.Poly.find_exn uni_senv v in
         let pfv = pn (pn pf 0) i in
         let pfvsort = Sort.mk_fun @@ params_sorts @ [ sort; ExtTerm.SBool ] in
         ((pfv, pfvsort), ExtTerm.mk_var_app pfv (params @ [ ExtTerm.mk_var v ])))

let pvars_of p exi_senv =
  let sort = Map.Poly.find_exn exi_senv p in
  Map.Poly.remove exi_senv p |> Map.Poly.to_alist
  |> List.cons (p, sort)
  |> List.sort ~compare:Stdlib.compare

(* [pred_phi] connected to [pure_phi] by "and" *)
(* result are disjunction formulas of [pred_phi] and [pure_phi]*)
let apply_qelim bound exi_senv uni_senv pred_phi pure_phi =
  let open LogicOld in
  let pred_phi = ExtTerm.to_old_fml exi_senv (uni_senv, pred_phi) in
  let pure_phi = ExtTerm.to_old_fml exi_senv (uni_senv, pure_phi) in
  dnf_of_pure_formula (to_old_sort_env_map exi_senv) pure_phi
  |> Set.Poly.map ~f:(Formula.mk_and pred_phi)
  |> Set.Poly.map ~f:(fun phi ->
         Debug.print_log ~tag:"qelim:" @@ lazy (LogicOld.Formula.str_of phi);
         let _, _, term =
           Qelim.qelim bound exi_senv
             (uni_senv, [], ExtTerm.of_old_formula @@ Evaluator.simplify_neg phi)
         in
         Debug.print_log ~tag:"after-qelim:"
         @@ lazy (ExtTerm.str_of_formula exi_senv uni_senv term);
         ExtTerm.neg_of term)

let check exi_senv uni_senv cond phi =
  Evaluator.check
    ~cond:(ExtTerm.to_old_fml exi_senv (uni_senv, cond))
    (Z3Smt.Z3interface.is_valid ~id:(Atomic.get id) (LogicOld.get_fenv ()))
    (ExtTerm.to_old_fml exi_senv (uni_senv, phi))

let inters sets =
  let rec inner = function
    | [] -> Set.Poly.empty
    | [ hd ] -> hd
    | hd :: tl -> Set.inter hd @@ inner tl
  in
  inner sets

let has v t = Set.mem (LogicOld.Term.tvs_of t) v

let is v = function
  | LogicOld.Term.Var (v1, _, _) -> Stdlib.(v = v1)
  | _ -> false

let rename phi =
  let open LogicOld in
  let param_senv = Formula.tvs_of phi in
  let subst =
    Set.to_list param_senv
    |> List.map ~f:(fun v -> (v, Ident.mk_fresh_tvar ()))
    |> Map.Poly.of_alist_exn
  in
  Formula.rename subst phi

let is_elimable_pair fnsols_senv phi0 (v, term) =
  let open LogicOld in
  let bound =
    Formula.sort_env_of phi0
    |> Set.filter ~f:(fun (v1, _) ->
           Stdlib.(v1 = v) || List.Assoc.mem ~equal:Stdlib.( = ) fnsols_senv v1)
  in
  let phi =
    Formula.mk_exists (Set.to_list bound) @@ Formula.apply_pred (v, phi0) term
  in
  Debug.print_log ~tag:"is_elimable_pair"
  @@ lazy
       (sprintf "%s -> %s : %s" (name_of_tvar v) (Term.str_of term)
          (Formula.str_of phi));
  (fun ret ->
    if ret then Debug.print_log ~tag:"is_elimable_pair" @@ lazy "yes"
    else Debug.print_log ~tag:"is_elimable_pair" @@ lazy "no";
    ret)
  @@
  let fenv = get_fenv () in
  Z3Smt.Z3interface.is_valid ~id:(Atomic.get id) fenv
  @@ Z3Smt.Z3interface.qelim ~id:(Atomic.get id) ~fenv phi

let simple_get_eq_pair_with_dnf fnsols_senv v dnf check_flag phi0 =
  let open LogicOld in
  let dnf =
    Set.Poly.map dnf ~f:(fun phi ->
        let ps, _ = Formula.atoms_of @@ Evaluator.simplify phi in
        Set.filter ps ~f:(fun atm ->
            Set.exists (Atom.terms_of atm) ~f:(fun t ->
                has v t || List.exists fnsols_senv ~f:(fun (v0, _) -> has v0 t)))
        |> Set.Poly.map ~f:Formula.mk_atom
        |> Set.to_list |> Formula.and_of)
  in
  match check_flag with
  | `Unuseable -> Set.Poly.empty
  | `Useable | `NeedCheck -> (
      let phi = Formula.and_of [ phi0; Formula.or_of @@ Set.to_list dnf ] in
      let bound =
        Formula.sort_env_of phi
        |> Set.filter ~f:(fun (v1, _) ->
               Stdlib.(v1 <> v)
               && (not @@ List.Assoc.mem ~equal:Stdlib.( = ) fnsols_senv v1))
      in
      let phi = Formula.mk_forall (Set.to_list bound) phi in
      Debug.print_log ~tag:"simple get eq pair" @@ lazy (Formula.str_of phi);
      match
        Z3Smt.Z3interface.check_sat ~id:(Atomic.get id) (get_fenv ()) [ phi ]
      with
      | `Sat models -> (
          let models =
            List.map models ~f:(fun ((v, _s), r) -> (v, r))
            |> Map.Poly.of_alist_exn
          in
          match Map.Poly.find models v with
          | Some (Some ret) ->
              if false (*ToDo*) && Stdlib.(`NeedCheck = check_flag) then
                if is_elimable_pair fnsols_senv phi0 (v, ret) then
                  Set.Poly.singleton (v, ret)
                else (
                  Debug.print_log @@ lazy "eq_pair cannot be used...";
                  Set.Poly.empty)
              else (
                Debug.print_log ~tag:"simple geted a eq pair"
                @@ lazy
                     (sprintf "%s -> %s" (Ident.name_of_tvar v)
                        (Term.str_of ret));
                Set.Poly.singleton (v, ret))
          | Some None ->
              Set.Poly.singleton
                ( v,
                  Term.mk_dummy
                  @@ List.Assoc.find_exn ~equal:Stdlib.( = ) fnsols_senv v )
          | None -> Set.Poly.empty)
      | _ -> Set.Poly.empty)

let complex_get_eq_pair v args atms exi_senv fnsols_senv check_flag phi0 =
  let open LogicOld in
  match check_flag with
  | `Unuseable -> Set.Poly.empty
  | _ ->
      let pure =
        Formula.and_of @@ Set.to_list @@ Set.Poly.map atms ~f:Formula.mk_atom
      in
      let dnfs =
        Set.to_list @@ dnf_of_pure_formula (to_old_sort_env_map exi_senv) phi0
      in
      let useable t =
        Set.for_all (Term.tvs_of t) ~f:(fun v1 ->
            Stdlib.(v1 = v) || Set.mem args v1)
      in
      List.foldi dnfs ~init:(true, []) ~f:(fun i (continue, acc) phi ->
          if not continue then (false, [])
          else
            let phi = Formula.mk_and pure phi in
            Debug.print_log ~tag:"(complex) dnf"
            @@ lazy (String.paren @@ sprintf "%d/%d" (i + 1) @@ List.length dnfs);
            Debug.print_log ~tag:"(complex) mk elim eqs form:"
            @@ lazy (Formula.str_of phi);
            let ps, _ = Formula.atoms_of @@ Evaluator.simplify phi in
            let ps = Set.Poly.map ps ~f:Normalizer.normalize_atom in
            let ps_with_v =
              Set.filter ps ~f:(fun atm ->
                  Set.exists (Atom.terms_of atm) ~f:(has v))
            in
            let pure_phi_with_v =
              Formula.and_of
              @@ List.map ~f:Formula.mk_atom
              @@ Set.to_list ps_with_v
            in
            let check_is_elimable_phi = Formula.mk_and pure_phi_with_v phi0 in
            (fun ret ->
              if Set.is_empty ret then (false, []) else (continue, ret :: acc))
            @@ Set.filter
                 ~f:(is_elimable_pair fnsols_senv check_is_elimable_phi)
            @@ Set.Poly.filter_map ps_with_v ~f:(fun atm ->
                   Debug.print_log ~tag:"(complex) mk elim eq form atom:"
                   @@ lazy (Atom.str_of atm);
                   match atm with
                   | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _)
                     when Fn.non Term.is_int_sort (Term.sort_of t1) ->
                       if
                         is v t1 && useable t2
                         && is_elimable_pair fnsols_senv check_is_elimable_phi
                              (v, t2)
                       then Some (v, t2)
                       else if
                         is v t2 && useable t1
                         && is_elimable_pair fnsols_senv check_is_elimable_phi
                              (v, t2)
                       then Some (v, t1)
                       else None
                   | Atom.App (Predicate.Psym T_bool.Eq, [ t1; _ ], _)
                     when is_affine t1 && has v t1 && useable t1 -> (
                       match extract_term_from_affine (is v) t1 with
                       | Some t1'
                         when is_elimable_pair fnsols_senv check_is_elimable_phi
                                (v, t1') ->
                           Some (v, t1')
                       | _ -> None)
                   | Atom.App (Predicate.Psym T_int.Geq, [ t1; _ ], _)
                     when is_affine t1 && has v t1 && useable t1 -> (
                       match extract_term_from_affine (is v) t1 with
                       | Some t1'
                         when is_elimable_pair fnsols_senv check_is_elimable_phi
                                (v, t1') ->
                           Some (v, t1')
                       | _ -> None)
                   | _ -> None))
      |> snd |> inters

let check_can_use_geq exi_senv uni_senv pure_phi phi0 =
  match check exi_senv uni_senv pure_phi phi0 with
  | Some ret -> if ret then `Useable else `Unuseable
  | None -> `NeedCheck

let qe_subst_of v args exi_senv uni_senv fnsols_senv pure_phi phi0 =
  let open LogicOld in
  let to_old phi = ExtTerm.to_old_fml exi_senv (uni_senv, phi) in
  Debug.print_log ~tag:"phi0:"
  @@ lazy (ExtTerm.str_of_formula exi_senv uni_senv phi0);
  let phi0', check_flag =
    match check exi_senv uni_senv pure_phi phi0 with
    | Some true -> (ExtTerm.mk_bool true, `Useable)
    | _ -> (phi0, `NeedCheck)
  in
  let old_phi0 = to_old phi0' in
  let dnfs =
    dnf_of_pure_formula (to_old_sort_env_map exi_senv) (to_old pure_phi)
  in
  let useable t =
    Set.for_all (Term.tvs_of t) ~f:(fun v1 ->
        Stdlib.(v1 = v) || Set.mem args v1)
  in
  let simple_substs =
    simple_get_eq_pair_with_dnf fnsols_senv v dnfs check_flag old_phi0
  in
  let dnfs = Set.to_list dnfs in
  List.mapi dnfs ~f:(fun i phi ->
      Debug.print_log ~tag:"start for a dnf"
      @@ lazy (String.paren @@ sprintf "%d/%d" (i + 1) @@ List.length dnfs);
      Debug.print_log ~tag:"mk elim eqs form:" @@ lazy (Formula.str_of phi);
      let ps, _ = Formula.atoms_of @@ Evaluator.simplify phi in
      let ps = Set.Poly.map ps ~f:Normalizer.normalize_atom in
      let ps_with_v =
        Set.filter ps ~f:(fun atm -> Set.exists (Atom.terms_of atm) ~f:(has v))
      in
      (fun ret ->
        Set.iter ret ~f:(fun (v, term) ->
            Debug.print_log ~tag:"qe subst candicate"
            @@ lazy (sprintf "%s -> %s" (name_of_tvar v) (Term.str_of term)));
        ret)
      @@ Set.union
           (complex_get_eq_pair v args ps_with_v exi_senv fnsols_senv check_flag
              old_phi0)
      @@ Set.Poly.filter_map ps_with_v ~f:(fun atm ->
             Debug.print_log ~tag:"mk elim eq form atom:"
             @@ lazy (Atom.str_of atm);
             match atm with
             | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _)
               when Fn.non Term.is_int_sort (Term.sort_of t1) ->
                 if is v t1 && useable t2 then Some (v, t2)
                 else if is v t2 && useable t1 then Some (v, t1)
                 else None
             | Atom.App (Predicate.Psym T_bool.Eq, [ t1; _ ], _)
               when is_affine t1 && has v t1 && useable t1 -> (
                 match extract_term_from_affine (is v) t1 with
                 | Some t -> Some (v, t)
                 | _ -> None)
             | _ -> None))
  |> inters |> Set.union simple_substs
  |> Set.Poly.map ~f:(fun (v, term) ->
         Debug.print_log ~tag:"qe subst"
         @@ lazy (sprintf "%s -> %s" (name_of_tvar v) (Term.str_of term));
         (v, ExtTerm.of_old_term term))
  |> Set.to_list
  |> function
  | (v, t) :: _ -> Map.Poly.singleton v t
  | [] -> Map.Poly.empty

(*
   when there is a formula is x1 = x2 + x3 + x4 /\ x5 = x2 + x3 + x4,
   change to x1 = x5
*)
let merge_eqs_with v args exi_senv uni_senv pure_phi phi_map =
  let open LogicOld in
  let to_old phi =
    ExtTerm.to_old_fml exi_senv (uni_senv, phi)
    |> Evaluator.simplify |> Normalizer.normalize
  in
  let old_phi_map =
    Map.Poly.map phi_map ~f:(fun (pure, psi) -> (to_old pure, psi))
  in
  let old_pure = to_old pure_phi in
  let dnfs = dnf_of_pure_formula (to_old_sort_env_map exi_senv) old_pure in
  let mk_term v =
    Term.mk_var v (Map.Poly.find_exn uni_senv v |> ExtTerm.to_old_sort)
  in
  let search_eq_pairs atms term =
    Set.Poly.map atms ~f:(fun atm ->
        Set.Poly.of_list
        @@ List.filter_map args ~f:(fun v1 ->
               match atm with
               | Atom.App (Predicate.Psym T_bool.Eq, [ t1; _ ], _)
                 when (Term.is_int_sort @@ Term.sort_of t1)
                      && Set.length (Term.tvs_of t1) > 2 -> (
                   match extract_term_from_affine (is v1) t1 with
                   | Some affine
                     when Evaluator.is_valid
                            (Z3Smt.Z3interface.is_valid ~id:(Atomic.get id)
                               (get_fenv ()))
                            (Formula.eq affine term) ->
                       Some (atm, T_bool.mk_eq (mk_term v) (mk_term v1))
                   | _ -> None)
               | _ -> None))
    |> Set.to_list |> Set.Poly.union_list
  in
  Set.Poly.map dnfs ~f:(fun phi ->
      (* Debug.print_log ~tag:"mk merge eqs form:" @@ Formula.str_of phi; *)
      let ps, _ = Formula.atoms_of phi in
      let ps_with_v =
        Set.filter ps ~f:(fun atm -> Set.exists (Atom.terms_of atm) ~f:(has v))
      in
      Set.Poly.map ps_with_v ~f:(fun atm ->
          (* Debug.print_log ~tag:"mk merge eq form atom:" @@ Atom.str_of atm; *)
          match atm with
          | Atom.App (Predicate.Psym T_bool.Eq, [ t1; _ ], _)
            when has v t1 && is_affine t1 && Set.length (Term.tvs_of t1) > 2
            -> (
              match extract_term_from_affine (is v) t1 with
              | Some affine ->
                  let pairs = search_eq_pairs ps affine in
                  Set.union pairs
                    (Set.Poly.map pairs ~f:(fun (_, atm1) -> (atm, atm1)))
              | _ -> Set.Poly.empty)
          | _ -> Set.Poly.empty)
      |> Set.to_list |> Set.Poly.union_list)
  |> Set.to_list |> inters
  |> fun atom_pairs ->
  let atom_map =
    Set.fold atom_pairs ~init:Map.Poly.empty ~f:(fun acc (atm1, atm2) ->
        match Map.Poly.find acc atm1 with
        | None -> Map.Poly.add_exn acc ~key:atm1 ~data:(Formula.mk_atom atm2)
        | Some phi ->
            Map.Poly.set acc ~key:atm1
              ~data:(Formula.and_of [ Formula.mk_atom atm2; phi ]))
  in
  let map_atms phi =
    Formula.map_atom phi ~f:(fun atm ->
        match Map.Poly.find atom_map atm with
        | Some phi ->
            Debug.print_log ~tag:"merge eq"
            @@ lazy (sprintf "%s -> %s" (Atom.str_of atm) (Formula.str_of phi));
            phi
        | None -> Formula.mk_atom atm)
  in
  ( ExtTerm.of_old_formula @@ map_atms old_pure,
    Map.Poly.map old_phi_map ~f:(fun (pure, psi) ->
        (ExtTerm.of_old_formula pure, psi)) )

let filter_pfapps exi_senv uni_senv pfapps pure_formula
    (phi_map : (int, term * term) Map.Poly.t) =
  let sol_args =
    let sols =
      List.map pfapps ~f:(fun (_, (_, (_, fnret))) ->
          fnret |> ExtTerm.let_var |> fst)
    in
    fun p -> List.filter sols ~f:(Stdlib.( <> ) p)
  in
  let pfapps =
    List.map pfapps
      ~f:(fun ((fnpred, ext), ((phi_pf, pfapp), (fnargs, fnret))) ->
        let pfapp' =
          ExtTerm.of_old_formula @@ Evaluator.simplify
          @@ ExtTerm.to_old_fml exi_senv (uni_senv, pfapp)
        in
        ((fnpred, ext), ((phi_pf, pfapp'), (fnargs, fnret))))
  in
  let fnsols_senv =
    List.filter_map pfapps
      ~f:(fun ((fnpred, _), ((phi_pf, pfapp), (_, fnret))) ->
        if
          (not (Set.mem (ExtTerm.fvs_of pfapp) fnpred)) || Option.is_some phi_pf
        then None
        else
          let v, _ = ExtTerm.let_var fnret in
          let sort = Map.Poly.find_exn uni_senv v |> ExtTerm.to_old_sort in
          Some (v, sort))
  in
  let fnsol_vars = fnsols_senv |> List.map ~f:fst |> Set.Poly.of_list in
  let rec inner pfapps pure_formula (phi_map : (int, term * term) Map.Poly.t)
      subst_map =
    List.fold pfapps ~init:(pure_formula, phi_map, subst_map, [])
      ~f:(fun
          (pure_phi, phi_map, subst_map, acc)
          ((fnpred, ext), ((phi_pf, pfapp), (fnargs, fnret)))
        ->
        Debug.print_log ~tag:"*** try to elim fn:"
        @@ lazy (ExtTerm.str_of_formula exi_senv uni_senv pfapp);
        if ExtTerm.is_false pfapp then (
          Debug.print @@ lazy "";
          ( pure_phi,
            phi_map,
            subst_map,
            ((fnpred, ext), ((phi_pf, pfapp), (fnargs, fnret))) :: acc ))
        else
          let v = fst @@ ExtTerm.let_var fnret in
          let args =
            List.map fnargs ~f:(fun term -> ExtTerm.let_var term |> fst)
          in
          let args =
            args
            @
            if ExtTerm.is_pvar_app exi_senv uni_senv pfapp then sol_args v
            else []
          in
          let pure_phi, phi_map =
            merge_eqs_with v args exi_senv uni_senv pure_phi phi_map
          in
          let phi_map =
            Map.Poly.map phi_map ~f:(fun (phi, psi) ->
                match check exi_senv uni_senv pure_formula phi with
                | Some false -> (ExtTerm.mk_bool false, psi)
                | _ -> (phi, psi))
          in
          let phi0 =
            if Set.mem fnsol_vars v then
              Map.Poly.to_alist phi_map
              |> List.filter_map ~f:(fun (_, (phi, psi)) ->
                     if
                       Fn.non Set.is_empty
                       @@ Set.inter (ExtTerm.fvs_of phi) fnsol_vars
                       || Fn.non Set.is_empty
                          @@ Set.inter (ExtTerm.fvs_of psi) fnsol_vars
                     then Some phi
                     else None)
              |> ExtTerm.and_of
            else ExtTerm.mk_bool false
          in
          let subst =
            qe_subst_of v (Set.Poly.of_list args) exi_senv uni_senv
              (if Set.mem fnsol_vars v then fnsols_senv else [])
              pure_phi phi0
          in
          if Map.Poly.is_empty subst then (
            Debug.print @@ lazy "";
            ( pure_phi,
              phi_map,
              subst_map,
              ((fnpred, ext), ((phi_pf, pfapp), (fnargs, fnret))) :: acc ))
          else
            let subst_map = Map.Poly.map subst_map ~f:(ExtTerm.subst subst) in
            let phi_map' =
              Map.Poly.map phi_map ~f:(fun (phi, psi) ->
                  (ExtTerm.subst subst phi, ExtTerm.subst subst psi))
            in
            let pure_phi' = ExtTerm.subst subst pure_phi in
            Debug.print_log ~tag:"fn elimed"
            @@ lazy (ExtTerm.str_of_formula exi_senv uni_senv pfapp);
            let acc =
              ((fnpred, ext), ((phi_pf, pfapp), (fnargs, fnret))) :: acc
            in
            Debug.print @@ lazy "";
            (pure_phi', phi_map', Map.force_merge subst subst_map, acc))
    |> fun (pure_phi', phi_map', subst_map', pfapps') ->
    if Map.Poly.length subst_map <> Map.Poly.length subst_map' then
      inner pfapps' pure_phi' phi_map' subst_map'
    else
      ( ExtTerm.simplify_formula exi_senv uni_senv @@ pure_phi',
        Map.Poly.map phi_map' ~f:(fun (phi0, psi) ->
            (ExtTerm.simplify_formula exi_senv uni_senv @@ phi0, psi)),
        pfapps',
        subst_map' )
  in
  Debug.print @@ lazy "";
  inner pfapps pure_formula phi_map Map.Poly.empty

let has_useable_pvar pcsp uni_senv atms =
  let exi_senv = PCSP.Problem.senv_of pcsp in
  Set.exists atms ~f:(fun t ->
      if ExtTerm.is_pvar_app exi_senv uni_senv t then
        PCSP.Problem.is_ne_pred pcsp @@ ExtTerm.pvar_of_atom t
      else false)

let elim_clauses pcsp =
  PCSP.Problem.clauses_of pcsp
  |> Set.filter ~f:(fun (params_senv, ps, ns, _) ->
         (not (has_useable_pvar pcsp params_senv ps))
         && not (has_useable_pvar pcsp params_senv ns))
  |> PCSP.Problem.of_clauses ~params:(PCSP.Problem.params_of pcsp)
  |> PCSP.Problem.remove_unused_params

let defs_of pcsp =
  PCSP.Problem.clauses_of pcsp
  |> Set.to_list
  |> List.filter ~f:(fun (params, ps, ns, _) ->
         if Set.is_empty ps then false
         else if
           has_useable_pvar pcsp params ps || has_useable_pvar pcsp params ns
         then false
         else true)

let goals_of pcsp =
  PCSP.Problem.clauses_of pcsp
  |> Set.to_list
  |> List.filter ~f:(fun (params, ps, ns, _) ->
         if has_useable_pvar pcsp params ps || has_useable_pvar pcsp params ns
         then false
         else Set.is_empty ps)

let to_cnf_clauses exi_senv uni_senv phi =
  ExtTerm.nnf_of phi
  |> ExtTerm.cnf_of exi_senv uni_senv
  |> Set.Poly.map ~f:(fun (ps, ns, phi) -> (uni_senv, ps, ns, phi))

let head_is p (_, ps, _, _) =
  assert (Set.is_singleton ps);
  let p_y, _ =
    Set.to_list ps |> List.hd_exn |> Term.let_apps |> fun (p_y, args_y) ->
    (fst @@ Term.let_var p_y, args_y)
  in
  Stdlib.(p_y = p)

let bwd_theta_of ~init exi_senv clauses =
  let inner (uni_senv, ps, ns, phi) =
    assert (Set.is_singleton ps && Set.is_empty ns);
    let p_y, args_y =
      Set.to_list ps |> List.hd_exn |> Term.let_apps |> fun (p_y, args_y) ->
      (fst @@ Term.let_var p_y, args_y)
    in
    let sort_env =
      List.map args_y ~f:(fun t ->
          let v, _ = ExtTerm.let_var t in
          (v, Map.Poly.find_exn uni_senv v))
    in
    let bound = sort_env |> Map.Poly.of_alist_exn in
    let fvs, pure_phi =
      apply_qelim_on_pure_formula bound exi_senv uni_senv @@ ExtTerm.neg_of phi
    in
    assert (List.is_empty fvs);
    (p_y, ExtTerm.mk_lambda sort_env pure_phi, sort_env, args_y)
  in
  List.map clauses ~f:inner
  |> List.fold ~init ~f:(fun acc (v, term, sort_env, args_y) ->
         match Map.Poly.find acc v with
         | None -> Map.Poly.add_exn acc ~key:v ~data:term
         | Some term1 ->
             let term = ExtTerm.beta_reduction (Term.mk_apps term args_y) in
             let term1 = ExtTerm.beta_reduction (Term.mk_apps term1 args_y) in
             Map.Poly.set acc ~key:v
               ~data:
                 (ExtTerm.mk_lambda sort_env @@ ExtTerm.or_of [ term; term1 ]))

let pysenv_of pvars =
  Map.Poly.of_alist_exn
  @@ List.map pvars ~f:(fun (pv, s) ->
         (pv, mk_fresh_sort_env_list @@ Sort.args_of s))

let idxs_of =
  List.mapi ~f:(fun i (p, sort) ->
      (p, ((i, p), Sort.args_of sort, Tvar (sprintf "DOM_%s" (name_of_tvar p)))))
