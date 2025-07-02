open Core
open Common.Ext
open Common.Combinator
open LogicOld

type pred = sort_env_map * Formula.t
type papp = pred_bind * Term.t list
type ppapp = pred * papp

type t =
  | FCon of pred
  | PApp of papp
  (* non-parametric atom *)
  (* assume that papp is ground *)
  | PPApp of ppapp (* parametric atom *)

let mk_fcon pred = FCon pred
let mk_true () = mk_fcon (Map.Poly.empty, Formula.mk_true ())
let mk_false () = mk_fcon (Map.Poly.empty, Formula.mk_false ())
let mk_papp pvar sorts args = PApp ((pvar, sorts), args)
let mk_ppapp pred pvar sorts args = PPApp (pred, ((pvar, sorts), args))

let of_old_atom exi_senv cond = function
  | Atom.App (Predicate.Var (pvar, sorts), terms, _) ->
      let param_senv =
        Set.Poly.union_list
          (Formula.sort_env_of cond :: List.map ~f:Term.sort_env_of terms)
      in
      if
        Set.is_empty param_senv
        && (Formula.is_true cond || Formula.is_false cond)
      then mk_papp pvar sorts terms
      else
        let map =
          let s =
            Set.filter param_senv ~f:(fst >> Map.Poly.mem exi_senv >> not)
          in
          try Map.of_set_exn s
          with _ ->
            failwith @@ str_of_sort_env_list Term.str_of_sort @@ Set.to_list s
        in
        mk_ppapp (map, cond) pvar sorts terms
  | Atom.App (Psym _, _, _) as atom -> (
      try if Evaluator.eval_atom atom then mk_true () else mk_false ()
      with _ ->
        let param_senv = Atom.sort_env_of atom in
        mk_fcon
          ( Map.of_set_exn
            @@ Set.filter param_senv ~f:(fst >> Map.Poly.mem exi_senv >> not),
            Formula.mk_atom atom ))
  | atom ->
      failwith @@ "only atoms can be converted into examples. error with : "
      ^ Atom.str_of atom

let of_ground_atom cond exi_senv t =
  of_old_atom exi_senv cond
  @@ Logic.ExtTerm.to_old_atm exi_senv Map.Poly.empty t

let is_fcon = function FCon _ -> true | _ -> false
let is_papp = function PApp _ -> true | _ -> false
let is_ppapp = function PPApp _ -> true | _ -> false

let pvar_of = function
  | PApp ((pvar, _), _) | PPApp (_, ((pvar, _), _)) -> Some pvar
  | _ -> None

let sorts_of = function
  | PApp ((_, sorts), _) | PPApp (_, ((_, sorts), _)) -> Some sorts
  | _ -> None

let pvar_sorts_of = function
  | PApp ((pvar, sorts), _) | PPApp (_, ((pvar, sorts), _)) -> Some (pvar, sorts)
  | _ -> None

let tvs_of = function
  | FCon (_, phi) -> Formula.tvs_of phi
  | PApp ((_, _), ts) ->
      assert (List.for_all ts ~f:(fun t -> Set.is_empty @@ Term.tvs_of t));
      Set.Poly.empty
  | PPApp ((_, phi), ((_, _), ts)) ->
      Set.Poly.union_list (Formula.tvs_of phi :: List.map ~f:Term.tvs_of ts)

let args_of = function
  | FCon (_, _) -> None
  | PApp ((_, _), ts) -> Some ts
  | PPApp ((_, _), ((_, _), ts)) -> Some ts

let params_of = function
  | FCon (param_senv, _) -> param_senv
  | PApp (_, _) -> Map.Poly.empty
  | PPApp ((param_senv, _), _) -> param_senv

let to_old_atom = function
  | FCon (_, phi) ->
      if Formula.is_true phi then Some (Map.Poly.empty, Atom.mk_true ())
      else if Formula.is_false phi then Some (Map.Poly.empty, Atom.mk_false ())
      else None (*ToDo*)
  | PApp ((pvar, sorts), terms) ->
      Some (Map.Poly.empty, Atom.mk_pvar_app pvar sorts terms)
  | PPApp ((param_senv, phi), ((pvar, sorts), terms)) ->
      if Formula.is_true phi then
        Some (param_senv, Atom.mk_pvar_app pvar sorts terms)
      else None (*ToDo*)

let to_old_atom_with_phi = function
  | FCon (_, phi) when Fn.non Formula.is_true phi -> (phi, None)
  | PPApp ((param_senv, phi), ((pvar, sorts), terms))
    when Fn.non Formula.is_true phi ->
      (phi, Some (param_senv, Atom.mk_pvar_app pvar sorts terms))
  | atm -> (Formula.mk_true (), to_old_atom atm)

let to_atom atm =
  match to_old_atom atm with
  | None -> None
  | Some (param_senv, atm) -> Some (param_senv, Logic.ExtTerm.of_old_atom atm)

let to_old_formula pos = function
  | FCon (param_senv, phi) ->
      (param_senv, (if pos then Fn.id else Formula.mk_neg ~info:Dummy) @@ phi)
  | PApp ((pvar, sorts), terms) ->
      ( Map.Poly.empty,
        (if pos then Fn.id else Formula.mk_neg ~info:Dummy)
        @@ Formula.mk_atom
        @@ Atom.mk_pvar_app pvar sorts terms )
  | PPApp ((param_senv, phi), ((pvar, sorts), terms)) ->
      let papp =
        (if pos then Fn.id else Formula.mk_neg ~info:Dummy)
        @@ Formula.mk_atom
        @@ Atom.mk_pvar_app pvar sorts terms
      in
      ( param_senv,
        if Formula.is_true phi then papp else Formula.mk_imply phi papp )

let to_formula pos atm =
  let param_senv, phi = to_old_formula pos atm in
  (param_senv, Logic.ExtTerm.of_old_formula phi)

let to_old_formula_and_cond = function
  | FCon (param_senv, phi) -> (param_senv, phi, Formula.mk_true ())
  | PApp ((pvar, sorts), terms) ->
      ( Map.Poly.empty,
        Formula.mk_true (),
        Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts terms )
  | PPApp ((param_senv, phi), ((pvar, sorts), terms)) ->
      (param_senv, phi, Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts terms)

(* let cond_map_of ~id fenv cond =
   if Formula.is_true cond then Map.Poly.empty
   else
     match Z3Smt.Z3interface.check_sat ~id fenv [ cond ] with
     | `Sat model ->
         List.fold_left model ~init:Map.Poly.empty
           ~f:(fun ret ((tvar, _), term) ->
             match term with
             | None -> ret
             | Some t ->
                 Map.Poly.set ret ~key:tvar ~data:(Logic.ExtTerm.of_old_term t))
     | _ -> Map.Poly.empty *)

let to_formula_and_cond atm =
  let param_senv, cond, atm = to_old_formula_and_cond atm in
  ( param_senv,
    Logic.ExtTerm.of_old_formula cond,
    Logic.ExtTerm.of_old_formula atm )

let str_of_papp ((Ident.Pvar ident, _), terms) =
  sprintf "%s(%s)" ident
  @@ String.concat_mapi_list ~sep:", " terms ~f:(fun _i ->
         (*sprintf "[x%d] %s" (i+1) @@*) Term.str_of ~priority:Priority.comma)

let str_of = function
  | FCon (_, phi) -> Formula.str_of phi
  | PApp papp -> str_of_papp papp
  | PPApp ((_, phi), papp) ->
      if Formula.is_true phi then sprintf "%s" (str_of_papp papp)
      else
        String.paren
        @@ sprintf "%s | %s" (Formula.str_of phi) (str_of_papp papp)

let normalize_pred tvs (param_senv, phi) =
  let phi' = Normalizer.normalize @@ Evaluator.simplify phi in
  let param_senv' =
    Map.Poly.filteri param_senv ~f:(fun ~key:v ~data:_ -> Set.mem tvs v)
  in
  (param_senv', phi')

let normalize_papp (target, terms) =
  ( target,
    List.map terms ~f:(fun term ->
        let term' =
          Normalizer.normalize_term
          @@ Evaluator.simplify_term term (*ToDo: check*)
        in
        try Term.of_value (get_dtenv ()) @@ Evaluator.eval_term term'
        with _ -> term') )

let normalize = function
  | FCon pred as t -> FCon (normalize_pred (tvs_of t) pred)
  | PApp papp -> PApp (normalize_papp papp)
  | PPApp (pred, papp) as t ->
      PPApp (normalize_pred (tvs_of t) pred, normalize_papp papp)

let instantiate = function
  | FCon (param_senv, phi) ->
      (*ToDo: find one that satisfies phi?*)
      let sub = Map.Poly.map param_senv ~f:T_dt.mk_dummy in
      FCon (Map.Poly.empty, Formula.subst sub phi)
  | PApp papp -> PApp papp
  | PPApp ((param_senv, phi), (target, terms)) -> (
      (*ToDo: find one that satisfies phi*)
      let sub = Map.Poly.map param_senv ~f:T_dt.mk_dummy in
      let phi = Evaluator.simplify @@ Formula.subst sub phi in
      let terms =
        List.map terms
          ~f:(Term.subst sub >> Term.elim_let >> Evaluator.simplify_term)
      in
      try
        if
          Evaluator.eval phi
          && List.for_all terms ~f:(Term.fvs_of >> Set.is_empty)
          (*ToDo*)
        then
          PApp
            ( target,
              terms
              (*List.map terms ~f:(Evaluator.eval_term >> Term.of_value (get_dtenv ()))*)
            )
        else PPApp ((Map.Poly.empty, Formula.mk_false ()), (target, terms))
      with _ -> PPApp ((Map.Poly.empty, phi), (target, terms)))

(* assume all parameters in phi/ts are in dom(map) *)
let rename map = function
  | FCon (params, phi) ->
      FCon
        ( Map.rename_keys_and_drop_unused ~f:(Map.Poly.find map)
            params (* Could have a parameter not in phi *),
          Formula.rename map phi )
  | PApp ((pvar, sorts), ts) ->
      PApp ((pvar, sorts), List.map ~f:(Term.rename map) ts)
  | PPApp ((params, phi), ((pvar, sorts), ts)) ->
      PPApp
        ( ( Map.rename_keys_and_drop_unused ~f:(Map.Poly.find map)
              params (* Could have a parameter not in phi and ts *),
            Formula.rename map phi ),
          ((pvar, sorts), List.map ~f:(Term.rename map) ts) )

let subst sub = function
  | FCon (senv, phi) -> FCon (senv, Formula.subst sub phi)
  | PApp (pred, terms) -> PApp (pred, List.map terms ~f:(Term.subst sub))
  | PPApp ((senv, phi), (pred, terms)) ->
      let senv' =
        Map.Poly.filteri senv ~f:(fun ~key ~data:_ ->
            not @@ Map.Poly.mem sub key)
      in
      PPApp
        ( (senv', Formula.subst sub phi),
          (pred, List.map terms ~f:(Term.subst sub)) )

let iterate_senv (senv, his) atom =
  let ref_senv = ref [] in
  let ref_his = ref his in
  match atom with
  | FCon (params, phi) ->
      Formula.iter_term phi ~f:(function
        | Term.Var (t, s, _)
          when Map.Poly.mem params t && (not @@ Set.mem !ref_his t) ->
            ref_senv := (t, s) :: !ref_senv;
            ref_his := Set.add !ref_his t
        | _ -> ());
      (!ref_senv @ senv, !ref_his)
  | PApp _ -> (senv, his)
  | PPApp ((params, phi), (_, ts)) ->
      List.iter ts ~f:(fun t ->
          Term.iter_term t ~f:(function
            | Term.Var (t, s, _)
              when Map.Poly.mem params t && (not @@ Set.mem !ref_his t) ->
                ref_senv := (t, s) :: !ref_senv;
                ref_his := Set.add !ref_his t
            | _ -> ()));
      Formula.iter_term phi ~f:(function
        | Term.Var (t, s, _)
          when Map.Poly.mem params t && (not @@ Set.mem !ref_his t) ->
            ref_senv := (t, s) :: !ref_senv;
            ref_his := Set.add !ref_his t
        | _ -> ());
      (!ref_senv @ senv, !ref_his)

let iterate_vars bvs = function
  | FCon (_params, phi) ->
      (*let s = Map.Poly.key_set params in*)
      let tvs_set = (*Set.inter s @@*) Set.diff (Formula.fvs_of phi) bvs in
      (Set.union bvs tvs_set, Set.to_list tvs_set)
  | PApp (_, _) -> (bvs, [])
  | PPApp ((_params, phi), (_, ts)) ->
      (*let s = Map.Poly.key_set params in*)
      let tvs_set = (*Set.inter s @@*) Set.diff (Formula.fvs_of phi) bvs in
      List.fold_left ts
        ~init:Set.(union bvs tvs_set, to_list tvs_set)
        ~f:(fun (bvs, tvs) t ->
          let tvs_set' =
            (*Set.inter s @@*) Set.diff (Term.tvs_of (*ToDo*) t) bvs
          in
          (Set.union bvs tvs_set', tvs @ Set.to_list tvs_set'))

let normalize_params atm =
  let _, tvs = iterate_vars Set.Poly.empty atm in
  let map =
    Map.Poly.of_alist_exn
    @@ List.mapi tvs ~f:(fun i x ->
           (x, Ident.mk_dontcare (string_of_int (i + 1))))
  in
  rename map atm

let exists ~f = function
  | FCon _ -> false
  | PApp (_, terms) | PPApp (_, (_, terms)) -> List.exists ~f terms

let is_non_empty_atm nepvs atm =
  match to_old_atom_with_phi atm with
  | _, None -> false
  | _, Some (_, atm) ->
      assert (Atom.is_pvar_app atm);
      let pvar, sorts, _, _ = Atom.let_pvar_app atm in
      if Set.mem nepvs (Ident.pvar_to_tvar pvar) then
        Set.length (Atom.tvs_of atm) = List.length sorts
      else false

(* type t =
   | FCon of pred
   | PApp of papp (* non-parametric atom *) (* assume that papp is ground *)
   | PPApp of ppapp (* parametric atom *)
*)
let equal atm1 atm2 =
  match (atm1, atm2) with
  | FCon (_, phi1), FCon (_, phi2) -> Stdlib.(phi1 = phi2)
  | PApp (_, ts1), PApp (_, ts2) -> Stdlib.(ts1 = ts2)
  | PPApp ((_, phi1), (_, ts1)), PPApp ((_, phi2), (_, ts2)) ->
      Stdlib.(phi1 = phi2) && Stdlib.(ts1 = ts2)
  | _, _ -> false
