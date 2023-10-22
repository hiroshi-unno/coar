open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld

type mode =
  | Mu | Mu' | Mus | Nu(* sound but incomplete *) of int(* range *)
  | SkolemFun | SkolemPred [@@ deriving yojson]

module Config = struct
  type t = {
    mode: mode;
    verbose: bool
  } [@@ deriving yojson]

  let instantiate_ext_files cfg = Ok cfg

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename ->
      let open Or_error in
      try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
      match of_yojson raw_json with
      | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
      | Error msg ->
        error_string @@ sprintf "Invalid Qelim Configuration (%s): %s" filename msg

  module type ConfigType = sig val config : t end
end

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))

  let add_prefix_to_tvars prefix bounds fml =
    let subst, bounds_rev =
      List.fold ~init:(Map.Poly.empty, []) bounds
        ~f:(fun (subst, bounds_rev) (tvar, sort) ->
            let new_tvar = Ident.Tvar (prefix ^ Ident.name_of_tvar tvar) in
            Map.Poly.add_exn subst ~key:tvar ~data:(Term.mk_var new_tvar sort),
            (new_tvar, sort) :: bounds_rev)
    in
    List.rev bounds_rev, Formula.subst subst fml

  let mk_app pvar bounds0 bounds ?replacer () =
    Formula.mk_atom @@ Atom.mk_app
      (Predicate.mk_var pvar @@ List.map ~f:snd @@ bounds0 @ bounds) @@
    Term.of_sort_env bounds0
    @ List.map bounds ~f:(fun (tvar, sort) ->
        Term.mk_var tvar sort
        |> match replacer with Some replacer -> replacer tvar | None -> Fn.id)

  let mk_replacer tvar op = fun tvar' term_var ->
    if Stdlib.(tvar' = tvar) then op term_var (T_int.one ()) else term_var

  let encode_exists_mu prefix bounds0 pvars fnpvs exists_formula =
    (* avoid dup *)
    let pvar = Problem.avoid_dup (Ident.Pvar prefix) (pvars @ List.map ~f:fst @@ Set.to_list fnpvs) in
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bounds0 =
      let fv = Formula.tvs_of body in
      List.filter bounds0  ~f:(fun (tvar, _) -> Set.mem fv tvar) in
    let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
    (** Exists(x,y) =mu F(x,y) \/ Exists(x+1,y) \/ Exists(x-1,y) \/ Exists(x,y+1) \/ Exists(x,y-1)*)
    [ Pred.make Predicate.Mu pvar (bounds0 @ bounds) @@
      Formula.or_of @@
      body :: List.fold ~init:[] bounds ~f:(fun res (tvar, _) ->
          mk_app pvar bounds0 bounds ~replacer:(mk_replacer tvar T_int.mk_add) () ::
          mk_app pvar bounds0 bounds ~replacer:(mk_replacer tvar T_int.mk_sub) () ::
          res) ],
    mk_app pvar bounds0 bounds ~replacer:(fun _ _ -> T_int.zero ()) (),
    fnpvs, Map.Poly.empty

  let encode_exists_mu' prefix bounds0 pvars fnpvs exists_formula =
    (* avoid dup *)
    let pvar = Problem.avoid_dup (Ident.Pvar prefix) (pvars @ List.map ~f:fst @@ Set.to_list fnpvs) in
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bounds0 =
      let fv = Formula.tvs_of body in
      List.filter bounds0  ~f:(fun (tvar, _) -> Set.mem fv tvar) in
    let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
    let rec rep body subst res = function
      | [] -> Formula.subst subst body :: res
      | (tvar, sort) :: tail ->
        let subst' =
          Map.Poly.add_exn subst ~key:tvar ~data:(T_int.mk_neg (Term.mk_var tvar sort))
        in
        rep body subst (rep body subst' res tail) tail
    in
    (** Exists(x,y) =mu F(x,y) \/ F(-x,y) \/ F(x,-y) \/ F(-x,-y) \/ Exists(x+1,y) \/ Exists(x,y+1)*)
    [ Pred.make Predicate.Mu pvar (bounds0 @ bounds) @@
      Formula.or_of @@
      rep body Map.Poly.empty [] bounds
      @ List.map bounds ~f:(fun (tvar, _) -> mk_app pvar bounds0 bounds ~replacer:(mk_replacer tvar T_int.mk_add) ()) ],
    mk_app pvar bounds0 bounds ~replacer:(fun _ _ -> T_int.zero ()) (),
    fnpvs, Map.Poly.empty

  let encode_exists_mus prefix bounds0 pvars fnpvs exists_formula =
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bounds0 =
      let fv = Formula.tvs_of body in
      List.filter bounds0 ~f:(fun (tvar, _) -> Set.mem fv tvar) in
    let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
    let rec encode_exists args bounds pvars =
      match bounds with
      | [] -> [], body
      | (tvar, sort) :: tail ->
        (* avoid dup *)
        let tvar_name = Ident.name_of_tvar tvar in
        let pvar1, pvar2 =
          let pvars_fnpvs = pvars @ List.map ~f:fst @@ Set.to_list fnpvs in
          Problem.avoid_dup (Ident.Pvar (prefix ^ "_" ^ tvar_name ^ "_n")) pvars_fnpvs,
          Problem.avoid_dup (Ident.Pvar (prefix ^ "_" ^ tvar_name ^ "_p")) pvars_fnpvs
        in
        (* rec *)
        let args' = (tvar, sort) :: args in
        let add_preds, body = encode_exists args' tail (pvar1 :: pvar2 :: pvars) in
        (* make exists body *)
        let mk_body pvar arg =
          Formula.mk_atom @@ Atom.mk_pvar_app pvar (List.map ~f:snd args')
            (arg :: Term.of_sort_env args)
        in
        let def1 = (* tvar_exists - 1 *)
          Pred.make Predicate.Mu pvar1 args' @@
          Formula.mk_or body (mk_body pvar1 @@ T_int.mk_sub (Term.mk_var tvar sort) (T_int.one ()))
        in
        let def2 = (* tvar_exists + 1 *)
          Pred.make Predicate.Mu pvar2 args' @@
          Formula.mk_or body (mk_body pvar2 @@ T_int.mk_add (Term.mk_var tvar sort) (T_int.one ()))
        in
        (** ExistsLy(x,y) =mu F(x,y) \/ ExistsLy(x,y-1)
            ExistsRy(x,y) =mu F(x,y) \/ ExistsRy(x,y+1)
            ExistsLx(x) =mu ExistsLy(x,0) \/ ExistsRy(x,0) \/ ExistsLx(x-1)
            ExistsRx(x) =mu ExistsLy(x,0) \/ ExistsRy(x,0) \/ ExistsRx(x+1)
        *)
        def1 :: def2 :: add_preds,
        Formula.mk_or (mk_body pvar1 (T_int.zero ())) (mk_body pvar2 (T_int.zero ()))
    in
    let preds, query = encode_exists bounds0 bounds pvars in
    preds, query, fnpvs, Map.Poly.empty

  let encode_exists_nu range prefix bounds0 pvars fnpvs exists_formula =
    (* avoid dup *)
    let pvar = Problem.avoid_dup (Ident.Pvar prefix) (pvars @ List.map ~f:fst @@ Set.to_list fnpvs) in
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bounds0 =
      let fv = Formula.tvs_of body in
      List.filter bounds0 ~f:(fun (tvar, _) -> Set.mem fv tvar) in
    let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
    let rec rep body subst res = function
      | [] -> Formula.subst subst body :: res
      | (tvar, sort) :: tail ->
        let subst' =
          Map.Poly.add_exn subst ~key:tvar ~data:(T_int.mk_neg (Term.mk_var tvar sort))
        in
        rep body subst (rep body subst' res tail) tail
    in
    (* Exists x =nu x >= 0 /\ (F(x) \/ F(-x) \/ Exists(x-1)) *)
    let body =
      Formula.and_of @@
      (* F(x) \/ F(-x) \/ Exists(x-1) *)
      (Formula.or_of
         (* F(x) \/ F(-x) *)
         (rep body Map.Poly.empty [] bounds
          (* Exists(x-1) *)
          @ List.map bounds ~f:(fun (tvar, _) ->
              mk_app pvar bounds0 bounds ~replacer:(mk_replacer tvar T_int.mk_sub) ())))
      (* x >= 0 *)
      :: List.map bounds ~f:(fun (tvar, sort) ->
          Formula.mk_atom (T_int.mk_geq (Term.mk_var tvar sort) (T_int.zero ())))
    in
    [Pred.make Predicate.Nu pvar (bounds0 @ bounds) body],
    (* forall x. x >= range => Exists(x) *)
    Evaluator.simplify @@ Formula.forall bounds @@ Formula.mk_imply
      (* x >= range *)
      (Formula.and_of @@
       List.map bounds ~f:(fun (tvar, sort) ->
           Formula.mk_atom (T_int.mk_geq (Term.mk_var tvar sort) (T_int.mk_int range))))
      (* Exists(x) *)
      (mk_app pvar bounds0 bounds ()),
    fnpvs, Map.Poly.empty

  let encode_exists_skolem_fun prefix bounds0 _pvars fnpvs exists_formula =
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let params =
      let fv = Formula.tvs_of body in
      List.filter bounds ~f:(fun (tvar, _) -> Set.mem fv tvar) in
    let bool_params, arith_params =
      List.partition_tf params ~f:(function (_, T_bool.SBool) -> true | _ -> false)
    in
    let arith_params, body =
      let subst, bounds_rev =
        List.fold ~init:(Map.Poly.empty, []) arith_params
          ~f:(fun (subst, bounds_rev) (tvar, sort) ->
              let new_tvar = (*ToDo:generate fresh id*)
                Ident.Tvar ("#skolem_" ^ prefix ^ Ident.name_of_tvar tvar)
              in
              let sorts = List.map ~f:snd bounds0 @ [sort] in
              let fapp = Term.mk_fvar_app new_tvar sorts (Term.of_sort_env bounds0) in
              Map.Poly.add_exn subst ~key:tvar ~data:fapp,
              (new_tvar, sorts) :: bounds_rev)
      in
      List.rev bounds_rev, Formula.subst subst body
    in
    (*assert (List.length pvars' = List.length arith_params);*)
    let body =
      (* expand existential quantification over boolean variables *)
      let rec aux body = function
        | [] -> body
        | (x, sort) :: xs ->
          assert (Term.is_bool_sort sort);
          let body = aux body xs in
          Formula.or_of [Formula.apply_pred (x, body) @@ T_bool.mk_true ();
                         Formula.apply_pred (x, body) @@ T_bool.mk_false ()]
      in
      aux body bool_params
    in
    [], Evaluator.simplify body,
    fnpvs,
    Map.of_list_exn @@
    List.map arith_params ~f:(fun (x, sorts) ->
        x, Logic.Sort.mk_fun @@ List.map ~f:Logic.ExtTerm.of_old_sort sorts)

  let encode_exists_skolem_pred prefix bounds0 pvars fnpvs exists_formula =
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let params =
      let fv = Formula.tvs_of body in
      List.filter bounds ~f:(fun (tvar, _) -> Set.mem fv tvar) in
    let bool_params, arith_params =
      List.partition_tf params ~f:(function (_, T_bool.SBool) -> true | _ -> false)
    in
    let pvars' = List.fold_right arith_params ~init:[] ~f:(fun (x, _) pvars' ->
        let pv = Ident.fnpred_pvar (Ident.Pvar (prefix ^ Ident.name_of_tvar x)) in
        Problem.avoid_dup pv (pvars' @ pvars @ List.map ~f:fst @@ Set.to_list fnpvs) :: pvars') in
    let arith_params, body = add_prefix_to_tvars "#exists_" arith_params body in
    (*assert (List.length pvars' = List.length arith_params);*)
    let body =
      (* expand existential quantification over boolean variables *)
      let rec aux body = function
        | [] -> body
        | (x, sort) :: xs ->
          assert (Term.is_bool_sort sort);
          let body = aux body xs in
          Formula.or_of [Formula.apply_pred (x, body) @@ T_bool.mk_true ();
                         Formula.apply_pred (x, body) @@ T_bool.mk_false ()]
      in
      aux body bool_params
    in
    [],
    Evaluator.simplify @@ Formula.forall arith_params @@ Formula.mk_imply
      (Formula.and_of
         (List.map2_exn pvars' arith_params ~f:(fun pvar (tvar, sort) ->
              mk_app pvar bounds0 [tvar, sort] ())))
      body,
    List.fold2_exn ~init:fnpvs pvars' arith_params ~f:(fun fnpvs pvar (_, sort) ->
        Set.add fnpvs (pvar, List.map ~f:snd bounds0 @ [sort])),
    Map.Poly.empty

  let dispatched =
    match config.mode with
    | Mu -> encode_exists_mu
    | Mu' -> encode_exists_mu'
    | Mus -> encode_exists_mus
    | Nu range -> encode_exists_nu (Z.of_int range)
    | SkolemFun -> encode_exists_skolem_fun
    | SkolemPred -> encode_exists_skolem_pred

  let encode_exists prefix bounds0 pvars (fnpvs : LogicOld.pred_sort_env_set) fml =
    let rec rep bounds0 pvars fnpvs fml =
      if Formula.is_quantifier_free fml then
        [], fml, pvars, fnpvs, Map.Poly.empty
      else if Formula.is_and fml || Formula.is_or fml then
        let binop, fml1, fml2, info = Formula.let_binop fml in
        let preds1, fml1, pvars, fnpvs, fnsenv1 = rep bounds0 pvars fnpvs fml1 in
        let preds2, fml2, pvars, fnpvs, fnsenv2 = rep bounds0 pvars fnpvs fml2 in
        preds1 @ preds2, Formula.mk_binop binop fml1 fml2 ~info,
        pvars, fnpvs, Map.force_merge fnsenv1 fnsenv2
      else if Formula.is_forall fml then
        let bounds, fml, info = Formula.let_forall fml in
        let preds, fml, pvars, fnpvs, fnsenv = rep (bounds @ bounds0) pvars fnpvs fml in
        preds, Formula.forall bounds fml ~info, pvars, fnpvs, fnsenv
      else if Formula.is_exists fml then
        let bounds, fml, info = Formula.let_exists fml in
        let preds, fml, pvars, fnpvs, fnsenv1 = rep (bounds @ bounds0) pvars fnpvs fml in
        let fml = Formula.exists bounds fml ~info in
        if Formula.is_exists fml then
          let add_preds, fml, fnpvs, fnsenv2 = dispatched prefix bounds0 pvars fnpvs fml in
          add_preds @ preds, fml,
          (Pred.pvars_of_list add_preds @ pvars), fnpvs, Map.force_merge fnsenv1 fnsenv2
        else preds, fml, pvars, fnpvs, fnsenv1
      else failwith (Formula.str_of fml ^ " not supported")
    in
    let preds, fml, _pvars, fnpvs, fnsenv = rep bounds0 pvars fnpvs @@ Formula.nnf_of fml in
    preds, fml, fnpvs, fnsenv

  let elim_exists_in_query muclp fnpvs =
    let preds, query = Problem.let_muclp muclp in
    let pvars = Pred.pvars_of_list preds in
    let add_preds, query', fnpvs, fnsenv =
      let prefix = "query_" in
      encode_exists prefix [] pvars fnpvs query
    in
    Problem.make (add_preds @ preds) query', (fnpvs, fnsenv)
  let elim_exists_in_preds muclp fnpvs =
    let preds, query = Problem.let_muclp muclp in
    let pvars = Pred.pvars_of_list preds in
    let preds', fnpvs, fnsenv =
      List.fold ~init:([], fnpvs, Map.Poly.empty) preds
        ~f:(fun (preds, fnpvs, fnsenv) def ->
            let fix, pvar, bounds, body = Pred.let_ def in
            let add_preds, body', fnpvs', fnsenv' =
              let prefix = Ident.name_of_pvar pvar ^ Ident.divide_flag in
              encode_exists prefix bounds pvars fnpvs body
            in
            add_preds @ Pred.make fix pvar bounds body' :: preds,
            fnpvs', Map.force_merge fnsenv fnsenv')
    in
    Problem.make (List.rev preds') query, (fnpvs, fnsenv)
  let elim_exists muclp fnpvs =
    let muclp, (fnpvs, fnsenv1) = elim_exists_in_query muclp fnpvs in
    let muclp, (fnpvs, fnsenv2) = elim_exists_in_preds muclp fnpvs in
    muclp, (fnpvs, Map.force_merge fnsenv1 fnsenv2)
end