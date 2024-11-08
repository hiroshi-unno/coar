open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld

type mode =
  | Mu
  | Mu'
  | Mus
  | Nu (* sound but incomplete *) of int (* range *)
  | SkolemFun
  | SkolemPred
[@@deriving yojson]

module Config = struct
  type t = { mode : mode; verbose : bool } [@@deriving yojson]

  let instantiate_ext_files cfg = Ok cfg

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid Qelim Configuration (%s): %s" filename msg)

  module type ConfigType = sig
    val config : t
  end
end

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let add_prefix_to_tvars prefix bounds fml =
    let subst, bounds_rev =
      List.fold ~init:(Map.Poly.empty, []) bounds
        ~f:(fun (subst, bounds_rev) (tvar, sort) ->
          let new_tvar = Ident.Tvar (prefix ^ Ident.name_of_tvar tvar) in
          ( Map.Poly.add_exn subst ~key:tvar ~data:(Term.mk_var new_tvar sort),
            (new_tvar, sort) :: bounds_rev ))
    in
    (List.rev bounds_rev, Formula.subst subst fml)

  let mk_app pvar bounds0 bounds ?replacer () =
    Formula.mk_atom
    @@ Atom.mk_pvar_app pvar (List.map ~f:snd @@ bounds0 @ bounds)
    @@ Term.of_sort_env bounds0
    @ List.map bounds ~f:(fun (tvar, sort) ->
          Term.mk_var tvar sort
          |>
          match replacer with Some replacer -> replacer tvar | None -> Fn.id)

  let mk_replacer tvar op tvar' term_var =
    if Stdlib.(tvar' = tvar) then op term_var (T_int.one ()) else term_var

  let encode_exists_mu prefix bound_tvars bound_pvars unknowns exists_formula =
    (* avoid dup *)
    let pvar =
      Problem.avoid_dup (Ident.Pvar prefix)
        (bound_pvars @ Set.to_list @@ Kind.pvars_of unknowns)
    in
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bound_tvars =
      let fv = Formula.tvs_of body in
      List.filter bound_tvars ~f:(fst >> Set.mem fv)
    in
    let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
    (* Exists(x,y) =mu F(x,y) \/ Exists(x+1,y) \/ Exists(x-1,y) \/ Exists(x,y+1) \/ Exists(x,y-1) *)
    ( [
        Pred.make Predicate.Mu pvar (bound_tvars @ bounds)
        @@ Formula.or_of
        @@ body
           :: List.fold ~init:[] bounds ~f:(fun res (tvar, _) ->
                  mk_app pvar bound_tvars bounds
                    ~replacer:(mk_replacer tvar T_int.mk_add)
                    ()
                  :: mk_app pvar bound_tvars bounds
                       ~replacer:(mk_replacer tvar T_int.mk_sub)
                       ()
                  :: res);
      ],
      mk_app pvar bound_tvars bounds ~replacer:(fun _ _ -> T_int.zero ()) (),
      unknowns )

  let encode_exists_mu' prefix bound_tvars bound_pvars unknowns exists_formula =
    (* avoid dup *)
    let pvar =
      Problem.avoid_dup (Ident.Pvar prefix)
        (bound_pvars @ Set.to_list @@ Kind.pvars_of unknowns)
    in
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bound_tvars =
      let fv = Formula.tvs_of body in
      List.filter bound_tvars ~f:(fst >> Set.mem fv)
    in
    let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
    let rec rep body subst res = function
      | [] -> Formula.subst subst body :: res
      | (tvar, sort) :: tail ->
          let subst' =
            Map.Poly.add_exn subst ~key:tvar
              ~data:(T_int.mk_neg (Term.mk_var tvar sort))
          in
          rep body subst (rep body subst' res tail) tail
    in
    (* Exists(x,y) =mu F(x,y) \/ F(-x,y) \/ F(x,-y) \/ F(-x,-y) \/ Exists(x+1,y) \/ Exists(x,y+1)*)
    ( [
        Pred.make Predicate.Mu pvar (bound_tvars @ bounds)
        @@ Formula.or_of
        @@ rep body Map.Poly.empty [] bounds
        @ List.map bounds ~f:(fun (tvar, _) ->
              mk_app pvar bound_tvars bounds
                ~replacer:(mk_replacer tvar T_int.mk_add)
                ());
      ],
      mk_app pvar bound_tvars bounds ~replacer:(fun _ _ -> T_int.zero ()) (),
      unknowns )

  let encode_exists_mus prefix bound_tvars bound_pvars unknowns exists_formula =
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bound_tvars =
      let fv = Formula.tvs_of body in
      List.filter bound_tvars ~f:(fst >> Set.mem fv)
    in
    let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
    let rec encode_exists args bounds bound_pvars =
      match bounds with
      | [] -> ([], body)
      | (tvar, sort) :: tail ->
          (* avoid dup *)
          let tvar_name = Ident.name_of_tvar tvar in
          let pvar1, pvar2 =
            let bound_pvars' =
              bound_pvars @ Set.to_list @@ Kind.pvars_of unknowns
            in
            ( Problem.avoid_dup
                (Ident.Pvar (prefix ^ "_" ^ tvar_name ^ "_n"))
                bound_pvars',
              Problem.avoid_dup
                (Ident.Pvar (prefix ^ "_" ^ tvar_name ^ "_p"))
                bound_pvars' )
          in
          (* rec *)
          let args' = (tvar, sort) :: args in
          let add_preds, body =
            encode_exists args' tail (pvar1 :: pvar2 :: bound_pvars)
          in
          (* make exists body *)
          let mk_body pvar arg =
            Formula.mk_atom
            @@ Atom.mk_pvar_app pvar (List.map ~f:snd args')
                 (arg :: Term.of_sort_env args)
          in
          let def1 =
            (* tvar_exists - 1 *)
            Pred.make Predicate.Mu pvar1 args'
            @@ Formula.mk_or body
                 (mk_body pvar1
                 @@ T_int.mk_sub (Term.mk_var tvar sort) (T_int.one ()))
          in
          let def2 =
            (* tvar_exists + 1 *)
            Pred.make Predicate.Mu pvar2 args'
            @@ Formula.mk_or body
                 (mk_body pvar2
                 @@ T_int.mk_add (Term.mk_var tvar sort) (T_int.one ()))
          in
          (* ExistsLy(x,y) =mu F(x,y) \/ ExistsLy(x,y-1)
             ExistsRy(x,y) =mu F(x,y) \/ ExistsRy(x,y+1)
             ExistsLx(x) =mu ExistsLy(x,0) \/ ExistsRy(x,0) \/ ExistsLx(x-1)
             ExistsRx(x) =mu ExistsLy(x,0) \/ ExistsRy(x,0) \/ ExistsRx(x+1)
          *)
          ( def1 :: def2 :: add_preds,
            Formula.mk_or
              (mk_body pvar1 (T_int.zero ()))
              (mk_body pvar2 (T_int.zero ())) )
    in
    let preds, query = encode_exists bound_tvars bounds bound_pvars in
    (preds, query, unknowns)

  let encode_exists_nu range prefix bound_tvars bound_pvars unknowns
      exists_formula =
    (* avoid dup *)
    let pvar =
      Problem.avoid_dup (Ident.Pvar prefix)
        (bound_pvars @ Set.to_list @@ Kind.pvars_of unknowns)
    in
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bound_tvars =
      let fv = Formula.tvs_of body in
      List.filter bound_tvars ~f:(fst >> Set.mem fv)
    in
    let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
    let rec rep body subst res = function
      | [] -> Formula.subst subst body :: res
      | (tvar, sort) :: tail ->
          let subst' =
            Map.Poly.add_exn subst ~key:tvar
              ~data:(T_int.mk_neg (Term.mk_var tvar sort))
          in
          rep body subst (rep body subst' res tail) tail
    in
    (* Exists x =nu x >= 0 /\ (F(x) \/ F(-x) \/ Exists(x-1)) *)
    let body =
      Formula.and_of
      @@ (* F(x) \/ F(-x) \/ Exists(x-1) *)
      Formula.or_of
        (* F(x) \/ F(-x) *)
        (rep body Map.Poly.empty [] bounds
        (* Exists(x-1) *)
        @ List.map bounds ~f:(fun (tvar, _) ->
              mk_app pvar bound_tvars bounds
                ~replacer:(mk_replacer tvar T_int.mk_sub)
                ()))
      (* x >= 0 *)
      :: List.map bounds ~f:(fun (tvar, sort) ->
             Formula.mk_atom
               (T_int.mk_geq (Term.mk_var tvar sort) (T_int.zero ())))
    in
    ( [ Pred.make Predicate.Nu pvar (bound_tvars @ bounds) body ],
      (* forall x. x >= range => Exists(x) *)
      Evaluator.simplify @@ Formula.forall bounds
      @@ Formula.mk_imply
           (* x >= range *)
           (Formula.and_of
           @@ List.map bounds ~f:(fun (tvar, sort) ->
                  Formula.mk_atom
                    (T_int.mk_geq (Term.mk_var tvar sort) (T_int.mk_int range)))
           )
           (* Exists(x) *)
           (mk_app pvar bound_tvars bounds ()),
      unknowns )

  let encode_exists_skolem_fun prefix bound_tvars _bound_pvars unknowns
      exists_formula =
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bool_params, arith_params =
      let fv = Formula.tvs_of body in
      List.filter bounds ~f:(fst >> Set.mem fv)
      |> List.partition_tf ~f:(snd >> Term.is_bool_sort)
    in
    let arith_params, body =
      let subst, bounds_rev =
        List.fold ~init:(Map.Poly.empty, []) arith_params
          ~f:(fun (subst, bounds_rev) (tvar, sort) ->
            let new_tvar =
              (*ToDo:generate fresh id*)
              Ident.Tvar ("#skolem_" ^ prefix ^ Ident.name_of_tvar tvar)
            in
            let sorts = List.map ~f:snd bound_tvars @ [ sort ] in
            let fapp =
              Term.mk_fvar_app new_tvar sorts (Term.of_sort_env bound_tvars)
            in
            ( Map.Poly.add_exn subst ~key:tvar ~data:fapp,
              (new_tvar, sorts) :: bounds_rev ))
      in
      (List.rev bounds_rev, Formula.subst subst body)
    in
    (*assert (List.length pvars' = List.length arith_params);*)
    let body =
      (* expand existential quantification over boolean variables *)
      let rec aux body = function
        | [] -> body
        | (x, sort) :: xs ->
            assert (Term.is_bool_sort sort);
            let body = aux body xs in
            Formula.or_of
              [
                Formula.apply_pred (x, body) @@ T_bool.mk_true ();
                Formula.apply_pred (x, body) @@ T_bool.mk_false ();
              ]
      in
      aux body bool_params
    in
    ( [],
      Evaluator.simplify body,
      Kind.add_funs unknowns Kind.IntFun
      @@ Map.of_list_exn
      @@ List.map arith_params ~f:(fun (x, sorts) ->
             ( x,
               Logic.Sort.mk_fun @@ List.map ~f:Logic.ExtTerm.of_old_sort sorts
             )) )

  let encode_exists_skolem_pred prefix bound_tvars bound_pvars unknowns
      exists_formula =
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bool_params, arith_params =
      let fv = Formula.tvs_of body in
      List.filter bounds ~f:(fst >> Set.mem fv)
      |> List.partition_tf ~f:(snd >> Term.is_bool_sort)
    in
    let pvars' =
      List.fold_right arith_params ~init:[] ~f:(fun (x, _) pvars' ->
          let pv =
            Ident.fnpred_pvar (Ident.Pvar (prefix ^ Ident.name_of_tvar x))
          in
          Problem.avoid_dup pv
            (pvars' @ bound_pvars @ Set.to_list @@ Kind.pvars_of unknowns)
          :: pvars')
    in
    let arith_params, body = add_prefix_to_tvars "#exists_" arith_params body in
    (*assert (List.length pvars' = List.length arith_params);*)
    let body =
      (* expand existential quantification over boolean variables *)
      let rec aux body = function
        | [] -> body
        | (x, sort) :: xs ->
            assert (Term.is_bool_sort sort);
            let body = aux body xs in
            Formula.or_of
              [
                Formula.apply_pred (x, body) @@ T_bool.mk_true ();
                Formula.apply_pred (x, body) @@ T_bool.mk_false ();
              ]
      in
      aux body bool_params
    in
    ( [],
      Evaluator.simplify
      @@ Formula.forall arith_params
      @@ Formula.mk_imply
           (Formula.and_of
              (List.map2_exn pvars' arith_params ~f:(fun pvar (tvar, sort) ->
                   mk_app pvar bound_tvars [ (tvar, sort) ] ())))
           body,
      Kind.add_pred_env_set unknowns Kind.FN
      @@ Set.Poly.of_list
      @@ List.map2_exn pvars' arith_params ~f:(fun pvar (_, sort) ->
             (pvar, List.map ~f:snd bound_tvars @ [ sort ])) )

  let dispatched =
    match config.mode with
    | Mu -> encode_exists_mu
    | Mu' -> encode_exists_mu'
    | Mus -> encode_exists_mus
    | Nu range -> encode_exists_nu (Z.of_int range)
    | SkolemFun -> encode_exists_skolem_fun
    | SkolemPred -> encode_exists_skolem_pred

  let encode_exists ?(forall_dom = false) prefix bound_tvars bound_pvars
      unknowns fml =
    let rec rep bound_tvars bound_pvars unknowns fml =
      if Formula.is_quantifier_free fml then ([], fml, bound_pvars, unknowns)
      else if Formula.is_and fml || Formula.is_or fml then
        let binop, fml1, fml2, info = Formula.let_binop fml in
        let preds1, fml1, bound_pvars, unknowns =
          rep bound_tvars bound_pvars unknowns fml1
        in
        let preds2, fml2, bound_pvars, unknowns =
          rep bound_tvars bound_pvars unknowns fml2
        in
        ( preds1 @ preds2,
          Formula.mk_binop binop fml1 fml2 ~info,
          bound_pvars,
          unknowns )
      else if Formula.is_forall fml then
        let bounds, fml, info = Formula.let_forall fml in
        let preds, fml, bound_pvars, unknowns =
          rep (bounds @ bound_tvars) bound_pvars unknowns fml
        in
        let fml' = Formula.forall bounds fml ~info in
        if forall_dom && Formula.is_forall fml' then
          let fml, unknowns =
            let body = fml in
            let bool_params, arith_params =
              let fv = Formula.tvs_of body in
              List.filter bounds ~f:(fst >> Set.mem fv)
              |> List.partition_tf ~f:(snd >> Term.is_bool_sort)
            in
            let pvars' =
              List.fold_right arith_params ~init:[] ~f:(fun (x, _) pvars' ->
                  let pv =
                    Ident.fnpred_pvar
                      (Ident.Pvar (prefix ^ Ident.name_of_tvar x))
                  in
                  Problem.avoid_dup pv
                    (pvars' @ bound_pvars @ Set.to_list
                   @@ Kind.pvars_of unknowns)
                  :: pvars')
            in
            let arith_params, body =
              add_prefix_to_tvars "#foralls_" arith_params body
            in
            (*assert (List.length pvars' = List.length arith_params);*)
            let body =
              (* expand universal quantification over boolean variables *)
              let rec aux body = function
                | [] -> body
                | (x, sort) :: xs ->
                    assert (Term.is_bool_sort sort);
                    let body = aux body xs in
                    Formula.and_of
                      [
                        Formula.apply_pred (x, body) @@ T_bool.mk_true ();
                        Formula.apply_pred (x, body) @@ T_bool.mk_false ();
                      ]
              in
              aux body bool_params
            in
            ( Evaluator.simplify
              @@ Formula.forall arith_params
              @@ Formula.or_of
                   (List.map2_exn pvars' arith_params
                      ~f:(fun pvar (tvar, sort) ->
                        mk_app pvar bound_tvars [ (tvar, sort) ] ())
                   @ [ body ]),
              Kind.add_pred_env_set unknowns Kind.Ord
              @@ Set.Poly.of_list
              @@ List.map2_exn pvars' arith_params ~f:(fun pvar (_, sort) ->
                     (pvar, List.map ~f:snd bound_tvars @ [ sort ])) )
          in
          (preds, fml, bound_pvars, unknowns)
        else (preds, fml', bound_pvars, unknowns)
      else if Formula.is_exists fml then
        let bounds, fml, info = Formula.let_exists fml in
        let preds, fml, bound_pvars, unknowns =
          rep (bounds @ bound_tvars) bound_pvars unknowns fml
        in
        let fml = Formula.exists bounds fml ~info in
        if Formula.is_exists fml then
          let add_preds, fml, unknowns =
            dispatched prefix bound_tvars bound_pvars unknowns fml
          in
          ( add_preds @ preds,
            fml,
            Pred.pvars_of_list add_preds @ bound_pvars,
            unknowns )
        else (preds, fml, bound_pvars, unknowns)
      else failwith (sprintf "[encode_exists] %s not supported" (Formula.str_of fml))
    in
    let preds, fml, _pvars, unknowns =
      rep bound_tvars bound_pvars unknowns @@ Formula.nnf_of fml
    in
    (preds, fml, unknowns)

  let elim_exists_in_query ?(forall_dom = false) (muclp, unknowns) =
    let preds, query = Problem.let_muclp muclp in
    let bound_pvars = Pred.pvars_of_list preds in
    let add_preds, query', unknowns =
      let prefix = "query_" in
      encode_exists ~forall_dom prefix [] bound_pvars unknowns query
    in
    (Problem.make (add_preds @ preds) query', unknowns)

  let elim_exists_in_preds ?(forall_dom = false) (muclp, unknowns) =
    let preds, query = Problem.let_muclp muclp in
    let bound_pvars = Pred.pvars_of_list preds in
    let preds', unknowns =
      List.fold ~init:([], unknowns) preds ~f:(fun (preds, unknowns) def ->
          let fix, pvar, bounds, body = Pred.let_ def in
          let add_preds, body', unknowns =
            let prefix = Ident.name_of_pvar pvar ^ Ident.divide_flag in
            encode_exists ~forall_dom prefix bounds bound_pvars unknowns body
          in
          (add_preds @ (Pred.make fix pvar bounds body' :: preds), unknowns))
    in
    (Problem.make (List.rev preds') query, unknowns)

  let elim_exists ?(forall_dom = false) =
    elim_exists_in_query ~forall_dom >> elim_exists_in_preds ~forall_dom
end
