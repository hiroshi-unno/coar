open Core
open Common
open Common.Util
open Ast
open Ast.LogicOld

type mode = Mu | Mu' | Mus | Nu | SkolemFun | SkolemPred [@@ deriving yojson]

module Config = struct
  type t = {
    mode: mode;
    verbose: bool
  } [@@ deriving yojson]

  let instantiate_ext_files cfg = Ok cfg

  let load_ext_file = function
    | ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename)
        >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x ->
          instantiate_ext_files x >>= fun x ->
          Ok (ExtFile.Instance x)
        | Error msg ->
          error_string
          @@ Printf.sprintf
            "Invalid Qelim Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)

  module type ConfigType = sig val config : t end
end

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))

  let add_prefix_to_tvars prefix bounds fml =
    let subst, bounds_rev =
      List.fold ~init:(Core.Map.Poly.empty, []) (SortEnv.list_of bounds)
        ~f:(fun (subst, bounds_rev) (tvar, sort) ->
            let new_tvar = Ident.Tvar (prefix ^ Ident.name_of_tvar tvar) in
            Core.Map.Poly.add_exn subst ~key:tvar ~data:(Term.mk_var new_tvar sort),
            (new_tvar, sort) :: bounds_rev)
    in
    SortEnv.of_list (List.rev bounds_rev), Formula.subst subst fml

  let mk_app pvar bounds_for_fv bounds ?replacer () =
    Formula.mk_atom
      (Atom.mk_app (Predicate.mk_var pvar @@ SortEnv.sorts_of (SortEnv.append bounds_for_fv bounds))
         (Term.of_sort_env bounds_for_fv
          @ (SortEnv.map bounds ~f:(fun (tvar, sort) ->
              let term_var = Term.mk_var tvar sort in
              match replacer with Some replacer -> replacer tvar term_var | None -> term_var))))

  let mk_replacer tvar op =
    fun tvar' term_var -> if Stdlib.(=) tvar' tvar then op term_var (T_int.one ())else term_var

  let mk_exists_funs_mu funname_cand bounds_for_fv pvars exists_formula fnpvs =
    (* avoid dup *)
    let pvar = Problem.avoid_dup (Ident.Pvar funname_cand) (pvars @ List.map ~f:fst @@ Set.Poly.to_list fnpvs) in
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bounds_for_fv =
      let fv = Formula.tvs_of body in
      SortEnv.filter bounds_for_fv  ~f:(fun (tvar, _) -> Set.Poly.mem fv tvar) in
    let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
    let body =
      Formula.or_of @@
      body :: List.fold ~init:[] (SortEnv.list_of bounds) ~f:(fun res (tvar, _) ->
          mk_app pvar bounds_for_fv bounds ~replacer:(mk_replacer tvar T_int.mk_add) () ::
          mk_app pvar bounds_for_fv bounds ~replacer:(mk_replacer tvar T_int.mk_sub) () ::
          res)
    in
    (** Exists(x,y) =mu F(x,y) \/ Exists(x+1,y) \/ Exists(x-1,y) \/ Exists(x,y+1) \/ Exists(x,y-1)*)
    [Problem.mk_func Predicate.Mu pvar (SortEnv.append bounds_for_fv bounds) body],
    mk_app pvar bounds_for_fv bounds ~replacer:(fun _ _ -> T_int.zero ()) (),
    fnpvs, Logic.SortMap.empty

  let mk_exists_funs_mu' funname_cand bounds_for_fv pvars exists_formula fnpvs =
    (* avoid dup *)
    let pvar = Problem.avoid_dup (Ident.Pvar funname_cand) (pvars @ List.map ~f:fst @@ Set.Poly.to_list fnpvs) in
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bounds_for_fv =
      let fv = Formula.tvs_of body in
      SortEnv.filter bounds_for_fv  ~f:(fun (tvar, _) -> Set.Poly.mem fv tvar) in
    let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
    let rec rep body subst res = function
      | [] -> Formula.subst subst body :: res
      | (tvar, sort) :: tail ->
        let subst' =
          Core.Map.Poly.add_exn subst ~key:tvar ~data:(T_int.mk_neg (Term.mk_var tvar sort))
        in
        rep body subst (rep body subst' res tail) tail
    in
    let body =
      Formula.or_of (rep body Core.Map.Poly.empty [] (SortEnv.list_of bounds)
                     @ (SortEnv.map bounds ~f:(fun (tvar, _) -> mk_app pvar bounds_for_fv bounds ~replacer:(mk_replacer tvar T_int.mk_add) ())))
    in
    (** Exists(x,y) =mu F(x,y) \/ F(-x,y) \/ F(x,-y) \/ F(x,-y) \/ Exists(x+1,y) \/ Exists(x,y+1)*)
    [Problem.mk_func Predicate.Mu pvar (SortEnv.append bounds_for_fv bounds) body],
    mk_app pvar bounds_for_fv bounds ~replacer:(fun _ _ -> T_int.zero ()) (),
    fnpvs, Logic.SortMap.empty

  let mk_exists_funs_mus funname_cand bounds_for_fv pvars exists_formula fnpvs =
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bounds_for_fv =
      let fv = Formula.tvs_of body in
      SortEnv.filter bounds_for_fv ~f:(fun (tvar, _) -> Set.Poly.mem fv tvar) in
    let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
    let rec mk_exists_funs bounds_for_fv bounds pvars fnpvs =
      match bounds with
      | [] -> [], body, fnpvs
      | (tvar, sort) :: tail ->
        (* avoid dup *)
        let tvar_name = Ident.name_of_tvar tvar in
        let pvars_fnpvs = pvars @ List.map ~f:fst @@ Set.Poly.to_list fnpvs in
        let pvar_left = Problem.avoid_dup (Ident.Pvar (funname_cand ^ "_" ^ tvar_name ^ "_n")) pvars_fnpvs in
        let pvar_right = Problem.avoid_dup (Ident.Pvar (funname_cand ^ "_" ^ tvar_name ^ "_p")) pvars_fnpvs in
        (* rec *)
        let args = SortEnv.append (SortEnv.singleton tvar sort) bounds_for_fv in
        let funcs, body, _ = mk_exists_funs args tail (pvar_left :: pvar_right :: pvars) fnpvs in
        (* make exists body *)
        let mk_body pvar arg =
          Formula.mk_atom
            (Atom.mk_app (Predicate.mk_var pvar @@ SortEnv.sorts_of (SortEnv.append bounds_for_fv (SortEnv.of_list bounds)))
               (arg :: Term.of_sort_env bounds_for_fv))
        in
        let term_var = Term.mk_var tvar sort in
        let zero = T_int.zero () in
        let one = T_int.one () in
        (* tvar_exists - 1 *)
        let body_left = Formula.mk_or body (mk_body pvar_left @@ T_int.mk_sub term_var one) in
        (* tvar_exists + 1 *)
        let body_right = Formula.mk_or body (mk_body pvar_right @@ T_int.mk_add term_var one) in
        (** ExistsLy(x,y) =mu F(x,y) \/ ExistsLy(x,y-1)
            ExistsRy(x,y) =mu F(x,y) \/ ExistsRy(x,y+1)
            ExistsLx(x,y) =mu ExistsLy(x,y) \/ ExistsRy(x,y) \/ ExistsLx(x-1,y)
            ExistsRx(x,y) =mu ExistsLy(x,y) \/ ExistsRy(x,y) \/ ExistsRx(x+1,y)
        *)
        Problem.mk_func Predicate.Mu pvar_left args body_left
        :: Problem.mk_func Predicate.Mu pvar_right args body_right
        :: funcs,
        Formula.mk_or (mk_body pvar_left zero) (mk_body pvar_right zero),
        fnpvs
    in
    let funcs, entry, fnpvs = mk_exists_funs bounds_for_fv (SortEnv.list_of bounds) pvars fnpvs in
    funcs, entry, fnpvs, Logic.SortMap.empty

  let mk_exists_funs_nu range funname_cand bounds_for_fv pvars exists_formula fnpvs =
    (* avoid dup *)
    let pvar = Problem.avoid_dup (Ident.Pvar funname_cand) (pvars @ List.map ~f:fst @@ Set.Poly.to_list fnpvs) in
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let bounds_for_fv =
      let fv = Formula.tvs_of body in
      SortEnv.filter bounds_for_fv  ~f:(fun (tvar, _) -> Set.Poly.mem fv tvar) in
    let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
    let rec rep body subst res = function
      | [] -> Formula.subst subst body :: res
      | (tvar, sort) :: tail ->
        let subst' =
          Core.Map.Poly.add_exn subst ~key:tvar ~data:(T_int.mk_neg (Term.mk_var tvar sort))
        in
        rep body subst (rep body subst' res tail) tail
    in
    (* Exists x =nu x >= 0 /\ (F(x) \/ F(-x) \/ Exists(x-1)) *)
    let body =
      Formula.and_of
        (* F(x) \/ F(-x) \/ Exists(x-1) *)
        ((Formula.or_of
            (* F(x) \/ F(-x) *)
            (rep body Core.Map.Poly.empty [] (SortEnv.list_of bounds)
             (* Exists(x-1) *)
             @ (SortEnv.map bounds ~f:(fun (tvar, _) ->
                 mk_app pvar bounds_for_fv bounds ~replacer:(mk_replacer tvar T_int.mk_sub) ()))))
         (* x >= 0 *)
         :: SortEnv.map bounds ~f:(fun (tvar, sort) ->
             Formula.mk_atom (T_int.mk_geq (Term.mk_var tvar sort) (T_int.zero ()))))
    in
    (* forall x. x >= range => Exists(x) *)
    let entry =
      Evaluator.simplify
      @@ Formula.forall bounds
        (Formula.mk_imply
           (* x >= range *)
           (Formula.and_of
              (SortEnv.map bounds ~f:(fun (tvar, sort) ->
                   Formula.mk_atom (T_int.mk_geq (Term.mk_var tvar sort) (T_int.mk_int range)))))
           (* Exists(x) *)
           (mk_app pvar bounds_for_fv bounds ()))
    in
    [Problem.mk_func Predicate.Nu pvar (SortEnv.append bounds_for_fv bounds) body], entry, fnpvs, Logic.SortMap.empty

  let skolemize prefix args bounds fml =
    let subst, bounds_rev =
      List.fold ~init:(Core.Map.Poly.empty, []) (SortEnv.list_of bounds)
        ~f:(fun (subst, bounds_rev) (tvar, sort) ->
            let new_tvar = Ident.Tvar (prefix (*ToDo:generate fresh id*) tvar) in
            Core.Map.Poly.add_exn subst
              ~key:tvar
              ~data:(Term.mk_fvar_app new_tvar (SortEnv.sorts_of args @ [sort])
                       (Term.of_sort_env args)),
            (new_tvar, SortEnv.sorts_of args @ [sort]) :: bounds_rev)
    in
    List.rev bounds_rev, Formula.subst subst fml
  let mk_exists_funs_skolem_fun funname_cand bounds_for_fv _pvars exists_formula fnpvs =
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let params =
      let fv = Formula.tvs_of body in
      SortEnv.filter bounds ~f:(fun (tvar, _) -> Set.Poly.mem fv tvar) in
    let bool_params, arith_params =
      SortEnv.partition_tf params ~f:(function (_, T_bool.SBool) -> true | _ -> false)
    in
    let arith_params, body =
      skolemize (fun x -> "#skolem_" ^ funname_cand ^ Ident.name_of_tvar x)
        bounds_for_fv
        arith_params body in
    (*assert (Stdlib.(=) (List.length pvars') (List.length arith_params));*)
    let body =
      (* expand existential quantification over boolean variables *)
      let rec aux body = function
        | [] -> body
        | (x, sort) :: xs ->
          assert (Stdlib.(=) sort T_bool.SBool);
          let body = aux body xs in
          Formula.or_of [Formula.subst (Map.Poly.singleton x (T_bool.of_atom (Atom.mk_true ()))) body;
                         Formula.subst (Map.Poly.singleton x (T_bool.of_atom (Atom.mk_false ()))) body]
      in
      aux body (SortEnv.list_of bool_params)
    in
    [], Evaluator.simplify body,
    fnpvs,
    Logic.SortMap.of_set @@ Set.Poly.of_list @@ List.map arith_params ~f:(fun (x, sorts) -> (x, Logic.Sort.mk_fun (List.map ~f:Logic.ExtTerm.of_old_sort sorts)))

  let mk_exists_funs_skolem_pred funname_cand bounds_for_fv pvars exists_formula fnpvs =
    (* make exists body *)
    let bounds, body, _ = Formula.let_exists exists_formula in
    let params =
      let fv = Formula.tvs_of body in
      SortEnv.filter bounds ~f:(fun (tvar, _) -> Set.Poly.mem fv tvar) in
    let bool_params, arith_params =
      SortEnv.partition_tf params ~f:(function (_, T_bool.SBool) -> true | _ -> false)
    in
    let pvars' = List.fold_right (SortEnv.list_of arith_params) ~init:[] ~f:(fun (x, _) pvars' ->
        let name = "FN_" ^ funname_cand ^ Ident.name_of_tvar x in
        Problem.avoid_dup (Ident.Pvar name) (pvars' @ pvars @ List.map ~f:fst @@ Set.Poly.to_list fnpvs) :: pvars') in
    let arith_params, body = add_prefix_to_tvars "#exists_" arith_params body in
    (*assert (Stdlib.(=) (List.length pvars') (List.length arith_params));*)
    let body =
      (* expand existential quantification over boolean variables *)
      let rec aux body = function
        | [] -> body
        | (x, sort) :: xs ->
          assert (Stdlib.(=) sort T_bool.SBool);
          let body = aux body xs in
          Formula.or_of [Formula.subst (Map.Poly.singleton x (T_bool.of_atom (Atom.mk_true ()))) body;
                         Formula.subst (Map.Poly.singleton x (T_bool.of_atom (Atom.mk_false ()))) body]
      in
      aux body (SortEnv.list_of bool_params)
    in
    let entry =
      Evaluator.simplify
      @@ Formula.forall arith_params
        (Formula.mk_imply
           (Formula.and_of
              (List.map2_exn pvars' (SortEnv.list_of arith_params) ~f:(fun pvar (tvar, sort) ->
                   mk_app pvar bounds_for_fv (SortEnv.singleton tvar sort) ())))
           body)
    in
    [], entry,
    List.fold2_exn ~init:fnpvs pvars' (SortEnv.list_of arith_params) ~f:(fun fnpvs pvar (_, sort) ->
        Set.Poly.add fnpvs (pvar, SortEnv.sorts_of bounds_for_fv @ [sort])),
    Logic.SortMap.empty

  let mk_exists_funs ?(range=100) funname_cand bounds_for_fv pvars fml fnpvs =
    let dispatched =
      match config.mode with
      | Mu -> mk_exists_funs_mu
      | Mu' -> mk_exists_funs_mu'
      | Mus -> mk_exists_funs_mus
      | Nu -> mk_exists_funs_nu (Z.of_int range)
      | SkolemFun -> mk_exists_funs_skolem_fun
      | SkolemPred -> mk_exists_funs_skolem_pred
    in
    let rec add_pvars pvars = function
      | [] -> pvars
      | func :: tail -> let pvar = Problem.get_pvar_of_function func in add_pvars (pvar :: pvars) tail
    in
    let rec rep pvars bounds_for_fv fml fnpvs =
      if Formula.is_atom fml then
        [], fml, pvars, fnpvs, Logic.SortMap.empty
      else if Formula.is_and fml || Formula.is_or fml then
        let binop, fml_left, fml_right, info = Formula.let_binop fml in
        let funcs_left, fml_left, pvars, fnpvs, fnsenv1 = rep pvars bounds_for_fv fml_left fnpvs in
        let funcs_right, fml_right, pvars, fnpvs, fnsenv2 = rep pvars bounds_for_fv fml_right fnpvs in
        funcs_left @ funcs_right, Formula.mk_binop binop fml_left fml_right ~info, pvars, fnpvs, Logic.SortMap.merge fnsenv1 fnsenv2
      else if Formula.is_forall fml then
        let bounds, fml, info = Formula.let_forall fml in
        let funcs, fml, pvars, fnpvs, fnsenv = rep pvars (SortEnv.append bounds bounds_for_fv) fml fnpvs in
        funcs, Formula.forall bounds fml ~info, pvars, fnpvs, fnsenv
      else if Formula.is_exists fml then
        let bounds, fml, info = Formula.let_exists fml in
        let funcs, fml, pvars, fnpvs, fnsenv1 = rep pvars (SortEnv.append bounds bounds_for_fv) fml fnpvs in
        let fml = Formula.exists bounds fml ~info in
        let funcs', fml, fnpvs, fnsenv2 = dispatched funname_cand bounds_for_fv pvars fml fnpvs in
        funcs' @ funcs, fml, add_pvars pvars funcs', fnpvs, Logic.SortMap.merge fnsenv1 fnsenv2
      else failwith (Formula.str_of fml ^ " not supported")
    in
    let funcs, fml, _, fnpvs, fnsenv = rep pvars bounds_for_fv fml fnpvs in
    funcs, fml, fnpvs, fnsenv

  (*val encode_top_exists: ?range:int -> Problem.t -> Problem.t*)
  let encode_top_exists ?range muclp fnpvs =
    let funcs, entry = Problem.let_muclp muclp in
    let pvars = List.map funcs ~f:Problem.get_pvar_of_function in
    let funcs', caller, fnpvs, fnsenv = mk_exists_funs ?range ("query_") SortEnv.empty pvars entry fnpvs in
    Problem.make (funcs' @ funcs) caller, fnpvs, fnsenv

  (*val encode_body_exists: ?range:int -> Problem.t -> Problem.t*)
  let encode_body_exists ?range muclp fnpvs =
    let funcs, entry = Problem.let_muclp muclp in
    let pvars = List.map funcs ~f:Problem.get_pvar_of_function in
    let funcs, _, fnpvs, fnsenv =
      List.fold ~init:([], pvars, fnpvs, Logic.SortMap.empty) funcs
        ~f:(fun (funcs, pvars, fnpvs, fnsenv) func ->
            let fix, pvar, bounds, body = Problem.let_function func in
            let funcs', caller, fnpvs', fnsenv' = mk_exists_funs ?range (Ident.name_of_pvar pvar ^ "_") bounds pvars body fnpvs in
            let func = Problem.mk_func fix pvar bounds caller in
            funcs' @ func :: funcs, pvars, fnpvs', Logic.SortMap.merge fnsenv fnsenv')
    in
    let funcs = List.rev funcs in
    Problem.make funcs entry, fnpvs, fnsenv
end