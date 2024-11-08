open Core
open Common.Ext
open Common.Combinator
open Logic

type t = sort_env_map (*parameters*) * pred_subst_set

type tag =
  | Total of bool
  (* with sample*)
  | Partial of Ident.tvar

let make cand : t =
  ( Map.Poly.empty,
    Set.Poly.map (Map.to_set cand) ~f:(fun (tvar, (sort, phi)) ->
        ((tvar, sort), phi)) )

let of_old_bind (Ident.Pvar n, (args, phi)) =
  let args_new = of_old_sort_env_list args in
  let sort = Sort.mk_fun @@ List.map args_new ~f:snd @ [ ExtTerm.SBool ] in
  ((Ident.Tvar n, sort), Term.mk_lambda args_new @@ ExtTerm.of_old_formula phi)

let of_old ((params_senv, cand) : CandSolOld.t) : t =
  (of_old_sort_env_map params_senv, Set.Poly.map cand ~f:of_old_bind)

let of_subst params_senv theta : t =
  ( params_senv,
    Set.Poly.of_list
    @@ List.map ~f:(fun (var, term) ->
           ((var, Map.Poly.find_exn params_senv var), term))
    @@ Map.Poly.to_alist theta )

let to_old_bind ((Ident.Tvar n, _sort), term) =
  let args, term' = Term.let_lam term in
  let phi =
    ExtTerm.to_old_formula Map.Poly.empty (Map.of_list_exn args) term' []
  in
  (Ident.Pvar n, (to_old_sort_env_list args, phi))

let to_old ((params_senv, cand) : t) : CandSolOld.t =
  (to_old_sort_env_map params_senv, Set.Poly.map cand ~f:to_old_bind)

let to_subst (_params_senv, cand) : term_subst_map =
  Map.of_set_exn @@ Set.Poly.map cand ~f:(fun ((tvar, _), term) -> (tvar, term))

let simplify (params_senv, cand) : t =
  ( params_senv,
    Set.Poly.map cand ~f:(fun ((t, s), term) ->
        (*ExtTerm.str_of term*)
        let simplified =
          try ExtTerm.simplify_formula Map.Poly.empty params_senv term
          with _ -> ExtTerm.simplify_term Map.Poly.empty params_senv term
        in
        (* print_endline @@ "after simplify:" ^ ExtTerm.str_of simplified; *)
        ((t, s), simplified)) )

let str_of (params_senv, cand) : string =
  String.concat_map_set ~sep:"\n" cand
    ~f:(fun ((Ident.Tvar tvar, _sort), term) ->
      let params, term' = Term.let_lam term in
      let params', map =
        LogicOld.normalize_sort_env_list @@ to_old_sort_env_list params
      in
      let params' = of_old_sort_env_list params' in
      (*ExtTerm.str_of term'*)
      let str_term' =
        let senv = Map.force_merge params_senv @@ Map.of_list_exn params in
        try
          LogicOld.Formula.str_of @@ Evaluator.simplify
          @@ LogicOld.Formula.rename map
          @@ ExtTerm.to_old_formula Map.Poly.empty senv term' []
        with _ ->
          LogicOld.Term.str_of @@ Evaluator.simplify_term
          @@ LogicOld.Term.rename map
          @@ ExtTerm.to_old_term Map.Poly.empty senv term' []
      in
      sprintf "%s(%s) :=\n  %s" tvar
        (str_of_sort_env_list ExtTerm.str_of_sort params')
        str_term')

type pcsp = { candidates : (string * (string * string) list * string) list }
[@@deriving to_yojson]

let to_yojson (params_senv, cand) =
  pcsp_to_yojson
  @@ {
       candidates =
         Set.to_list
         @@ Set.Poly.map cand ~f:(fun ((Ident.Tvar tvar, _sort), term) ->
                let params, term' = Term.let_lam term in
                let params', map =
                  LogicOld.normalize_sort_env_list
                  @@ to_old_sort_env_list params
                in
                let params' = of_old_sort_env_list params' in
                (*ExtTerm.str_of term'*)
                let str_term' =
                  let senv =
                    Map.force_merge params_senv @@ Map.of_list_exn params
                  in
                  try
                    LogicOld.Formula.str_of @@ Evaluator.simplify
                    @@ LogicOld.Formula.rename map
                    @@ ExtTerm.to_old_formula Map.Poly.empty senv term' []
                  with _ ->
                    LogicOld.Term.str_of @@ Evaluator.simplify_term
                    @@ LogicOld.Term.rename map
                    @@ ExtTerm.to_old_term Map.Poly.empty senv term' []
                in
                ( tvar,
                  List.map params' ~f:(fun (tvar, sort) ->
                      (Ident.name_of_tvar tvar, ExtTerm.str_of_sort sort)),
                  str_term' ));
     }

(* replace all non-parametric interger in the term
   ToDo: rewrite *)
let replace_int_con t =
  let norm t sortmap =
    (* normalization *)
    Logic.ExtTerm.of_old_term @@ Normalizer.normalize_term
    @@ Logic.ExtTerm.to_old_term Map.Poly.empty sortmap t []
  in
  let rec replace_int_con' = function
    | Logic.App
        ( Logic.App
            ( Logic.Con (Logic.IntTerm.Mult, _),
              Logic.Con (Logic.IntTerm.Int _, _),
              _ ),
          Logic.Var (_, _),
          _ ) as t' ->
        t'
    | Logic.TyApp (term, a, b) -> Logic.TyApp (replace_int_con' term, a, b)
    | Logic.TyLam (a, term, b) -> Logic.TyLam (a, replace_int_con' term, b)
    | Logic.App (term1, term2, b) ->
        Logic.App (replace_int_con' term1, replace_int_con' term2, b)
    | Logic.Let (a, b, c, d, e) -> Logic.Let (a, b, c, d, e)
    | Logic.Var (_, _) as t' -> t'
    | Logic.Con (sym, _) as t' -> (
        match sym with
        | Logic.IntTerm.Int _ ->
            (*if Stdlib.(a = Z.zero) then t' else*)
            Logic.ExtTerm.mk_var @@ Ident.mk_fresh_tvar ()
        | Logic.IntTerm.Mult -> t'
        | Logic.IntTerm.Add -> t'
        | Logic.IntTerm.Sub -> t'
        | Logic.IntTerm.Div -> t'
        | Logic.IntTerm.Mod -> t'
        | Logic.IntTerm.Neg -> t'
        | Logic.IntTerm.Abs -> t'
        | Logic.BoolTerm.IfThenElse -> t'
        | _ -> t')
    | Logic.Bin (_, _, _, _, _) -> assert false
  in
  let rec add map = function
    | (a, b) :: tl -> add (Map.Poly.add_exn map ~key:a ~data:b) tl
    | [] -> map
  in
  let main (letlam, term) a b =
    let m = Map.Poly.singleton a b in
    let m' = add m letlam in
    Logic.ExtTerm.mk_lambda letlam @@ replace_int_con' (norm term m')
  in
  match t with (a, b), term -> ((a, b), main (Logic.ExtTerm.let_lam term) a b)

(* candidate generalization a la CEGIS(T) *)
let generalize (_psenv, cand) =
  let cand = Set.Poly.map ~f:replace_int_con cand in
  ( Map.of_set_exn
    @@ Set.Poly.map ~f:(fun x ->
           ( x,
             Logic.IntTerm.SInt
             (*ToDo: support non-integer parameters for candidate solution*) ))
    @@ Set.concat_map cand ~f:(snd >> Logic.Term.fvs_of),
    cand )
