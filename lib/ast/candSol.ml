open Core
open Common.Util
open Logic

type t = SortMap.t * ((Ident.tvar * Sort.t) * term) Set.Poly.t

let of_old ((params_senv, cand) : CandSolOld.t) : t =
  SortMap.of_old_sort_map ExtTerm.of_old_sort params_senv,
  Set.Poly.map cand ~f:(fun (Ident.Pvar n, (args, phi)) ->
      let args_new = LogicOld.SortEnv.map args ~f:(fun (tvar, sort) -> tvar, ExtTerm.of_old_sort sort) in
      let sort = Sort.mk_fun @@ (List.map args_new ~f:snd @ [ExtTerm.SBool]) in
      (Ident.Tvar n, sort), Term.mk_lambda args_new (ExtTerm.of_old_formula phi))

let to_old ((params_senv, cand) : t) : CandSolOld.t =
  SortMap.to_old_sort_map ExtTerm.to_old_sort params_senv,
  Set.Poly.map cand ~f:(fun ((Ident.Tvar n, _sort), term) ->
      let args, term' = Term.let_lam term in
      let phi = ExtTerm.to_old_formula (SortMap.of_set @@ Set.Poly.of_list args) term' [] in
      Ident.Pvar n, (LogicOld.SortEnv.of_list @@ List.map args ~f:(Pair.map_snd @@ ExtTerm.to_old_sort), phi))

let to_subst (_params_senv, cand) : (Ident.tvar, term) Map.Poly.t =
  Map.of_set @@ Set.Poly.map cand ~f:(fun ((tvar, _), term) -> tvar, term)

let str_of (params_senv, cand) : string =
  String.concat ~sep:"\n" @@
  Set.Poly.to_list @@ Set.Poly.map cand ~f:(fun ((Ident.Tvar tvar, _sort), term) ->
      let params, term' = Term.let_lam term in
      let params', map = LogicOld.SortEnv.normalize (SortEnv.to_old_sort_env ExtTerm.to_old_sort params) in
      let params' = SortEnv.of_old_sort_env ExtTerm.of_old_sort params' in
      (*ExtTerm.str_of term'*)
      let str_term' =
        let senv = Map.force_merge params_senv @@ SortMap.of_set @@ Set.Poly.of_list params in
        try
          LogicOld.Formula.str_of @@ Evaluator.simplify @@ LogicOld.Formula.rename map @@
          ExtTerm.to_old_formula senv term' []
        with _ ->
          LogicOld.Term.str_of @@ Evaluator.simplify_term @@ LogicOld.Term.rename map @@
          ExtTerm.to_old_term senv term' []
      in
      Printf.sprintf "%s(%s) :=\n  %s" tvar (SortEnv.str_of ExtTerm.str_of_sort params') str_term')

let str_of_list candidates =
  String.concat ~sep:"\n"
  @@ List.mapi candidates ~f:(fun i candidate ->
      (Printf.sprintf "**** %s candidate solution\n" (Ordinal.string_of i))
      ^ (str_of candidate) ^ "\n")

(* replace all non-parametric interger in the term
   ToDo: rewrite *)
let replace_int_con t =
  let norm t sortmap = (* normalization *)
    Logic.ExtTerm.of_old_term 
      (Normalizer.normalize_term 
         (Logic.ExtTerm.to_old_term
            sortmap t []))
  in
  let rec replace_int_con' t'=
    match t' with
    | Logic.App(
        Logic.App(Logic.Con(Logic.IntTerm.Mult,_),
                      Logic.Con(Logic.IntTerm.Int _,_),_),
        Logic.Var(_,_),_) -> t'
    | Logic.TyApp(term, a, b) -> Logic.TyApp(replace_int_con' term, a, b)
    | Logic.TyLam(a, term, b) -> Logic.TyLam(a, replace_int_con' term, b)
    | Logic.App(term1, term2, b) -> Logic.App(replace_int_con' term1, replace_int_con' term2, b)
    | Logic.Let(a, b, c, d, e) -> Logic.Let(a, b, c, d, e)
    | Logic.Var(_,_) -> t'
    | Logic.Con(sym,_) ->begin match sym with 
        | Logic.IntTerm.Int _ -> (*if Stdlib.(=) a (Z.of_int 0) then t' else*) Logic.ExtTerm.mk_var @@ Ident.mk_fresh_tvar ()
        | Logic.IntTerm.Mult -> t'
        | Logic.IntTerm.Add -> t'
        | Logic.IntTerm.Sub -> t'
        | Logic.IntTerm.Div -> t'
        | Logic.IntTerm.Mod -> t'
        | Logic.IntTerm.Neg -> t'
        | Logic.IntTerm.Abs -> t'
        | Logic.BoolTerm.IfThenElse -> t'
        | _ -> t' end
    | Logic.Bin(_, _, _, _, _) -> assert false
  in
  let rec add map letlam =
    match letlam with
    | (a, b) :: tl -> add (Map.Poly.add_exn map ~key:a ~data:b) tl
    | [] -> map
  in
  let main res a b =
    match res with
    | (letlam, term) -> let m = Map.Poly.singleton a b in let m' = add m letlam in Logic.ExtTerm.mk_lambda letlam (replace_int_con' (norm term m'))
  in
  match t with
  | ((a,b),term) -> ((a,b),main (Logic.ExtTerm.let_lam term) a b)

(* candidate generalization a la CEGIS(T) *)
let generalize (_psenv, cand) =
  let cand = Set.Poly.map ~f:replace_int_con cand in
  Set.concat_map cand ~f:(fun (_, t) -> Logic.Term.fvs_of t)
  |> Set.Poly.map ~f:(fun x -> x, Logic.IntTerm.SInt(*ToDo: support non-integer parameters for candidate solution*))
  |> Logic.SortMap.of_set,
  cand
