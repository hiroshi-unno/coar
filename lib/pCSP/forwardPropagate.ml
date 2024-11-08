open Core
open Common.Ext
open Ast
open Ast.Logic

(* recursion-free CHC solver based on forward propagation *)
(* we assume that CHC is satisfiable and contains no undefined predicate variable *)

let pos_pvars =
  Set.Poly.map ~f:(fun c ->
      match Set.choose @@ Clause.pos_pvars c with
      | None -> assert false
      | Some pvar -> pvar)

let rec solve exi_senv lbs cs =
  let ps = pos_pvars cs in
  let ready_to_compute_lb c =
    Set.for_all ~f:(Map.Poly.mem lbs) @@ Clause.neg_pvars c
  in
  let ps_ready =
    Set.filter ps ~f:(fun pvar ->
        Set.for_all ~f:ready_to_compute_lb
        @@ Set.filter cs ~f:(Clause.is_definite pvar))
  in
  let cs1, cs2 =
    Set.partition_tf cs ~f:(fun c ->
        Set.exists ps_ready ~f:(fun p -> Clause.is_definite p c))
  in
  if Set.is_empty cs1 then
    if Set.is_empty cs2 then Ok (Problem.Sat lbs)
    else Or_error.error_string "not supported"
  else
    let lbs' =
      let cs1 = ClauseSet.subst exi_senv lbs cs1 in
      Set.Poly.map (pos_pvars cs1) ~f:(fun pvar ->
          let env, phi = ClauseSet.pred_of_pos exi_senv cs1 pvar in
          (pvar, Term.mk_lambda env phi))
      |> Map.of_set_exn |> Map.force_merge lbs
    in
    solve exi_senv lbs' cs2

let solve pcsp =
  Problem.to_nnf pcsp |> Problem.to_cnf |> Problem.clauses_of
  |> Set.filter ~f:(Fn.non Clause.is_goal) (*ToDo*)
  |> solve (Problem.senv_of pcsp) Map.Poly.empty
