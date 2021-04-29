open Core
open Common
open Util
open Logic

type t = Clause.t Set.Poly.t

let of_old_clause_set = Set.Poly.map ~f:Clause.of_old_clause

let to_old_clause_set exi_senv = Set.Poly.map ~f:(Clause.to_old_clause exi_senv)

let pvs_of cls = cls |> Set.Poly.map ~f:Clause.pvs_of |> Util.Set.concat

let count_pvar_apps cls =
  let pvs = pvs_of cls in
  let pos_nonlin = ref Set.Poly.empty in
  let neg_nonlin = ref Set.Poly.empty in
  pvs
  |> Set.Poly.to_list
  |> List.map ~f:(fun pvar ->
      pvar,
      cls
      |> Set.Poly.to_list
      |> List.map ~f:(fun ((_, ps, ns, _) : Clause.t) ->
          let pc = Set.Poly.count ps ~f:(fun t -> Set.Poly.mem (Term.fvs_of t) pvar) in
          let nc = Set.Poly.count ns ~f:(fun t -> Set.Poly.mem (Term.fvs_of t) pvar) in
          (*let pc = Set.Poly.count ps ~f:(Atom.occur pvar) in
            let nc = Set.Poly.count ns ~f:(Atom.occur pvar) in*)
          (if pc >= 2 then pos_nonlin := Set.Poly.add !pos_nonlin pvar);
          (if nc >= 2 then neg_nonlin := Set.Poly.add !neg_nonlin pvar);
          if pc > 0 && nc > 0 then 1, 0, 0 else 0, pc, nc)
      |> List.unzip3
      |> (fun (dcs, pcs, ncs) -> List.fold dcs ~init:0 ~f:(+),
                                 List.fold pcs ~init:0 ~f:(+),
                                 List.fold ncs ~init:0 ~f:(+))),
  Set.Poly.inter !pos_nonlin !neg_nonlin

(* val simplify_with: Set.Poly.t -> Set.Poly.t -> t -> t *)
let simplify_with positive negative = Set.Poly.filter_map ~f:(Clause.simplify_with positive negative)

(* val resolve_one_step_all: Set.Poly.t -> Set.Poly.t -> t -> t *)
let resolve_one_step_all positive negative exi_senv = Set.concat_map ~f:(Clause.resolve_one_step_all positive negative exi_senv)

(* val is_only_pure : t -> bool *)
let is_only_pure = Set.Poly.for_all ~f:Clause.is_only_pure

let to_formula clauses(*ToDo: rename*) =
  BoolTerm.and_of @@ Set.Poly.to_list @@ Set.Poly.map clauses ~f:Clause.to_formula

let of_formulas exi_senv phis =
  Util.Set.concat_map phis ~f:(fun (uni_senv, phi) ->
    Set.Poly.map ~f:(fun (ps, ns, phi) -> uni_senv, ps, ns, phi) @@
    BoolTerm.cnf_of exi_senv uni_senv phi)

(** assume that chc is CHC *)
let pred_of exi_senv chc pvar =
  match List.map ~f:snd @@ Set.Poly.to_list @@ Set.Poly.map ~f:(Clause.pred_of_definite exi_senv) @@ Set.Poly.filter chc ~f:(Clause.is_definite pvar) with
  | [] -> failwith "pred_of"
  | (env, phi) :: ps ->
    env,
    BoolTerm.and_of @@
    phi :: List.map ps ~f:(fun (env', phi') ->
        let sub = Map.Poly.of_alist_exn @@ List.map2_exn env' env ~f:(fun (x, _) (y, _) -> x, Term.mk_var y) in
        Term.subst sub phi')

let subst exi_senv sub clauses = Set.Poly.map ~f:(Clause.subst exi_senv sub) clauses
