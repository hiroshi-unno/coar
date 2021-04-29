open Core
open Common
open Util
open LogicOld

type t = ClauseOld.t Set.Poly.t

let pvs_of = Set.concat_map ~f:ClauseOld.pvs_of

let count_pvar_apps pvs cls =
  let pos_nonlin = ref Set.Poly.empty in
  let neg_nonlin = ref Set.Poly.empty in
  Set.Poly.filter_map pvs ~f:(fun pvar ->
      let dc, pc, nc =
        cls
        |> List.map ~f:(fun (_, ps, ns, _) ->
            let pc = Set.Poly.count ps ~f:(fun atm -> Stdlib.(=) pvar (Atom.pvar_of atm)) in
            let nc = Set.Poly.count ns ~f:(fun atm -> Stdlib.(=) pvar (Atom.pvar_of atm)) in
            (if pc >= 2 then pos_nonlin := Set.Poly.add !pos_nonlin pvar);
            (if nc >= 2 then neg_nonlin := Set.Poly.add !neg_nonlin pvar);
            if pc > 0 && nc > 0 then 1, 0, 0 else 0, pc, nc)
        |> List.unzip3
        |> (fun (dcs, pcs, ncs) -> List.fold dcs ~init:0 ~f:(+),
                                   List.fold pcs ~init:0 ~f:(+),
                                   List.fold ncs ~init:0 ~f:(+))
      in
      if dc = 0 && pc = 0 && nc = 0 then None else Some (pvar, (dc, pc, nc))),
  Set.Poly.inter !pos_nonlin !neg_nonlin

(* val simplify_with: Atom.t Set.Poly.t -> Atom.t Set.Poly.t -> t -> t *)
let simplify_with positive negative = Set.Poly.filter_map ~f:(ClauseOld.simplify_with positive negative)

let simplify npfvs is_valid = Set.Poly.filter_map ~f:(ClauseOld.simplify npfvs is_valid)

let reduce_sort_map = Set.Poly.map ~f:ClauseOld.reduce_sort_map

(* val resolve_one_step_all: Atom.t Set.Poly.t -> Atom.t Set.Poly.t -> t -> t *)
let resolve_one_step_all positive negative cs =
  Set.concat_map cs ~f:(ClauseOld.resolve_one_step_all positive negative)

(* val is_only_pure : t Set.Poly.t -> bool *)
let is_only_pure = Set.Poly.for_all ~f:ClauseOld.is_only_pure

(*let to_formula clauses = Formula.and_of (Set.Poly.map clauses ~f:ClauseOld.to_formula |> Set.Poly.to_list)*)

(*let of_formulas =
  List.fold ~f:(fun acc phi ->
      Set.Poly.union acc (Set.Poly.of_list @@ list_to_set @@ Formula.cnf_of phi))
    ~init:Set.Poly.empty*)
