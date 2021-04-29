open Core
open Common.Util
open Ast
open PCSatCommon

module Config = struct
  type t = { verbose: bool } [@@deriving yojson]
  module type ConfigType = sig val config: t end
end

module Make (Cfg: Config.ConfigType) = struct
  type dtree = Leaf of bool | Node of PropLogic.Formula.t * dtree * dtree

  let entropy (d: TruthTable.table) =
    let d_pos, d_neg = TruthTable.num_pos_neg_labeled_atoms d in
    let p, n = float_of_int d_pos, float_of_int d_neg in
    let l = if Stdlib.(>) p 0. then
        let x = p /. (p +. n) in x *. log2 x
      else 0. in
    let r = if Stdlib.(>) n 0. then
        let x = n /. (p +. n) in x *. log2 x
      else 0. in
    let res = (-1.) *. (l +. r) in
    assert (Stdlib.(>=) res 0. && Stdlib.(<=) res 1.);
    res

  let gain (d: TruthTable.table) q =
    let d_q, d_nq = TruthTable.divide q d in
    let size_d_q = float_of_int @@ TruthTable.num_atoms d_q in
    let size_d_nq = float_of_int @@ TruthTable.num_atoms d_nq in
    let size_d = float_of_int @@ TruthTable.num_atoms d in
    let weighted_entropy_q = entropy d_q *. size_d_q /. size_d in
    let weighted_entropy_nq = entropy d_nq *. size_d_nq /. size_d in
    entropy d -. (weighted_entropy_q +. weighted_entropy_nq)

  let choose_qualifier (d: TruthTable.table) =
    if Map.is_empty d.alist then
      Or_error.error_string "There is no example"
    else if List.is_empty d.qlist then
      Or_error.error_string "There is no qualifier"
    else Ok (argmax d.qlist ~f:(gain d))

  let rec build_tree (d: TruthTable.table) =
    let d_pos, d_neg = TruthTable.num_pos_neg_labeled_atoms d in
    if d_neg = 0 then Ok (Leaf true)
    else if d_pos = 0 then Ok (Leaf false)
    else
      let open Or_error in
      choose_qualifier d >>= fun qi ->
      let t_q, t_nq = TruthTable.divide qi d in
      let qual = PropLogic.Formula.mk_atom (TruthTable.name_of_qual qi) in
      build_tree t_q >>= fun t_q ->
      build_tree t_nq >>= fun t_nq ->
      Ok (Node (qual, t_q, t_nq))

  let rec formula_of_tree = function
    | Leaf b ->
      Ok PropLogic.Formula.(if b then mk_true () else mk_false ())
    | Node (q, t1, t2) ->
      let open Or_error in
      formula_of_tree t1 >>= fun subtree1 ->
      formula_of_tree t2 >>= fun subtree2 ->
      Ok PropLogic.Formula.(mk_or (mk_and q subtree1) (mk_and (mk_neg q) subtree2))

  let synthesize (ttable: TruthTable.table) = let open Or_error in
    build_tree ttable >>= formula_of_tree
end
