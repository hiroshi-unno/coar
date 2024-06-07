open Core
open Common.Ext
open Ast
open Ast.PropLogic.Formula

type t = PropLogic.Formula.t

let size = PropLogic.Formula.size
let height = PropLogic.Formula.height
let str_of = PropLogic.Formula.str_of
let name_of_qual qi = sprintf "#qual_%d" qi
let qual_of_name name k = Scanf.sscanf name "#qual_%d" k

let rec of_dt = function
  | DecisionTree.Leaf b ->
      Ok PropLogic.Formula.(if b then mk_true () else mk_false ())
  | DecisionTree.Node (q, t1, t2) ->
      let open Or_error in
      of_dt t1 >>= fun subtree1 ->
      of_dt t2 >>= fun subtree2 ->
      let atm = mk_atom (name_of_qual q) in
      Ok
        PropLogic.Formula.(
          mk_or (mk_and atm subtree1) (mk_and (mk_neg atm) subtree2))
  | DecisionTree.Select ((_, _, t) (* the head is the selected branch *) :: _)
    ->
      of_dt t
  | DecisionTree.Select [] -> assert false

let rec concretize quals = function
  | True _ -> LogicOld.Formula.mk_true ()
  | False _ -> LogicOld.Formula.mk_false ()
  | Atom (name, _) -> qual_of_name name (fun qi -> quals.(qi))
  | UnaryOp (Neg, phi, _) -> LogicOld.Formula.mk_neg (concretize quals phi)
  | BinaryOp (And, phi1, phi2, _) ->
      LogicOld.Formula.mk_and (concretize quals phi1) (concretize quals phi2)
  | BinaryOp (Or, phi1, phi2, _) ->
      LogicOld.Formula.mk_or (concretize quals phi1) (concretize quals phi2)
