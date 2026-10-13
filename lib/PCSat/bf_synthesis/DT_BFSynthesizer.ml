(* Boolean-function synthesis by a greedy decision tree: split on the
   qualifier of largest information gain until every leaf is pure (see
   [DecisionTree.build_tree]).  The result classifies every labelled atom of
   the reduced table, or the call fails when the qualifiers do not separate
   the examples. *)
open Core
open PCSatCommon

module Config = struct
  type t = { verbose : bool [@default false] } [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end
end

module Make (Cfg : Config.ConfigType) = struct
  let synthesize (ttable : TruthTable.table) (qlist, alist) =
    let open Or_error in
    DecisionTree.build_tree ttable (qlist, alist) >>= BoolFunction.of_dt
end
