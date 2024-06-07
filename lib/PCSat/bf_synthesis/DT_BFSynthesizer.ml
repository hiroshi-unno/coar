open Core
open PCSatCommon

module Config = struct
  type t = { verbose : bool } [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end
end

module Make (Cfg : Config.ConfigType) = struct
  let synthesize (ttable : TruthTable.table) (qlist, alist) =
    let open Or_error in
    DecisionTree.build_tree ttable (qlist, alist) >>= BoolFunction.of_dt
end
