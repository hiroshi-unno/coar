open Core
open PCSatCommon

module Config = struct
  type t = { verbose : bool; coeff : float; bias : int (* must be positive *) }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end
end

module Make (Cfg : Config.ConfigType) = struct
  let search_tree = ref (DecisionTree.Select [])
  let total_num_visited = ref 0

  let synthesize (ttable : TruthTable.table) (qlist, alist) =
    let open Or_error in
    assert (Cfg.config.bias > 0);
    DecisionTree.mcts ttable (qlist, alist) !total_num_visited
      (Cfg.config.coeff, Cfg.config.bias)
      !search_tree
    >>= fun search_tree' ->
    search_tree := search_tree';
    total_num_visited := !total_num_visited + 1;
    BoolFunction.of_dt search_tree'
end
