open Common.Ext
open Ast.LogicOld

type hspace = {
  depth : int;
  params : sort_env_list;
  quals : Formula.t Set.Poly.t;
  qdeps : (Formula.t, QDep.t) Map.Poly.t;
  terms : Term.t Set.Poly.t;
  consts : Term.t Set.Poly.t;
}
