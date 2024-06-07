open Core
open Common.Ext
open Ast
open Ast.LogicOld
open PCSatCommon

let classify _dummy_param _params pos_examples neg_examples =
  if Set.is_empty pos_examples || Set.is_empty neg_examples then Set.Poly.empty
  else failwith "not implemented (should return set of qualifiers)"

let nn_half_spaces_of dummy_param sorts pos_examples neg_examples =
  let params = LogicOld.sort_env_list_of_sorts sorts in
  ( params,
    Set.union
      (Set.Poly.of_list params
      |> Set.Poly.filter_map ~f:(function
           | x, T_bool.SBool -> Some (Term.mk_var x T_bool.SBool)
           | _, T_int.SInt -> None
           | _, T_real.SReal -> failwith "real"
           | _, s -> failwith ("not supported" ^ Term.str_of_sort s))
      |> Set.Poly.map ~f:(fun x -> Formula.eq x (T_bool.mk_true ())))
      (classify dummy_param params pos_examples neg_examples) )

module Make (Config : sig
  val dummy_param : int
end) =
struct
  let qualifiers_of _pvar sorts labeled_atoms (_senv, clause_examples) =
    let pos_examples =
      Set.Poly.filter_map labeled_atoms ~f:(fun (atom, label) ->
          if TruthTable.label_pos = label then
            match ExAtom.instantiate atom with
            | ExAtom.PApp (_, terms) -> Some terms
            | ExAtom.PPApp (_, (_, terms)) -> Some terms
            | _ -> None
          else None)
    in
    let neg_examples =
      Set.Poly.filter_map labeled_atoms ~f:(fun (atom, label) ->
          if TruthTable.label_neg = label then
            match ExAtom.instantiate atom with
            | ExAtom.PApp (_, terms) -> Some terms
            | ExAtom.PPApp (_, (_, terms)) -> Some terms
            | _ -> None
          else None)
    in
    (* use the following instead if you want to use NN for labeling of clause examples *)
    let _pos_examples, _neg_examples, _und_examples =
      let pos_examples, neg_examples, und_examples =
        ClauseGraph.pos_neg_und_examples_of clause_examples
      in
      ( ExClauseSet.instantiate pos_examples,
        ExClauseSet.instantiate neg_examples,
        ExClauseSet.instantiate und_examples )
    in
    let params, quals =
      nn_half_spaces_of Config.dummy_param sorts pos_examples neg_examples
    in
    Set.Poly.map ~f:(fun qual -> (params, Normalizer.normalize qual)) quals

  let str_of_domain = "Neural Network"
end
