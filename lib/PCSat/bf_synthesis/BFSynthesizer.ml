(* Boolean-function synthesis over a truth table: the dispatcher.

   Given a predicate's truth table (rows are qualifiers, columns labelled
   example atoms) and the qualifier and atom indices to use, [synthesize]
   returns a propositional formula over the atoms [#qual_i] that is meant to
   classify the labelled atoms; [BoolFunction.concretize] turns it back into a
   first-order formula.  The configuration selects the learner: a greedy
   decision tree, a Monte-Carlo-tree-search variant of it, or an unimplemented
   placeholder that always returns an error. *)
open Core
open Common.Util
open PCSatCommon

module type BFSynthesizerType = sig
  val synthesize :
    TruthTable.table ->
    TruthTable.qlist * TruthTable.alist ->
    Ast.PropLogic.Formula.t Or_error.t
end

module Config = struct
  type t =
    | DTBF of DT_BFSynthesizer.Config.t
    | MCTSBF of MCTS_BFSynthesizer.Config.t
    | SCQMBF of SCQM_BFSynthesizer.Config.t
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "BFSynthesizer"

    (* a leaf: no nested config to load *)
    let instantiate = Or_error.return
  end)
end

module Make (Cfg : Config.ConfigType) : BFSynthesizerType =
  (val match Cfg.config with
       | DTBF cfg ->
           (module DT_BFSynthesizer.Make (struct
             let config = cfg
           end) : BFSynthesizerType)
       | MCTSBF cfg ->
           (module MCTS_BFSynthesizer.Make (struct
             let config = cfg
           end) : BFSynthesizerType)
       | SCQMBF cfg ->
           (module SCQM_BFSynthesizer.Make (struct
             let config = cfg
           end) : BFSynthesizerType))
