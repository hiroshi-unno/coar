(* Configuration of the template back end that solves a predicate constraint
   problem by instantiating each predicate unknown with one fixed template and
   handing the resulting polynomial quantified entailments to PolyQEnt.

   [preprocessor]: the preprocessing run before the back end (predicate
   elimination, argument erasure) and the solution extension after it, as for
   PCSat.  [polyqent]: the PolyQEnt wrapper's configuration (its record,
   written as ["Instance", {...}] or a file holding the record).  [adm_pieces]: the
   number [L] of absolute-value pieces in an admissible template's bound
   [c + |e_1| + ... + |e_L|] (each [e_l] affine in the unknown's numeric
   arguments); a negative occurrence of the template is split into [2^L] cases
   per value component.  [cond_scaled]: for an admissible predicate with
   conditioning, whether the value is bounded by the score times a constant
   ([true]) or by the bound alone ([false]).  [max_pqes]: the number of
   entailments above which the problem is declined rather than sent. *)
open Core
open Common.Util

(* the wrapper's configuration with every field at its default (a
   [config/solver/*polyqent*.json] file is a solver choice, a variant around
   this record, and is not read here) *)
let default_polyqent =
  match PolyQEnt.Config.of_yojson (`Assoc []) with
  | Ok cfg -> cfg
  | Error msg -> failwith msg

type t = {
  preprocessor : Preprocessing.Preprocessor.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/preprocessor/enable.json"]
  polyqent : PolyQEnt.Config.t ext_file; [@default Common.Util.ExtFile.Instance default_polyqent]
  adm_pieces : int; [@default 1]
  cond_scaled : bool; [@default true]
  max_pqes : int; [@default 4096]
  verbose : bool; [@default false]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  Preprocessing.Preprocessor.Config.load_ext_file cfg.preprocessor
  >>= fun preprocessor ->
  PolyQEnt.Config.load_ext_file cfg.polyqent >>= fun polyqent ->
  Ok { cfg with preprocessor; polyqent }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "PolyQEntTempl"
  let instantiate = instantiate_ext_files
end)
