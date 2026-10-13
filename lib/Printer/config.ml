(* Configuration of the Printer backend, which dumps a problem in another
   format instead of solving it: the preprocessor run first, and the output
   format chosen per input class (SAT problems as text or as a higher-order
   model-checking problem, SMT as text or SMT-LIB2, labelled transition
   systems as muCLP or as a predicate constraint problem). *)
open Core
open Common.Util
open Preprocessing

type sat_format = String | HOMC [@@deriving yojson]
type smt_format = String | SMT2 [@@deriving yojson]
type lts_format = MuCLP | PCSP [@@deriving yojson]

type t = {
  preprocessor : Preprocessor.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/preprocessor/enable.json"]
  homc_sat : HOMCSat.Config.t; [@default Common.Util.config_default HOMCSat.Config.of_yojson "{}"]
  sat_format : sat_format; [@default HOMC]
  smt_format : smt_format; [@default SMT2]
  lts_format : lts_format; [@default MuCLP]
  add_missing_forall : bool; [@default false]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  Preprocessor.Config.load_ext_file cfg.preprocessor >>= fun preprocessor ->
  HOMCSat.Config.instantiate_ext_files cfg.homc_sat >>= fun homc_sat ->
  Ok { cfg with preprocessor; homc_sat }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "Printer"
  let instantiate = instantiate_ext_files
end)
