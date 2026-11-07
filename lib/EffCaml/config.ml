(* Configuration of EffCaml: whether to trace, the higher-order model
   checker ([HOMCSolver]) its generated problems and a HORS problem given to
   it are handed to, and, under [ehmtt], how an EHMTT program's generated
   problems are checked and kept, whichever checker [solver] names (no other
   configuration carries these options). *)

open Core
open Common.Util

(* which CPS transformation produces the model-checking problems: [Legacy] is
   the generator of [Cgen] (Sekiyama and Unno's OOPSLA 2024 transformation
   with a coercion for recursive calls under a handler); [Selective_atp]
   asks the CPS framework for the selective transformation of Sekiyama, Dal
   Lago and Unno (OOPSLA 2025), which is not built yet and is refused there *)
type cps_scheme = Legacy | Selective_atp [@@deriving yojson]

type t = {
  verbose : bool; [@default false]
  cps_scheme : cps_scheme; [@default Legacy]
  solver : HOMCSolver.Config.t ext_file;
      [@default Common.Util.ExtFile.Filename "./config/solver/horsat2_ce.json"]
  ehmtt : HOMC.EhmttOptions.t; [@default HOMC.EhmttOptions.default]
  mbcsol : RCaml.MBcsol.Config.t;
      [@default Common.Util.config_default RCaml.MBcsol.Config.of_yojson "{}"]
      (** the effect-constraint solver's settings (shared with RCaml); its
          [verbose] is replaced by this configuration's *)
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  HOMCSolver.Config.load_ext_file cfg.solver >>= fun solver ->
  Ok { cfg with solver }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "EffCaml"
  let instantiate = instantiate_ext_files
end)
