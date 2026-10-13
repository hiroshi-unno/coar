(* Configuration of the Spacer backend (Z3's fixedpoint engine run in-process
   through the Z3 library).  Besides the preprocessing applied first and Z3's
   own options (native model-based projection, global guidance, Z3's internal
   validation), it says whether a returned solution must be usable
   ([solution_needed], which turns off the Z3 transformations that make it
   unsound), whether a counterexample is wanted, and whether a solution is
   re-checked against the clauses ([check_validity]); [conservative_check]
   rejects a solution whose check is undecided, and [solve_again_if_invalid]
   queries again instead of failing when the check rejects one. *)
open Core
open Common.Util
open Preprocessing

type t = {
  preprocessor : Preprocessor.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/preprocessor/disable.json"]
  timeout : int option; [@default None]
  use_z3_native_mbp : bool; [@default true]
  enable_global_guidance : bool; [@default true]
  enable_z3_validation : bool; [@default false]
  check_validity : bool; [@default false]
  conservative_check : bool; [@default true]
  solve_again_if_invalid : bool; [@default true]
  solution_needed : bool; [@default false]
  cex_needed : bool; [@default false]
  verbose : bool; [@default false]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let instantiate_ext_files cfg =
  let open Or_error in
  Preprocessor.Config.load_ext_file cfg.preprocessor >>= fun preprocessor ->
  Ok { cfg with preprocessor }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "SPACER"
  let instantiate = instantiate_ext_files
end)
