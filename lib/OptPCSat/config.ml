(* Configuration of OptPCSat: the constraint solvers used to improve a
   solution and to check its optimality, whether to start from a seed
   solution read beside the input, whether improvement considers the whole
   priority list or only the predicates not yet optimized, the side
   conditions (none, non-trivial or non-vacuous solutions), and how an optimality
   certificate that is not known to be exact is treated. *)
open Core
open Common.Util

type mode = NoSideCond | NonTrivial | NonVacuous [@@deriving yojson]

type t = {
  load_init_sol : bool; [@default false]
  improve_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/pcsat_d3_nothr.json"]
      (** the solver that improves a solution: PCSat at its default except
          that the predicate template starts at three disjuncts and the
          constant bound is never capped, so an improvement is searched among
          disjunctive shapes from the first round rather than reached by growth
          from one disjunct *)
  opt_check_solver : PCSPSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/pcsat.json"]
      (** the solver that checks a solution's optimality: PCSat at its
          default *)
  verbose : bool; [@default false]
  one_by_one : bool; [@default true]
  improve_current : bool; [@default false]
  side_conditions : mode; [@default NoSideCond]
  (* accept the optimality checker's certificate only when it is exact;
     [false] treats every certificate as exact and accepts it at once *)
  exact_opt_check : bool; [@default true]
  (* milliseconds the improver gets to refute an inexact certificate before it
     is accepted anyway *)
  inexact_certificate_wait_ms : int; [@default 5000]
  (* once a predicate's optimization is over, substitute the improved
     predicates' solutions into the problem and preprocess it again before the
     next predicate is improved, so later improvements are made against the
     earlier ones fixed; [false] keeps the problem unchanged and passes the
     current solution along only as the candidate, which leaves the earlier
     predicates free to change *)
  fix_improved_solutions : bool; [@default false]
  (* in the maximality check's auxiliary problem, keep the Tseitin predicates
     the check introduces for a disjunction of conjunctions (named [PTsetin..])
     from elimination by the preprocessor; [false] lets the preprocessor
     eliminate them like any other unknown *)
  maximality_keeps_tseitin_preds : bool; [@default false]
}
[@@deriving yojson]

module type ConfigType = sig
  val config : t
end

let is_non_trival_mode = function NonTrivial -> true | _ -> false
let is_non_vacuous_mode = function NonVacuous -> true | _ -> false

let instantiate_ext_files cfg =
  let open Or_error in
  PCSPSolver.Config.load_ext_file cfg.improve_solver >>= fun improve_solver ->
  PCSPSolver.Config.load_ext_file cfg.opt_check_solver
  >>= fun opt_check_solver -> Ok { cfg with improve_solver; opt_check_solver }

include MakeExtFile (struct
  type nonrec t = t

  let of_yojson = of_yojson
  let to_yojson = to_yojson
  let name = "OptPCSat"
  let instantiate = instantiate_ext_files
end)
