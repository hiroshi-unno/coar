(* Options of checking an EHMTT through its reduction to HORS problems
   ([Reducer.solve_ehmtt]).  EffCaml verifies an EHMTT, and its
   configuration embeds the record as its field [ehmtt], read whichever
   checker it names; the checkers' own configurations have none, since they
   decide single HORS problems.

   - [check_all_problems]: the reduction yields several HORS problems (the
     whole program, and one per coercion).  When [false], they are decided in
     order and checking stops at the first one that is not satisfied; when
     [true], every problem is decided and each one's outcome is reported on
     standard error.  The verdict is the same either way: it is decided by the
     first problem, in order, that is not satisfied.
   - [hors_dir]: a directory into which the text of every generated HORS
     problem is written, as [<name>.hors] ([main.hors], [coerce1.hors], ...),
     after the reduction and before any problem is checked; [None] writes
     nothing. *)
open Core

type t = {
  check_all_problems : bool; [@default false]
  hors_dir : string option; [@default None]
}
[@@deriving yojson]

let default = { check_all_problems = false; hors_dir = None }
