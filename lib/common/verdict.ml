(** The answer a solver gives about one problem.

    Four constructors shared by every fixpoint-logic backend: muCLP validity
    checking, MuCyc, MuStrat and the quantitative-fixpoint (QFL) path.
    They live here rather than in [MuCLP.Problem], where every line that
    mentioned one would read as though a muCLP solver were running -- a QFL
    bound query is answered by a pCSP solver (PolyQEnt on that path), and
    [MuCLP.Problem.Valid] there would misstate which solver answered.
    [MuCLP.Problem.solution] remains as an equal type, so that spelling still
    compiles.

    [Unknown] and [Timeout] are ordinary answers here, not failures: a backend
    that cannot settle a problem has answered the question it was asked. *)

type t = Valid | Invalid | Unknown | Timeout

let str_of = function
  | Valid -> "valid"
  | Invalid -> "invalid"
  | Unknown -> "unknown"
  | Timeout -> "timeout"

(** the LTS vocabulary, in which the two undecided answers are one *)
let lts_str_of = function
  | Valid -> "YES"
  | Invalid -> "NO"
  | Unknown | Timeout -> "MAYBE"

(** dualising a problem dualises its answer, and leaves the undecided ones *)
let flip = function Valid -> Invalid | Invalid -> Valid | x -> x
