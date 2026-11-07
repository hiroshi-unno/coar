open Core

(* Witness generation can be switched off when its cost matters.
   Every field has a default, so existing solver configs need no change; a
   solver config may set e.g. ["witness": {"sat": true, "unsat": ["Not_recorded"]}]. *)

(** whether, and how fully, the evidence behind an [unsat] verdict is
    recorded *)
type unsat =
  | Not_recorded
  | Recorded of {
      substitutions : bool; [@default true]
          (** also record, per example, the substitution that produced it
              from its clause (memory per example; needed for a checkable
              certificate) *)
    }
      (** record which examples conflicted, from which clauses, and which
          kind lemmas *)
[@@deriving yojson]

type t = {
  sat : bool; [@default true]
      (** record definitions for predicates eliminated by resolution and
          quantifier-eliminate them for the printed model *)
  unsat : unsat; [@default Recorded { substitutions = true }]
}
[@@deriving yojson]

let default = { sat = true; unsat = Recorded { substitutions = true } }
let disabled = { sat = false; unsat = Not_recorded }

(* whether the evidence behind an [unsat] verdict is recorded at all *)
let records_unsat t = match t.unsat with Not_recorded -> false | Recorded _ -> true

(* whether each example's substitution is recorded with it; implies
   [records_unsat] *)
let records_substitutions t =
  match t.unsat with Not_recorded -> false | Recorded { substitutions } -> substitutions
