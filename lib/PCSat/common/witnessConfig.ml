open Core

(* Witness generation can be switched off when its cost matters.
   Every field has a default, so existing solver configs need no change; a
   solver config may set e.g. ["witness": {"sat": true, "unsat": false}]. *)
type t = {
  sat : bool; [@default true]
      (** record definitions for predicates eliminated by resolution and
          quantifier-eliminate them for the printed model *)
  unsat : bool; [@default true]
      (** record the evidence behind an [unsat] verdict (which examples
          conflicted, from which clauses, which kind lemmas) *)
  unsat_substitutions : bool; [@default true]
      (** also record, per example, the substitution that produced it from its
          clause (memory per example; needed for a checkable certificate) *)
}
[@@deriving yojson]

let default = { sat = true; unsat = true; unsat_substitutions = true }
let disabled = { sat = false; unsat = false; unsat_substitutions = false }
