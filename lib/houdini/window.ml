(** The state the Houdini-style pre-pass shares with the validator's clause
    checks while it runs: one value per validator instance, created by the
    validator and handed to the pre-pass ([FixedPoint.Make]) as an argument.

    The checks read it to behave differently inside the pre-pass's window: a
    question asked while [deadline] is set gets at most what is left of it
    ([cap_timeout]); a question that may not return is asked in a killed copy;
    the [in_*] flags say which kind of pre-pass question is being asked, for the
    per-kind budgets and counts. Outside the pre-pass every field is at its
    initial value, so nothing here changes a question asked elsewhere. The fixed
    point sets the fields and restores them (with [Exn.protect]) around each
    question. *)

open Core
open Ast.LogicOld

type t = {
  deadline : Time_ns.t option ref;
      (** the deadline of the pre-pass, a reading of [Common.Clock], while it runs with a budget;
          [None] at every other time *)
  pending_judge : (Formula.t * (model -> int list)) option ref;
      (** while one atom's question is asked: the question as it reaches the
          clause check (compared by physical identity) and the judge giving the
          positions of the atoms still to be asked that a model of the
          question's negation makes false *)
  judged_drops : int list option ref;
      (** the positions the countermodel of that question refuted, once it has
          been answered; cleared by the fixed point after each question *)
  atom_model_drops : int ref;
      (** atoms a reused countermodel dropped without a question of their own *)
  shared_body_proofs : int ref;
      (** questions proved against the body held once per clause *)
  shared_body_refutations : int ref;
      (** questions refuted there by a model every conjunct set aside holds
          under *)
  skip_weakened_once : bool ref;
      (** for the next question only: skip the weakened question, which would
          ask again what the shared-body session has just found satisfiable *)
  in_final : bool ref;  (** the final check of the fixed point is running *)
  in_fixed_point : bool ref;  (** the fixed point is running *)
  in_atom_question : bool ref;  (** one atom's question is being asked *)
  in_conjunction_question : bool ref;
      (** a conjunction of atoms is being asked (the countermodel route) *)
  in_seq_instantiation : bool ref;
      (** a sequence-existential question is asked by witness instantiation *)
  instr_pass : int ref;  (** the pass, for the question instrument *)
  instr_clause : int ref;  (** the clause in the pass, for the instrument *)
  instr_premise : Formula.t Lazy.t option ref;
      (** the clause's premise, for the instrument *)
}

let create () =
  {
    deadline = ref None;
    pending_judge = ref None;
    judged_drops = ref None;
    atom_model_drops = ref 0;
    shared_body_proofs = ref 0;
    shared_body_refutations = ref 0;
    skip_weakened_once = ref false;
    in_final = ref false;
    in_fixed_point = ref false;
    in_atom_question = ref false;
    in_conjunction_question = ref false;
    in_seq_instantiation = ref false;
    instr_pass = ref 0;
    instr_clause = ref 0;
    instr_premise = ref None;
  }

(* the milliseconds left before the deadline, [None] when none is set *)
let remaining_ms w =
  Option.map !(w.deadline) ~f:(fun d ->
      Time_ns.Span.to_int_ms (Time_ns.diff d (Common.Clock.now_ns ())))

let budget_spent w =
  match remaining_ms w with Some r -> r <= 0 | None -> false

(* spent, or so nearly that the question just asked was cut short by it: a
   solver can give up a few milliseconds before the budget it was given *)
let budget_nearly_spent w =
  match remaining_ms w with Some r -> r <= 100 | None -> false

(* [t] itself when no deadline is set; otherwise the smaller of [t] and the
   remainder (at least 1 ms, since a solver budget of 0 means none).  A
   caller's [Some 0] is unbounded, just like [None], so it must take the
   remainder rather than winning the numeric minimum. *)
let cap_timeout w (t : int option) =
  match remaining_ms w with
  | None -> t
  | Some r -> (
      let r = max 1 r in
      match t with Some t when t <> 0 && t <= r -> Some t | _ -> Some r)

(* the judge of [pending_judge] applied to [model], when [phi] is the very
   question it was set for; an exception of the judge drops nothing *)
let judge_pending w phi model =
  match !(w.pending_judge) with
  | Some (key, judge) when phys_equal key phi -> (
      try Some (judge model)
      with exn_ when not (Common.Timer.is_async exn_) -> Some [])
  | _ -> None
