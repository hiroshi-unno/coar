(* The dynamic form of choosing between a recursive function's two forms in a
   problem: a clause that applies a counted recursive function stays as it is
   (the function a definition the solver unfolds) until validation leaves it
   undecided; then it is replaced by its encoding with a graph unknown
   ([PCSP.RecFunGraph.encode_clauses]) and the problem is solved again.  An
   SMT solver does no induction, so a clause whose check needs one is left
   undecided with the function as a definition, while as an unknown the
   induction is an invariant the loop synthesises; a clause whose check needs
   none is cheaper left alone, since a graph unknown is recursive and has to
   be synthesised.

   PROTOCOL.  [solve] arms the registry with the clauses it may encode, runs
   the given solve, and reads back the clauses the validator reported
   ([note_undecided]) while armed.  The validator, seeing a report pending at
   the end of a round that rejected every candidate, answers [Undecided]
   (the loop ends with [unknown]) instead of returning the vacuous
   counterexample an undecided clause otherwise gives.

   CONTRACT of [solve ~candidates p].
   - Pre: [candidates] are clauses of [p] in clause form; nothing else is
     ever encoded, and each of them at most once, so there are at most
     [|candidates|] restarts (each restart encodes at least one).
   - Each problem solved is equisatisfiable with [p]: every step replaces
     some clauses by their encodings, each equisatisfiable on its own with the
     other unknowns fixed (the argument of [PCSP.RecFunGraph]), so a
     solution of the step's result restricted to [p]'s unknowns solves [p]
     and a solution of [p] extended by the graphs solves the result.  Hence
     a [sat] of any problem solved is one of [p] (its extra entries are the
     graph unknowns) and an [unsat] of it is an [unsat] of [p].
   - The answer is the first one that is not an [unknown] with a report
     pending, or that [unknown] when the encoding changes nothing.
   - Examples carried across a restart.  The solver context keeps, from one
     solve to the next, the examples whose derivations name only clauses the
     new problem still has, and drops those derived from a clause that is
     gone, with everything derived from them; a refutation found after a
     restart therefore rests only on clauses of the problem it was found for,
     which is the problem its witness records.  The function environment is
     kept whole ([keep_functions]), so an example that mentions a counted
     function's terms keeps reading them as its definition.  An example of a
     problem is a consequence of that problem's clauses over its unknowns,
     and the encoding changes neither those unknowns' solutions nor the
     clauses the example came from, so a kept example stays sound.

   Process-global state, by necessity: the validator is built by the
   coordinator from the problem alone and cannot be handed the registry.  It
   is read only while [on] is set; a solve nested inside another (the
   preprocessor's own solves of instances) has clauses that are not armed and
   so reports nothing. *)

open Core
open Common.Ext
open Ast

let on = Atomic.make false

(* the clauses the current solve may encode, and those the validator found
   undecided among them *)
let encodable : ClauseSet.t Atomic.t = Atomic.make Set.Poly.empty
let pending : ClauseSet.t Atomic.t = Atomic.make Set.Poly.empty

(* how many restarts [solve] has made in this process: an instrument for
   tests; nothing reads it to decide *)
let restarts = Atomic.make 0

(* [COAR_RECFUN_DYNAMIC_TRACE] set: one line on stderr per restart (a
   diagnostic; nothing reads it) *)
let trace = Option.is_some (Sys.getenv "COAR_RECFUN_DYNAMIC_TRACE")

let rec add_pending cl =
  let old = Atomic.get pending in
  if not (Atomic.compare_and_set pending old (Set.add old cl)) then
    add_pending cl

(* [cl]: a clause the validator asked about and the solver neither confirmed
   nor refuted on the candidate *)
let note_undecided (cl : Clause.t) =
  if Atomic.get on && Set.mem (Atomic.get encodable) cl then add_pending cl

let has_pending () = Atomic.get on && not (Set.is_empty (Atomic.get pending))

let solve ~(solve : PCSP.Problem.t -> State.output Or_error.t)
    ~(candidates : ClauseSet.t) (p : PCSP.Problem.t) =
  let rec loop p remaining =
    let armed =
      PCSP.RecFunGraph.encodable_clauses (PCSP.Problem.params_of p) remaining
    in
    Atomic.set encodable armed;
    Atomic.set pending Set.Poly.empty;
    let disarm () =
      let chosen = Atomic.get pending in
      Atomic.set encodable Set.Poly.empty;
      Atomic.set pending Set.Poly.empty;
      chosen
    in
    let r =
      match solve p with
      | r -> r
      | exception e ->
          ignore (disarm () : ClauseSet.t);
          raise e
    in
    let chosen = disarm () in
    match r with
    | Ok (PCSP.Problem.Unknown, _) when not (Set.is_empty chosen) ->
        let p', added =
          PCSP.RecFunGraph.encode_clauses ~only:(Set.mem chosen)
            ~keep_functions:true p
        in
        if List.is_empty added then r
        else (
          Atomic.incr restarts;
          if trace then
            eprintf
              "[recfun-dynamic] restart %d: %d clause(s) encoded, %d \
               unknown(s) introduced\n\
               %!"
              (Atomic.get restarts) (Set.length chosen) (List.length added);
          loop p' (Set.diff remaining chosen))
    | r -> r
  in
  loop p candidates
