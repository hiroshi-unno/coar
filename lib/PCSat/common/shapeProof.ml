open Core
open Ast.LogicOld

(* A validity proof of an obligation without unknowns, asked after exact
   rewrites and in a weakened form, for a caller that reads only a proof.

   [valid_within ~ms ~id phi] asks, each in a forked copy killed after its
   budget ([ForkedQuery.valid_within]), or in this process under Z3's own
   budget with [~fork:false] (for a caller that is itself a forked copy with
   a deadline: a copy of a copy doubles the memory once the collector touches
   the heap):
   1. [phi] rewritten by [Evaluator.elim_onepoint_and_split_binders] under
      [Evaluator.with_shape_rewrites] (an equivalence in every model) and then
      weakened by [Evaluator.abstract_seq_reads_and_functions] (every sequence
      read and every defined function an uninterpreted array), asked of Z3 with
      [ms] milliseconds;
   2. when that is not proved, the same form restricted by
      [Evaluator.relevant_premises] to the premises tied to the goal's subject
      (the variables it equates with its own) and to its rarer variables, then
      at [k] = 8, 16 and 32 (each a strengthening), with [ms / 2] each.
   3. with [~literal_closures:(m, ms')] ([m > 0]) and still nothing proved, at
      most [m] forms of [Evaluator.literal_closures] (each top-level literal
      taken as the conclusion, with the disjuncts [closure_hops] steps away
      through variables occurring in at most [closure_k] disjuncts), each a
      strengthening, with [ms'] each.
   Contract: [true] only when one of those forms is proved valid, which proves
   [phi] valid in every model: the rewrite is an equivalence, the abstraction
   reads its arrays as one interpretation among those it quantifies over, and
   the restriction implies [phi].  [false] otherwise; nothing is refuted.

   Why: the obligations a layout computation leaves after predicate
   elimination (a trusted callee's contract against the caller's postcondition
   over the same values) are instances of their premises, but Z3 finds no
   instance -- the premises' variables are defined by cases or fixed through
   constructor applications and have no ground term to be matched with, and a
   quantified premise read through [seq.nth] is not instantiated at a ground
   read.  Once rewritten and weakened they are proved in under a second. *)

(* [with_refutation_only f]: [f ()] with [refutation_only] set, restored
   afterwards whatever [f] does.  For a caller that reads only a refutation of
   what [f] solves (a forked copy that answers only [unsat]): a shape proof can
   only show a clause valid, which refutes nothing, while each form it asks
   takes up to its budget -- on [univariant_sat] the stage takes 28 s against
   the refuting copy's 10 s kill, so run there it could only use up the time
   the refutation needs.  A stage that only proves reads [refutation_only] and
   is skipped while it is set.  A plain reference: set it only in a forked
   copy, or around work no other domain runs meanwhile. *)
let refutation_only = ref false

let with_refutation_only f =
  let saved = !refutation_only in
  refutation_only := true;
  Common.Timer.protect ~finally:(fun () -> refutation_only := saved) f

let shape_form phi =
  Ast.Evaluator.abstract_seq_reads_and_functions
  @@ Ast.Evaluator.with_shape_rewrites (fun () ->
         Ast.Evaluator.elim_onepoint_and_split_binders phi)

(* The closure's reach: two steps, the second through variables occurring
   in at most 30 disjuncts.  Measured on the two loop-body obligations of
   [univariant_sat] (about 1,200 disjuncts each, the contract of every earlier
   iteration among them): one step leaves out the premise that fixes the
   field's offset (a countermodel), three steps or a bound of 70 bring in
   enough copies of the contract that Z3 does not decide the question in
   30 s, and the bound 12 leaves out one premise of the two-step closure. *)
let dump_count = Atomic.make 0
let closure_hops = 2
let closure_k = 30

let valid_within ?(print = fun (_ : string lazy_t) -> ()) ?(fork = true)
    ?(literal_closures = (0, 0)) ~ms ~id phi =
  let tried what r =
    print
    @@ lazy
         (sprintf "shape proof (%s): %s" what
            (match r with
            | `Valid -> "valid"
            | `Timeout -> "timeout"
            | `Unknown r -> "unknown " ^ r
            | `Invalid _ -> "invalid"));
    (* one phase-report event per form asked, [shape-proof/WHAT/OUTCOME]; an
       instrument that decides nothing *)
    Common.PhaseTime.event_here
      (sprintf "shape-proof/%s/%s" what
         (match r with
         | `Valid -> "valid"
         | `Timeout -> "timeout"
         | `Unknown _ -> "unknown"
         | `Invalid _ -> "invalid"));
    match r with `Valid -> true | _ -> false
  in
  (* the rewritten and weakened form, built once in this process (the
     rewrite is a bounded number of passes over the formula) *)
  let form = lazy (shape_form phi) in
  let ask ?(what = "") ~ms question =
    let run () =
      match Lazy.force question with
      | None -> `Unknown "nothing to drop"
      | Some q -> (
          (* [COAR_DUMP_SHAPE_PROOF=dir] (instrument only): each form asked is
             recorded as [dir/qN-PID] with its outcome in [dir/index.tsv] and
             its name in [dir/forms.tsv], an undecided one written out as its
             negation ([..._native.smt2]); the answer is unchanged *)
          (match Sys.getenv "COAR_DUMP_SHAPE_PROOF" with
          | Some dir ->
              Out_channel.with_file (dir ^ "/forms.tsv") ~append:true
                ~f:(fun oc ->
                  Out_channel.output_string oc
                    (sprintf "q%d-%d\t%s\t%d\n" (Atomic.get dump_count)
                       (Common.ForkGuard.self_pid ()) what
                       (List.length (Formula.disjuncts_list_of q))))
          | None -> ());
          match
            Z3Smt.Z3interface.with_validity_dump ~var:"COAR_DUMP_SHAPE_PROOF"
              ~counter:dump_count ~id ~timeout:ms
              ~outcome:(function
                | `Valid -> "valid"
                | `Invalid _ -> "invalid"
                | _ -> "undecided")
              (Z3Smt.Z3interface.fenv_reached_by (get_fenv ()) q)
              q
            @@ fun () ->
            (* only the definitions the form reaches are declared: the
               abstraction has replaced every applied defined function, and
               a recursive definition declared in the context, used or not,
               can slow Z3 on the form (measured on a loop body's closure:
               proved in 17 s asked from its file and in 35 s in a solver
               run declaring only what it reaches, undecided at 30 s and at
               90 s in runs that declared the input's two recursive
               functions).  Omitting a definition removes constraints, so a
               proof stays a proof *)
            Z3Smt.Z3interface.check_valid ~timeout:(Some ms) ~fresh_solver:true ~id
              (Z3Smt.Z3interface.fenv_reached_by (get_fenv ()) q)
              q
          with
          | `Valid -> `Valid
          | `Invalid _ -> `Invalid ()
          | `Timeout -> `Timeout
          | `Unknown r -> `Unknown r
          | `Sat _ | `Unsat -> `Unknown "unexpected answer")
    in
    if fork then
      ForkedQuery.valid_within ~ms (fun () ->
          match run () with `Invalid () -> `Unknown "invalid" | r -> r)
    else
      try run ()
      with exn_ when not (Common.Timer.is_async exn_) ->
        `Unknown (Exn.to_string exn_)
  in
  tried "whole" (ask ~what:"whole" ~ms (lazy (Some (Lazy.force form))))
  || List.exists [ (true, 8); (false, 8); (false, 16); (false, 32) ]
       ~f:(fun (linked, k) ->
         let ms' = Int.max 1 (ms / 2) in
         tried
           (sprintf "%sk=%d" (if linked then "linked, " else "") k)
           (ask ~what:(sprintf "k=%d%s" k (if linked then " linked" else "")) ~ms:ms'
              (lazy
                (Ast.Evaluator.relevant_premises ~linked ~k (Lazy.force form)))))
  ||
  let max, ms' = literal_closures in
  max > 0
  && List.existsi
       (Ast.Evaluator.literal_closures ~k:closure_k ~hops:closure_hops ~max
          (Lazy.force form))
       ~f:(fun i q ->
         print
         @@ lazy
              (sprintf "shape proof: literal closure %d, size %d" i
                 (Formula.ast_size q));
         tried "literal closure"
           (ask ~what:(sprintf "closure %d" i) ~ms:ms' (lazy (Some q))))
