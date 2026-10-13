(* The order of the zero-unknown verdict's two early stages and the budget of
   its whole-conjunction questions.  The verdict asks, when preprocessing
   leaves no predicate variable, whether the remaining constraints are valid
   by a ladder of questions; this module holds the two decisions about that
   ladder that are pure functions of the configuration and of what the ladder
   has learned so far, so that they can be checked without a solver.

   The two early stages are
   - [Early_pins]: the sequence-length, point and relation pins, which read
     only a model of a strengthened negation (a refutation) and never a proof;
   - [Exact_forms]: each clause not yet shown valid asked in its exactly
     rewritten form, piece by piece, then the sequence instantiation, which
     read a refutation only from an exact rewrite and otherwise only a proof.
   and, ahead of both when asked for,
   - [Cheap_pins]: the one pin question whose cost the problem's shape bounds
     ([SeqPin.cheap_first]), which also reads only a refutation;
   - [Raced_pins]: the [Early_pins] stage started in a forked copy that
     answers only with a refutation, while this process goes on with the
     exact forms, so that neither stage waits for the other;
   - [Point_pin]: the point pin alone (one of the three [Early_pins]),
     under a budget of its own, which also reads only a refutation.
   Each stage is sound on its own, so whichever decides first decides the
   answer the other would have reached, if it reached one: running them in
   either order changes when an answer is reached within the run's time, and
   which questions are asked before it, never which answer is right. *)
open Core

type early_stage =
  | Raced_pins
  | Cheap_pins
  | Point_pin
  | Early_pins
  | Exact_forms

(* [early_order ~pins_after_exact ?cheap_pins_first ?pins_raced
   ?point_pin_first ()] is the order the early stages are run in: the pins
   first (the order before this option existed) unless [pins_after_exact],
   and then, with [cheap_pins_first], the cheap pin question before the exact
   forms, and with [point_pin_first] the point pin alone ([Point_pin],
   [early_point_pin_first_no_unknown_query]) after it and before the exact
   forms.  With [pins_after_exact] and [pins_raced], [Raced_pins] comes first
   of all: the stage that starts the early pins in a forked copy racing the
   rest of the ladder ([early_pins_raced_no_unknown_query]); the
   [pins_after_exact] order follows it unchanged, [Early_pins] included, so
   the race adds an earlier chance of the pins' refutation and takes nothing
   from the sequential run.
   Contract: without the three optional flags the result is a permutation of
   [[Early_pins; Exact_forms]], with [Early_pins] first exactly when
   [pins_after_exact] is false; each optional stage occurs exactly when its
   flag and [pins_after_exact] hold, [Raced_pins] first, then [Cheap_pins],
   then [Point_pin], all before [Exact_forms]; the rest is the
   [pins_after_exact] order, [Exact_forms] then [Early_pins].  Every optional
   stage is a part of the pins put earlier, pointless before the pins
   themselves, so a flag alone changes nothing. *)
let early_order ?(cheap_pins_first = false) ?(pins_raced = false)
    ?(point_pin_first = false) ~pins_after_exact () =
  if pins_after_exact then
    (if pins_raced then [ Raced_pins ] else [])
    @ (if cheap_pins_first then [ Cheap_pins ] else [])
    @ (if point_pin_first then [ Point_pin ] else [])
    @ [ Exact_forms; Early_pins ]
  else [ Early_pins; Exact_forms ]

(* Whether the point pin, run alone before the exact forms ([Point_pin]),
   searched everything the point pin of the later [Early_pins] stage would
   search, so that the later one may be left out.

   The later point pin searches the clauses not shown valid by then, a subset
   of those open when [Point_pin] ran (the exact forms only add clauses shown
   valid), piece by piece in the same order, with the same per-question cap
   and the same number of guesses per relaxation; a point is proved only by a
   validity question at that point.  So when [Point_pin] went through every
   piece of every open clause (no clause, piece or guess left out because its
   budget ran out or its point count was reached: [search_complete]) and gave
   every question the whole per-question cap (its budget, read after the
   search, still offers [per_query]: the remaining budget only shrinks, so it
   offered every earlier question at least that), the later pin would search
   the same pieces again, differing only in the points the solver's models
   happen to suggest.  Leaving it out forgoes that second draw and nothing
   else: the late pins at the end of the ladder, which are not affected,
   still search every open clause with their own budget.

   [point_pin_searched_all ~search_complete ~next_budget ~per_query] is
   [search_complete && next_budget = Some per_query].  Contract: true only
   when both hold; a [false] keeps the later point pin, which is the order
   without the stage.  Each pin reads only a refutation, so leaving one out
   changes when an answer is reached, never which answer. *)
let point_pin_searched_all ~search_complete ~next_budget ~per_query =
  search_complete
  && match next_budget with Some b -> b = per_query | None -> false

(* [first_decided order ~run] runs the stages of [order] one at a time, in
   order, and returns the first [Some] answer, running no stage after it.
   Contract: [run] is called on a prefix of [order], each stage at most once;
   the result is [None] exactly when every stage of [order] was run and
   returned [None].  An exception (a [Common.Timer] timeout among them) leaves
   through it unchanged. *)
let first_decided order ~run = List.find_map order ~f:run

(* [conj_timeout ~cap ~early_ran ~default] is the budget in milliseconds of a
   whole-conjunction question of the ladder (the conjunction, the conjunction
   with its single-constructor binders opened, and the conjunction of the
   rewritten clauses not yet shown valid).  [early_ran] says whether the
   exact-forms stage ran before it and left the problem undecided, which is
   when the conjunction is the same question the stage has just failed to
   settle piece by piece; [default] is the ladder's per-question budget.
   Contract: the result is [default] unless [cap = Some ms] and [early_ran],
   and then it is [min ms default], so a cap can only shorten a question and
   never lengthen one; a non-positive cap gives a non-positive budget, which
   the caller must treat as "do not ask" ([ask_conj]). *)
let conj_timeout ~cap ~early_ran ~default =
  match cap with
  | Some ms when early_ran -> Int.min ms default
  | _ -> default

(* [ask_conj ~timeout ~ask phi] asks [phi] under [timeout], or answers
   [`Timeout] without asking when [timeout <= 0].  Contract: [ask] is called
   at most once, with [timeout], and only when [timeout > 0]; an unasked
   question is reported as one that ran out of its budget, which the ladder
   reads as undecided, as it reads every answer but [`Valid] and
   [`Invalid _] from these questions. *)
let ask_conj ~timeout ~ask phi = if timeout <= 0 then `Timeout else ask timeout phi

(* [lazy_budget ~now (per_query, whole)] is the [(within, expired)] pair of a
   budget of [whole] milliseconds whose clock starts at the FIRST call of
   either function, not when the pair is built, with [now] the clock in
   seconds.  [within ()] is the budget of the next question: [None] once
   [whole] milliseconds have elapsed since the start, otherwise
   [Some (min per_query left)] with [left > 0] the milliseconds remaining;
   [expired ()] holds exactly when [within ()] is [None].  Contract: every
   [Some b] has [0 < b <= per_query] and [b <= whole]; the sum of the budgets
   of questions asked back to back, each taking its whole budget, does not
   exceed [whole] by more than the time between the calls; and with
   [whole <= 0] nothing is ever within.  Built so that one stage of a ladder
   can be given a budget of its own that an earlier stage cannot spend. *)
let lazy_budget ~now (per_query, whole) =
  let start = ref None in
  let deadline () =
    match !start with
    | Some d -> d
    | None ->
        let d = now () +. (Float.of_int whole /. 1000.) in
        start := Some d;
        d
  in
  let within () =
    let d = deadline () in
    let left = Float.iround_down_exn ((d -. now ()) *. 1000.) in
    if left <= 0 then None else Some (Int.min per_query left)
  in
  let expired () = Option.is_none (within ()) in
  (within, expired)

(* [cpu_budget ~now ~cpu ~max_scale (per_query, whole)] is [lazy_budget]'s
   [(within, expired)] pair with the budget charged by the CPU time [cpu] (in
   seconds) of the thread doing the work instead of by the wall clock [now]
   (in seconds); both clocks start at the first call of either function.
   Wanted where the work's wall time grows with the machine's load and its
   CPU time does not: on a loaded machine each question, and the forced
   collection before each new solver context, takes a multiple of its CPU
   time in wall time, so a wall-clock budget is spent on the waiting.

   [within ()] is [None] once [whole] milliseconds of CPU time have been
   spent since the start, or once [max_scale *. whole] milliseconds of wall
   time have elapsed (a bound on how long the whole stage can take however
   loaded the machine is).  Otherwise it is the wall-clock cap of the next
   question, which a solver can only be given in wall time: the CPU budget
   [min per_query left] multiplied by the slowdown observed so far, the wall
   time elapsed over the CPU time spent since the start, clamped to
   [[1, max_scale]] and taken as 1 until [min_cpu_spent] seconds of CPU time
   have been spent (too little to measure a ratio by).  [expired ()] holds
   exactly when [within ()] is [None].  Contract: every [Some b] has
   [1 <= b <= max_scale *. per_query] (rounded down, at least 1); with
   [whole <= 0] nothing is ever within; and with [cpu] advancing as [now]
   does (an idle machine) the caps are those of [lazy_budget], to within
   [min_cpu_spent]'s rounding. *)
(* the CPU time of the calling thread, in seconds; the process's user and
   system time where the thread clock is not available.  A solver check runs
   in the thread that asks it, so its work is counted. *)
let thread_cpu_seconds =
  match Core_unix.Clock.gettime with
  | Ok gettime ->
      fun () -> Int63.to_float (gettime Core_unix.Clock.Process_thread) /. 1e9
  | Error _ ->
      fun () ->
        let t = Core_unix.times () in
        t.tms_utime +. t.tms_stime

let min_cpu_spent = 0.1

let cpu_budget ~now ~cpu ~max_scale (per_query, whole) =
  let start = ref None in
  let origin () =
    match !start with
    | Some o -> o
    | None ->
        let o = (now (), cpu ()) in
        start := Some o;
        o
  in
  let within () =
    let w0, c0 = origin () in
    let spent = cpu () -. c0 in
    let elapsed = now () -. w0 in
    let whole_s = Float.of_int whole /. 1000. in
    let left = Float.iround_down_exn ((whole_s -. spent) *. 1000.) in
    if left <= 0 || Float.(elapsed >= max_scale *. whole_s) then None
    else
      let scale =
        if Float.(spent < min_cpu_spent) then 1.
        else Float.max 1. (Float.min max_scale (elapsed /. spent))
      in
      Some
        (Int.max 1
           (Float.iround_down_exn (Float.of_int (Int.min per_query left) *. scale)))
  in
  let expired () = Option.is_none (within ()) in
  (within, expired)

(* [quick_sweep ~finish_started_clause ~past_deadline ~pieces_of ~ask
   ~mark_valid ~on_piece ~on_refuted clauses] is the ladder's first stage:
   every clause of [clauses], piece by piece ([pieces_of]), asked by [ask] at a
   short budget, stopping at the first refutation.  A clause all of whose
   pieces [ask] answers [`Valid] is recorded by [mark_valid i] (its index);
   [on_piece i p] is called before [p] is asked and [on_refuted i] when it
   refutes clause [i].
   The sweep has a whole budget, read by [past_deadline]: no clause is started
   past it.  Inside a clause, without [finish_started_clause] the deadline cuts
   the clause at the next piece, and the pieces already shown valid are lost,
   since only a whole clause is recorded.  With [finish_started_clause] a
   clause started before the deadline is asked to its end while every piece so
   far is valid -- the clause can still be recorded -- and cut at the first
   piece past the deadline once one piece was left undecided.  Why: one tuple
   variable split into its fields turned the 36 pieces of a residual clause
   into 60, six of which take the per-question budget plus the sequence-axiom
   fallback (about 1 s each), so the sweep's 5 s ran out a few pieces before
   the clause's end, and the later stages, which ask the clause whole or
   rewritten, needed 40 s more for what these pieces would have recorded in
   3 s.  The cost past the deadline is at most one clause's remaining pieces,
   each bounded by [ask]'s own budget.
   Contract: [ask] is called on pieces in order, never on a piece of a clause
   not started before the deadline; [mark_valid i] is called exactly when every
   piece of clause [i] was asked and answered [`Valid]; the result is
   [Some (`Invalid m)] for the first piece answered [`Invalid m], after which
   nothing is asked, and [None] otherwise.  With the deadline never passed the
   switch changes nothing; past it, the switch only adds questions, each one
   [ask] would put to the same piece, so an answer it reads is one of [ask]'s. *)
let quick_sweep ~finish_started_clause ~past_deadline ~pieces_of ~ask
    ~mark_valid ~on_piece ~on_refuted clauses =
  List.find_mapi clauses ~f:(fun i c ->
      if past_deadline () then None
      else
        let rec go all_valid = function
          | [] ->
              if all_valid then mark_valid i;
              None
          | p :: rest -> (
              if past_deadline () && not (finish_started_clause && all_valid)
              then None
              else (
                on_piece i p;
                match ask p with
                | `Invalid model ->
                    on_refuted i;
                    Some (`Invalid model)
                | `Valid -> go all_valid rest
                | _ -> go false rest))
        in
        go true (pieces_of c))
