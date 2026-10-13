(* Three mechanisms in this subsystem are switched off in every shipped
   configuration -- the index/value cells, the QSAT clause-constraint route
   and the quantifier-prefix synthesis -- and some definitions have no caller
   at all.  Three markers
   say which code is which, and every one of them carries the reason it is
   where it is:

     REACHABLE ON THE DEFAULT PATH -- executes in an ordinary run; the comment
       states what it evaluates to there, which in every case is "no change".
     UNREACHABLE BY DEFAULT (<mechanism>) -- runs only when that mechanism's
       field is set.
     PORTED, UNCALLED -- no caller at all.

   DUBIOUS marks code that is kept without being endorsed: a defect preserved
   deliberately so that unexercised code is not quietly "repaired", a
   heuristic whose constants nothing explains, a printer used as a
   serialiser.  Those are the ones to argue about first. *)

open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* Every check call of this module goes through these two, so that the
   phase-time account ([Common.PhaseTime], off by default) can say how much of
   each phase was spent inside Z3. *)
(* With [COAR_Z3_LAST=path] in the environment, every check first writes its
   solver's assertions to [path], replacing what was there; when a run is
   stopped inside a Z3 call that does not return, [path] holds that call's
   question, whichever entry point asked it ([COAR_Z3_LAST_STACK] set too
   appends the OCaml call stack that asked, as comments).  [COAR_DUMP_Z3] prints every
   question of [check_sat] as it goes; this keeps only the last one, and also
   sees solvers driven directly, such as the synthesizer's. *)
(* A caller that wants the questions of one of its calls kept as files sets
   [with_query_dump prefix f]: every check made by [f] in the calling domain
   writes its solver's assertions to [prefix_k.smt2] (k counting from 0 within
   the call) before asking, and appends the answer, Z3's reason for an
   undecided one and the wall-clock seconds as a comment after.  A diagnostic
   for replaying a question outside the context that asked it; nothing is
   written unless a caller asks. *)
let query_dump : (string * int ref) option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_query_dump prefix f =
  let saved = Stdlib.Domain.DLS.get query_dump in
  Stdlib.Domain.DLS.set query_dump (Some (prefix, ref 0));
  Fun.protect
    ~finally:(fun () -> Stdlib.Domain.DLS.set query_dump saved)
    f

let z3_check solver exprs =
  (match Sys.getenv "COAR_Z3_LAST" with
   | Some path ->
       Out_channel.write_all path
         ~data:
           (Z3.Solver.to_string solver ^ "\n;; assumptions\n"
           ^ String.concat ~sep:"\n" (List.map exprs ~f:Z3.Expr.to_string)
           ^ "\n(check-sat)\n"
           ^
           match Sys.getenv "COAR_Z3_LAST_STACK" with
           | None -> ""
           | Some _ ->
               ";; asked from\n"
               ^ String.concat_map_list ~sep:"\n"
                   (String.split_lines
                      (Stdlib.Printexc.raw_backtrace_to_string
                         (Stdlib.Printexc.get_callstack 80)))
                   ~f:(fun l -> ";; " ^ l)
               ^ "\n")
   | None -> ());
  match Stdlib.Domain.DLS.get query_dump with
  | None -> Common.PhaseTime.z3 (fun () -> Z3.Solver.check solver exprs)
  | Some (prefix, k) ->
      let path = sprintf "%s_%d.smt2" prefix !k in
      incr k;
      Out_channel.write_all path
        ~data:
          ("(set-logic ALL)\n" ^ Z3.Solver.to_string solver
          ^ String.concat
              (List.map exprs ~f:(fun e ->
                   "(assert " ^ Z3.Expr.to_string e ^ ")\n"))
          ^ "(check-sat)\n");
      let started = Common.Clock.now_float () in
      let status =
        Common.PhaseTime.z3 (fun () -> Z3.Solver.check solver exprs)
      in
      let secs =
        Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) started)
      in
      Out_channel.with_file path ~append:true ~f:(fun oc ->
          Out_channel.output_string oc
            (sprintf "; answer: %s%s in %.3f s\n"
               (match status with
               | Z3.Solver.SATISFIABLE -> "sat"
               | Z3.Solver.UNSATISFIABLE -> "unsat"
               | Z3.Solver.UNKNOWN -> "unknown")
               (match status with
               | Z3.Solver.UNKNOWN ->
                   " (" ^ Z3.Solver.get_reason_unknown solver ^ ")"
               | _ -> "")
               secs));
      status

let z3_opt_check optimizer =
  Common.PhaseTime.z3 (fun () -> Z3.Optimize.check optimizer)

(* Whether integers that are bit-vectors in disguise are handed to Z3 as
   bit-vectors: the rewrite of bounded words in [check_sat]
   ([int_to_bv_range_subst] below) and, in the conversion of every term, the
   collapse of [int_to_bv n (ubv_to_int x)] for an [x] of width [n] to [x].
   Process-wide, off by default. *)
let int_to_bv_range = Atomic.make false
let set_int_to_bv_range b = Atomic.set int_to_bv_range b

(* With [int_to_bv_range] on, also move [int2bv n] into a remainder by a
   power of two ([push_int2bv]); a separate switch so that it can be judged on
   its own. *)
let int_to_bv_mod_pow2 = Atomic.make false
let set_int_to_bv_mod_pow2 b = Atomic.set int_to_bv_mod_pow2 b

(* With [int_to_bv_range] on, also give each bounded integer of a question a
   bit-vector name and each of its top-level integer literals a bit-vector
   twin ([int_to_bv_twins_subst]); a separate switch, off by default. *)
let int_to_bv_twins = Atomic.make false
let set_int_to_bv_twins b = Atomic.set int_to_bv_twins b

(* [int_to_bv_pow2_shifts]: in the translation of bounded integer arithmetic
   to bit-vectors ([int_to_bv_twins_subst], the words questions among its
   users), a [div] or [mod] by a positive power of two [2^k] is written with
   shifts and a mask instead of [bvudiv]/[bvsdiv]/[bvurem]/[bvsrem]: the
   floor quotient of a two's complement value is its arithmetic shift right
   by [k], its Euclidean remainder its low [k] bits ([bvand] with [2^k - 1]),
   and the truncated quotient the shift of the value plus [2^k - 1] where it
   is negative.  Exact at every value the translation admits (each value lies
   within the signed range of the width, so no step wraps).  Why: a division
   circuit is bit-blasted in full, and a words question whose negative-index
   branches kept two [bvsdiv] and four [bvsrem] by 64 at width 72 was decided
   in 21-24 s or not within 30 s, where the questions without them took under
   a second; a shift by a constant is wiring.  A separate switch, off by
   default. *)
let int_to_bv_pow2_shifts = Atomic.make false
let set_int_to_bv_pow2_shifts b = Atomic.set int_to_bv_pow2_shifts b

let verbose = false

module Debug =
  Debug.Make ((val Debug.Config.(if verbose then enable else disable)))

let dump_z3_queries = Stdlib.(Sys.getenv_opt "COAR_DUMP_Z3" <> None)

(* Print, per query, the instance it runs on and the sort of every free variable
   it mentions, so that a name used at two sorts in one instance can be found.

   Why that is worth finding: the instances are POOLED and an instance's context
   accumulates the declarations of every query that ran on it, so a model
   describes symbols the current query never mentioned.  A consumer that looks an
   entry up by name then gets a value of a sort it never asked about.  That is a
   repaired defect; what is not understood is why two queries on one instance use
   one name at two sorts in the first place, and this is the cheapest way to see
   the pair.

   Off unless the environment asks, like the query dump above.  Post-process with
   something that groups the lines by instance and name and reports a name with
   more than one sort. *)
let dump_query_sorts = Stdlib.(Sys.getenv_opt "COAR_DUMP_QUERY_SORTS" <> None)

let print_query_sorts ~id phis =
  if dump_query_sorts then
    List.iter phis ~f:(fun phi ->
        Set.iter (Formula.term_sort_env_of phi) ~f:(fun (x, srt) ->
            print_endline
            @@ sprintf "[query-sort] id=%s %s : %s"
                 (match id with None -> "-" | Some i -> string_of_int i)
                 (Ident.name_of_tvar x) (Term.str_of_sort srt)))

let debug_print_z3_input phis =
  Debug.print @@ lazy "Z3 input formulas:";
  List.iter phis ~f:(fun phi -> Debug.print @@ lazy (Formula.str_of phi))

let debug_print_z3_model model =
  Debug.print @@ lazy ("Z3 output model: " ^ str_of_model model)

let validate = false
let validate_cfg = [ ("model_validate", "true"); ("well_sorted_check", "true") ]

(* let _ = Z3.set_global_param "smt.macro_finder" "true" *)

(* Environments *)
type dtenv = (Datatype.t * Z3.Sort.sort) Set.Poly.t
type fenv = (Ident.tvar, Z3.FuncDecl.func_decl) Map.Poly.t

(* For concurrency control *)
let mutex = Caml_threads.Mutex.create ()
let enable_mutex = false
let lock () = if enable_mutex then Caml_threads.Mutex.lock mutex
let unlock () = if enable_mutex then Caml_threads.Mutex.unlock mutex

(* Solver pool *)
let enable_solver_pool = true

type instance = {
  ctx : Z3.context;
  solver : Z3.Solver.solver;
  goal : Z3.Goal.goal;
  cfg : (string * string) list;
  mutable dtenv : dtenv;
  mutable fenv : fenv;
  mutable uses : int;
      (** questions this context has answered as a clean-pool context
          ([lease_clean_instance]); 0 elsewhere *)
}

(* the pool is one Hashtbl shared by every solver domain (keys differ per
   domain, but the table itself is not safe for concurrent mutation); guard the
   table operations — not the Z3 work — with their own mutex *)
let pool_mutex = Caml_threads.Mutex.create ()

let with_pool_lock f =
  Caml_threads.Mutex.lock pool_mutex;
  match f () with
  | v ->
      Caml_threads.Mutex.unlock pool_mutex;
      v
  | exception e ->
      Caml_threads.Mutex.unlock pool_mutex;
      raise e

(* A Z3 context's memory is released only when the OCaml value holding it is
   finalised, and the collector does not see that memory, so contexts dropped
   after one question pile up unless a collection is forced; a full major
   collection before every new context is what keeps them from doing so.  Its
   cost grows with the live OCaml heap, and on a run that asks hundreds of
   fresh-context questions over a large heap it was a sixth of the run.
   [new_context_full_major_every n] forces it before every n-th new context
   only (1, the default, before each), bounding the contexts left waiting for
   the collector by n.  Process-wide, written once when a solver configuration
   that asks for it is loaded. *)
let new_context_full_major_every = Atomic.make 1
let new_contexts = Atomic.make 0

let set_new_context_full_major_every n =
  Atomic.set new_context_full_major_every (Int.max 1 n)

(* [with_new_context_full_major_every n f] runs [f] with the forced collection
   made before every n-th new context only, in the calling domain, whatever
   the process-wide setting is, and restores the setting on return and on
   raise.  For a stage that asks many small fresh-context questions over a
   large heap, where the collection costs more than the questions: at most n
   dropped contexts then wait for the collector at once.  The questions asked
   are the same; only the collector's timing changes. *)
let full_major_every_override : int option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_new_context_full_major_every n f =
  let saved = Stdlib.Domain.DLS.get full_major_every_override in
  Stdlib.Domain.DLS.set full_major_every_override (Some (Int.max 1 n));
  Fun.protect
    ~finally:(fun () -> Stdlib.Domain.DLS.set full_major_every_override saved)
    f

(* A collection trigger by heap growth instead of a context count.

   [set_new_context_full_major_bytes (Some b)] makes the forced collection
   before a new context depend on how many bytes the program has allocated in
   the OCaml major heap (promoted words included; [Gc.quick_stat]'s
   [major_words], which is process-wide and sampled at the last minor
   collection) since the last forced collection: it is made exactly when that
   growth is at least [b] bytes, and before the first context of the process
   (or the first after the switch is set), which has no last collection.
   While it is set it replaces the count rules: the process-wide
   [new_context_full_major_every], a stage's [with_new_context_full_major_every
   n] and the sequence-axiom fallback's every-n thinning all defer to it.  The
   one exception is an override of [Int.max_value], which keeps meaning "no
   collection here" (a forked copy that lives for one question).  [None], the
   default, leaves the count rules as they are.

   Why: the count rule's cost is one full collection per n contexts whatever
   the heap does, so a run that makes many small contexts over a small heap
   pays for collections it does not need, and a run whose heap grows fast lets
   n contexts wait however large they are.  Under the byte rule a run with
   little allocation between contexts collects rarely, and one that allocates
   much collects in time.  What it does not bound is the number of dropped
   contexts waiting for the collector, whose memory is outside the OCaml heap:
   a run that makes contexts and allocates little lets them accumulate until
   the threshold or a natural major cycle releases them.  The questions asked
   are the same; only the collector's timing changes (and with it, possibly,
   the identifiers in a Z3 model).  Process-wide, written once when a solver
   configuration that asks for it is loaded. *)
let new_context_full_major_bytes : int option Atomic.t = Atomic.make None

(* the [major_words] reading taken right after the last forced collection
   ([Float.nan] before the first one under the byte rule) *)
let major_words_at_last_full_major = Atomic.make Float.nan

(* process-wide count of collections forced before a new context, for the
   phase report and tests *)
let new_context_full_majors = Atomic.make 0

let set_new_context_full_major_bytes b =
  Atomic.set new_context_full_major_bytes (Option.map b ~f:(Int.max 1));
  Atomic.set major_words_at_last_full_major Float.nan

(* [full_major_due_by_bytes ~threshold ~last ~now]: [last] and [now] are
   [major_words] readings (words); due when there is no last reading or the
   growth in bytes reaches [threshold] *)
let word_bytes = Float.of_int (Stdlib.Sys.word_size / 8)

let full_major_due_by_bytes ~threshold ~last ~now =
  Float.is_nan last || Float.((now - last) * word_bytes >= of_int threshold)

let current_major_words () = (Gc.quick_stat ()).major_words

(* [COAR_GC_BYTES_LOG] set: one stderr line per new context with the growth
   since the last forced collection, the major heap's size and the process's
   resident set, for choosing a threshold *)
let gc_bytes_log = Stdlib.(Sys.getenv_opt "COAR_GC_BYTES_LOG" <> None)

let rss_mb () =
  try
    let line = In_channel.read_all "/proc/self/statm" in
    match String.split ~on:' ' line with
    | _ :: res :: _ -> Int.of_string res * 4096 / 1_048_576
    | _ -> -1
  with exn when not (Common.Timer.is_async exn) -> -1

(* A collection trigger for a caller that drops whole native contexts in
   bursts (the template synthesizer replaces its contexts on every qualifier
   search and template rebuild): [full_major_if_resident_grew ()] forces a full
   major collection exactly when the process's resident set has grown by at
   least [resident_growth_mb] megabytes over the lowest reading taken since
   the last such collection, before the first call, and whenever the resident
   set cannot be read.

   Why the resident set and not a count: the memory at stake is the dropped
   contexts' native heaps, which neither a context count nor the OCaml heap's
   size sees, and which the resident set does.  A forced collection before
   every new context bounded that memory but cost a full stop-the-world
   collection per context: on a three-clause optimisation problem 38 of them
   took 13-17 s of a 28-40 s run with three domains on a loaded machine (each
   0.3-0.45 s), and the per-predicate maps of contexts forced one collection
   per predicate in a row, the second and later collecting nothing new.  Under
   the growth rule a burst of contexts that allocates little collects once,
   and a run whose dropped contexts do pile up still collects each time they
   reach the threshold, so the resident overshoot stays bounded by the
   threshold plus what one context creation allocates.  The questions asked
   are the same; only the collector's timing changes.
   [COAR_SYNTH_GC_RESIDENT_MB] overrides the threshold (0 restores a
   collection on every call) and [COAR_SYNTH_GC_LOG] prints one stderr line
   per call, both for measuring. *)
let resident_growth_mb =
  match Stdlib.Sys.getenv_opt "COAR_SYNTH_GC_RESIDENT_MB" with
  | Some s -> (
      match Int.of_string_opt (String.strip s) with
      | Some n -> Int.max 0 n
      | None -> 128)
  | None -> 128

let synth_gc_log = Stdlib.(Sys.getenv_opt "COAR_SYNTH_GC_LOG" <> None)

(* the lowest resident reading (MB) since the last forced collection, -1
   before the first *)
let resident_mb_since_full_major = Atomic.make (-1)

(* process-wide count of the collections [full_major_if_resident_grew] forced *)
let resident_full_majors = Atomic.make 0

(* [full_major_due_by_resident ~threshold_mb ~low_mb ~now_mb]: due when either
   reading is missing (negative) or the growth over the low reading reaches
   the threshold *)
let full_major_due_by_resident ~threshold_mb ~low_mb ~now_mb =
  now_mb < 0 || low_mb < 0 || now_mb - low_mb >= threshold_mb

let full_major_if_resident_grew () =
  let now = rss_mb () in
  let low = Atomic.get resident_mb_since_full_major in
  let due =
    full_major_due_by_resident ~threshold_mb:resident_growth_mb ~low_mb:low
      ~now_mb:now
  in
  if synth_gc_log then
    Stdlib.Printf.eprintf "synthgc rss_mb=%d low_mb=%d forced=%d\n%!" now low
      (if due then 1 else 0);
  if due then (
    Common.PhaseTime.with_phase "gc-full-major" Gc.full_major;
    Atomic.incr resident_full_majors;
    Atomic.set resident_mb_since_full_major (rss_mb ()))
  else if now < low then Atomic.set resident_mb_since_full_major now

let get_instance =
  let new_instance cfg =
    Caml_threads.Mutex.lock mutex;
    (let k = Atomic.fetch_and_add new_contexts 1 in
     let override = Stdlib.Domain.DLS.get full_major_every_override in
     let due =
       match (override, Atomic.get new_context_full_major_bytes) with
       | Some n, _ when n = Int.max_value -> k = 0
       | _, Some threshold ->
           full_major_due_by_bytes ~threshold
             ~last:(Atomic.get major_words_at_last_full_major)
             ~now:(current_major_words ())
       | Some n, None -> k % n = 0
       | None, None -> k % Atomic.get new_context_full_major_every = 0
     in
     if gc_bytes_log then
       Stdlib.Printf.eprintf
         "gcbytes ctx=%d forced=%d grow_mb=%.1f heap_mb=%d rss_mb=%d\n%!" k
         (if due then 1 else 0)
         (let last = Atomic.get major_words_at_last_full_major in
          if Float.is_nan last then -1.
          else
            Float.((current_major_words () - last) * word_bytes / 1_048_576.))
         ((Gc.quick_stat ()).heap_words * (Stdlib.Sys.word_size / 8)
         / 1_048_576)
         (rss_mb ());
     (* both marked for the phase report, which then counts the contexts made
        under each phase and the time the forced collections took there *)
     if due then (
       Common.PhaseTime.with_phase "gc-full-major" Gc.full_major;
       Atomic.incr new_context_full_majors;
       Atomic.set major_words_at_last_full_major (current_major_words ())));
    let ctx, solver, goal =
      Common.PhaseTime.with_phase "new-context" @@ fun () ->
      let ctx = Z3.mk_context cfg in
      ( ctx,
        Z3.Solver.mk_solver ctx None,
        Z3.Goal.mk_goal ctx false false false )
    in
    let dtenv = Set.Poly.empty in
    let fenv = Map.Poly.empty in
    Caml_threads.Mutex.unlock mutex;
    { ctx; solver; goal; dtenv; fenv; cfg; uses = 0 }
  in
  fun (id : int option) cfg instance_pool ->
    if not enable_solver_pool then new_instance cfg
    else
      match
        with_pool_lock (fun () -> Hashtbl.Poly.find instance_pool (id, cfg))
      with
      | None -> new_instance cfg
      | Some instance -> instance

let back_instance ~reset instance_pool id instance =
  if enable_solver_pool then (
    reset instance;
    with_pool_lock (fun () ->
        Hashtbl.Poly.set instance_pool ~key:(id, instance.cfg) ~data:instance))

let instance_pool = Hashtbl.Poly.create ()

(* ------------------------------------------------------------------
   Clean contexts, reused through [Z3.Solver.reset].

   A question that must not lose a quantified decision is asked in a context
   of its own ([check_sat ~fresh_solver:true], the sequence-axiom fallback),
   because Z3's default solver answers quantified goals with its incremental
   core alone -- without the preprocessing that decides them -- in a context
   whose solver has been pushed or that holds a recursive function definition.
   Making a context is cheap (about 6 ms); what costs is the forced full major
   collection before it ([new_context_full_major_every]), which on a run of a
   hundred such questions over a few hundred MB of heap was a fifth of the
   wall time.

   With [clean_reset_pool] on, such a question leases a CLEAN context instead:
   one whose solver has never been pushed and in which no recursive function
   has ever been declared.  Measured with Z3 5.1.0 on a satisfiable quantified
   goal decided by a fresh context in 7 of 16 identifier shifts: a context that
   had answered earlier quantifier-free and quantified questions, reset,
   decided 7 of 16 as well, while one that had held a [define-fun-rec], reset,
   decided none.  So:
   - a leased context is used without [push] and is [reset] before it returns;
   - a question that declares a recursive function in it ([z3_fenv_of]
     declares every function of its environment as one) never returns it: the
     context is dropped, as every fresh context is today;
   - a question that raises never returns it either (the solver may be in the
     middle of a check);
   - a context is retired after [clean_pool_max_uses] questions, so that the
     terms of earlier questions, which Z3 releases only when the collector
     finalises their OCaml handles, cannot pile up in one long-lived context
     without bound; its replacement is made by [get_instance], with that
     path's forced collection;
   - datatypes declared in a context stay declared and are reused by full name
     ([instance.dtenv]), as in every pooled instance: the datatypes a run uses
     are fixed before solving, and a stage that substitutes them clears this
     pool with the others ([clear_instance_pool]).
   What a reset does NOT keep is the effect of an earlier attempt at the same
   question: a quantifier-free question undecided in 5 s in a solver of its
   own was decided in 0.03 s when asked again in a new scope of the solver
   that had tried it for 100 ms or more inside push/pop, and after a reset (or
   in a second solver of the context, or by checking the same assertions
   again) it was not.  A fresh context loses that too, so the pool loses
   nothing a fresh context had.

   The pool is keyed by the instance id, the context configuration and the
   arithmetic solver the question asks for (that parameter is fixed when a
   solver's core is first set up, so solvers asked with different ones are not
   mixed).  A lease removes the context from the pool, so two domains never
   share one; at most [clean_pool_per_key] wait per key.  Off by default:
   [lease_clean_instance] is then [get_instance] on an empty table, which is
   exactly the fresh context it replaces, and [release_clean_instance] does
   nothing. *)
let clean_reset_pool = Atomic.make false
let set_clean_reset_pool b = Atomic.set clean_reset_pool b
let clean_pool_max_uses = Atomic.make 64
let set_clean_pool_max_uses n = Atomic.set clean_pool_max_uses (Int.max 1 n)
let clean_pool_per_key = 4

(* process-wide counts, for the report and for tests: leases served from the
   pool, leases that made a context, contexts returned, and contexts dropped
   because a recursive function was declared in them, because the question
   raised, because they had served [clean_pool_max_uses] questions, or because
   [clean_pool_per_key] already waited *)
let clean_pool_hits = Atomic.make 0
let clean_pool_misses = Atomic.make 0
let clean_pool_returned = Atomic.make 0
let clean_pool_dropped_rec = Atomic.make 0
let clean_pool_dropped_raised = Atomic.make 0
let clean_pool_dropped_uses = Atomic.make 0
let clean_pool_dropped_full = Atomic.make 0

type clean_key = int option * (string * string) list * int option

let clean_pool : (clean_key, instance list) Hashtbl.Poly.t =
  Hashtbl.Poly.create ()

let lease_clean_instance ~arith id cfg =
  if not (Atomic.get clean_reset_pool) then
    get_instance id cfg (Hashtbl.Poly.create ())
  else
    let key = (id, cfg, arith) in
    let taken =
      (* marked for the phase report, whose count is then the leases made
         with the pool on; the leases it could not serve are the contexts
         made, counted by [new-context] *)
      Common.PhaseTime.with_phase "clean-pool-lease" @@ fun () ->
      with_pool_lock (fun () ->
          match Hashtbl.Poly.find clean_pool key with
          | Some (inst :: rest) ->
              Hashtbl.Poly.set clean_pool ~key ~data:rest;
              Some inst
          | _ -> None)
    in
    match taken with
    | Some inst ->
        Atomic.incr clean_pool_hits;
        inst
    | None ->
        Atomic.incr clean_pool_misses;
        get_instance id cfg (Hashtbl.Poly.create ())

(* [reusable]: the question neither raised nor declared a recursive function
   in the context.  The caller must not use [inst] afterwards. *)
let release_clean_instance ~arith ~reusable id inst =
  if Atomic.get clean_reset_pool then (
    inst.uses <- inst.uses + 1;
    let uses = inst.uses in
    let rec_declared = not (Map.Poly.is_empty inst.fenv) in
    if rec_declared then Atomic.incr clean_pool_dropped_rec
    else if not reusable then Atomic.incr clean_pool_dropped_raised
    else if uses >= Atomic.get clean_pool_max_uses then
      Atomic.incr clean_pool_dropped_uses
    else (
      Z3.Solver.reset inst.solver;
      let kept =
        with_pool_lock (fun () ->
            let key = (id, inst.cfg, arith) in
            let waiting =
              Option.value ~default:[] (Hashtbl.Poly.find clean_pool key)
            in
            if List.length waiting >= clean_pool_per_key then false
            else (
              Hashtbl.Poly.set clean_pool ~key ~data:(inst :: waiting);
              true))
      in
      if kept then Atomic.incr clean_pool_returned
      else Atomic.incr clean_pool_dropped_full))

let clean_pool_report () =
  sprintf
    "(z3-clean-reset-pool (on %b) (hits %d) (misses %d) (returned %d) \
     (dropped-rec %d) (dropped-raised %d) (dropped-uses %d) (dropped-full %d))"
    (Atomic.get clean_reset_pool)
    (Atomic.get clean_pool_hits)
    (Atomic.get clean_pool_misses)
    (Atomic.get clean_pool_returned)
    (Atomic.get clean_pool_dropped_rec)
    (Atomic.get clean_pool_dropped_raised)
    (Atomic.get clean_pool_dropped_uses)
    (Atomic.get clean_pool_dropped_full)

(* Z3 sort name -> [T_dt.SUS (name, params)] for uninterpreted sorts,
   so that distinct declarations and instantiations get distinct Z3 sorts and decode back;
   guarded by [pool_mutex] like [instance_pool] *)
let sus_instances : (string, Sort.t) Hashtbl.Poly.t = Hashtbl.Poly.create ()

(* Drop every pooled instance, so that the next query starts from a context
   that has declared nothing.  An instance ACCUMULATES its declarations -- a
   datatype already declared there under a given name is reused rather than
   redeclared -- so a stage that replaces a sort inside a datatype while
   keeping the datatype's NAME leaves every pooled instance holding the old
   field sorts, and the first term built over the new ones is rejected outright
   ("supplied sort is ..." against the constructor's declared argument).  The
   sorts a run uses are fixed before any solving begins, so nothing on the
   ordinary path needs this; it is for a stage that substitutes them. *)
let clear_instance_pool () =
  with_pool_lock (fun () ->
      Hashtbl.Poly.clear instance_pool;
      Hashtbl.Poly.clear clean_pool;
      Hashtbl.Poly.clear sus_instances)

(* Z3 sequence sorts by the name Z3 prints for them, so that a sequence value
   coming back from a model decodes to the right element sort.  It has to be a
   table because the OCaml binding exposes no accessor for a sequence sort's
   element, and the sort kind alone cannot tell [(Seq Int)] from [String] --
   in Z3 a string IS a sequence, of characters.  Written where the sort is
   encoded, read where a model is decoded; guarded by [pool_mutex] like the
   table above. *)
let seq_instances : (string, Sort.t) Hashtbl.Poly.t = Hashtbl.Poly.create ()

(* A display name is not a sort identity: [S<int>] may itself be a legal
   declared name, and an uninterpreted sort named [int] prints like [SInt].
   Tag each sort constructor and preserve name/parameter boundaries instead.
   Datatypes are identified by their declared name and parameters, not by
   expanding their potentially recursive selector graph. *)
let rec sus_sort_key sort =
  let node tag fields = Sexp.List (Sexp.Atom tag :: fields) in
  let atom s = Sexp.Atom s in
  match sort with
  | Sort.SVar (Ident.Svar name) -> node "var" [ atom name ]
  | Sort.SArrow (arg, result) ->
      node "arrow" [ sus_sort_key arg; sus_comp_key result ]
  | Sort.SPoly (vars, body) ->
      node "poly"
        [
          Sexp.List
            (List.map (Set.to_list vars) ~f:(fun var ->
                 atom (Ident.name_of_svar var)));
          sus_sort_key body;
        ]
  | T_bool.SBool -> node "bool" []
  | T_int.SInt -> node "int" []
  | T_real.SReal -> node "real" []
  | T_bv.SBV size -> node "bv" [ atom (T_bv.str_of_size size) ]
  | T_string.SString -> node "string" []
  | T_regex.SRegEx -> node "regex" []
  | T_trace.STrace fin -> node "trace" [ atom (Bool.to_string fin) ]
  | T_seq.SSeq elem -> node "seq" [ sus_sort_key elem ]
  | T_array.SArray (index, elem) ->
      node "array" [ sus_sort_key index; sus_sort_key elem ]
  | T_tuple.STuple elems -> node "tuple" (List.map elems ~f:sus_sort_key)
  | T_dt.SUS (name, params) ->
      node "uninterpreted" (atom name :: List.map params ~f:sus_sort_key)
  | T_dt.SDT dt ->
      node
        (match Datatype.flag_of dt with Undef -> "uninterpreted" | _ -> "datatype")
        (atom (Datatype.name_of dt)
        :: List.map (Datatype.params_of dt) ~f:sus_sort_key)
  | T_int.SRefInt -> node "ref-int" []
  | T_ref.SRef elem -> node "ref" [ sus_sort_key elem ]
  | _ -> failwith "[z3:sus_sort_key] unsupported sort parameter"

and sus_comp_key (comp : Sort.c) =
  Sexp.List
    [ sus_opsig_key comp.op_sig; sus_sort_key comp.val_type; sus_effect_key comp.cont_eff ]

and sus_opsig_key = function
  | Sort.OpSig (ops, tail) ->
      Sexp.List
        [
          Sexp.List
            (List.map (Common.Util.ALMap.to_alist ops) ~f:(fun (name, sort) ->
                 Sexp.List [ Sexp.Atom name; sus_sort_key sort ]));
          Sexp.List
            (Option.to_list
               (Option.map tail ~f:(fun var -> Sexp.Atom (Ident.name_of_rvar var))));
        ]
  | _ -> failwith "[z3:sus_sort_key] unsupported operation signature"

and sus_effect_key = function
  | Sort.Pure -> Sexp.List [ Sexp.Atom "pure" ]
  | Sort.EVar var ->
      Sexp.List [ Sexp.Atom "var"; Sexp.Atom (Ident.name_of_evar var) ]
  | Sort.Eff (before, after) ->
      Sexp.List [ Sexp.Atom "effect"; sus_comp_key before; sus_comp_key after ]
  | _ -> failwith "[z3:sus_sort_key] unsupported continuation effect"

(* Encode every declaration, including a nullary one, so no legal user name
   can impersonate a generated name. Hex is injective over the tagged key and
   avoids depending on the quoting rules of a solver's printed symbols. *)
let z3_name_of_sus name params =
  let sort = T_dt.SUS (name, params) in
  let z3name =
    "#sus_"
    ^ String.concat_map (Sexp.to_string (sus_sort_key sort)) ~f:(fun c ->
          sprintf "%02x" (Char.to_int c))
  in
  with_pool_lock (fun () ->
      Hashtbl.Poly.set sus_instances ~key:z3name ~data:sort);
  z3name

let clean () =
  (* Hashtbl.Poly.clear cache; *)
  with_pool_lock (fun () -> Hashtbl.Poly.clear instance_pool)

(** decoding *)

let unint_svar_prefix = "#svar_"
let unint_arrow_prefix = "#arrow_"
let unint_is_cons_prefix = "#is_"
let unint_tuple_prefix = "#tuple"
let unint_tuple_sel_prefix = "#t_sel."
let unint_epsilon = "#epsilon"
let unint_symbol_prefix = "#symbol_"
let unint_concat_fin = "#concat_fin"
let unint_concat_inf = "#concat_inf"
let unint_is_prefix_of_fin = "#is_prefix_of_fin"
let unint_is_prefix_of_inf = "#is_prefix_of_inf"
let unint_is_in_reg_exp_fin_prefix = "#is_in_reg_exp_fin"
let unint_is_in_reg_exp_inf_prefix = "#is_in_reg_exp_inf"
let unint_unsupported = "unsupported"
let unint_fintrace = "#fin_trace"
let unint_inftrace = "#inf_trace"
let unescape_z3 = String.substr_replace_all ~pattern:"|" ~with_:"" (*ToDo*)

(* The suffix a solving instance puts on every name it hands to Z3, and the only
   code that reads it back.  Both directions live here because they are one
   format, and they were written apart once: the encoder appended, three readers
   each undid it separately, and all three undid it wrongly.

   A name becomes [name ++ separator ++ id-in-decimal ++ the sort's short name].
   Undoing that by splitting on the separator and keeping the first piece is not
   its inverse: a name the input itself declares may contain the separator, and
   two such declarations then come back as one.  A file declaring [x] and
   [x__separator__y] produced the model [x |-> 5, x |-> 7] -- two values for one
   name, and the second declaration gone.

   So [decode] removes the sort's short name and then the digits, in that order,
   and only where both are there.  Taking the digits first would be wrong for a
   sort whose short name begins with one, which a datatype named by a quoted
   SMT-LIB symbol can be.

   What the format cannot express is a name that already ends in a valid suffix
   for its own sort: [x__separator__7i] declared by the input decodes to [x].
   The encoder has no escape, so that is a property of the format and not of the
   reader, and removing it needs a change on both sides. *)
module InstanceName = struct
  let separator = "__separator__"

  let encode ~id ~sort name =
    sprintf "%s%s%d%s" name separator id (Term.short_name_of_sort sort)

  let decode ~sort name =
    match String.chop_suffix name ~suffix:(Term.short_name_of_sort sort) with
    | None -> name
    | Some without_sort -> (
        match
          List.rev @@ Str.split_delim (Str.regexp_string separator) without_sort
        with
        | digits :: (_ :: _ as rest)
          when (not (String.is_empty digits))
               && String.for_all digits ~f:Char.is_digit ->
            String.concat ~sep:separator @@ List.rev rest
        | _ -> name)
end

let divide_str = InstanceName.separator

(* let var_of s =
   Scanf.unescaped (try Scanf.sscanf s "|%s@|" Fn.id with _ -> s)
   |> Str.split (Str.regexp divide_str)
   |> List.hd_exn *)

(* the Z3 operator of an application, [None] for numerals, bound variables and
   quantifiers *)
let decl_kind_opt expr =
  try Some (Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl expr))
  with exn_ when not (Common.Timer.is_async exn_) -> None

(* [push_int2bv ctx n e] is a Z3 bit-vector term equal to [int2bv n e] for an
   integer term [e], with the conversion moved inside sums, differences,
   negations and products and onto integer numerals, and dropped where it
   meets [bv2int] (or its signed form) of a width-[n] term.  Each step is exact
   because [int2bv n] is the ring homomorphism from the integers onto the
   integers modulo [2^n]: [int2bv n (a + b) = bvadd (int2bv n a) (int2bv n b)],
   likewise for [-] and [*], and [int2bv n (bv2int x) = x] since [bv2int x]
   is [x]'s value (or that value less [2^n]).  Z3 5.1.0 decides neither
   identity by itself: a two-variable query reading a bit of
   [int2bv 64 (1 + x)] and one reading a bit of
   [int2bv 64 (bv2int (bvor c (bvshl 1 y)))] each ran past 30 s, and each is
   answered in under half a second once rewritten.  A remainder [mod a 2^k]
   by a power of two (Z3's [mod], which is Euclidean, so its value is the low
   [k] bits of [a] for every integer [a]) becomes the low [k] bits of the
   pushed [a] when [k < n], [bvand (int2bv n a) (2^k - 1)], and the pushed
   [a] itself when [k >= n], since [2^n] divides [2^k]; that is the shape of a
   shift amount [i % 64] read as a word.  A term of any other shape keeps its
   [int2bv]. *)
let rec push_int2bv ctx n e =
  let args () = Z3.Expr.get_args e in
  let fold f = function
    | [] -> Z3.Arithmetic.Integer.mk_int2bv ctx n e
    | a :: rest ->
        List.fold rest ~init:(push_int2bv ctx n a) ~f:(fun acc b ->
            f ctx acc (push_int2bv ctx n b))
  in
  if Z3.Arithmetic.is_int_numeral e then
    Z3.BitVector.mk_numeral ctx
      (Z.to_string
         (Z.erem
            (Z.of_string (Z3.Arithmetic.Integer.numeral_to_string e))
            (Z.shift_left Z.one n)))
      n
  else
    match decl_kind_opt e with
    | Some Z3enums.OP_ADD -> fold Z3.BitVector.mk_add (args ())
    | Some Z3enums.OP_SUB -> fold Z3.BitVector.mk_sub (args ())
    | Some Z3enums.OP_MUL -> fold Z3.BitVector.mk_mul (args ())
    | Some Z3enums.OP_UMINUS -> (
        match args () with
        | [ a ] -> Z3.BitVector.mk_neg ctx (push_int2bv ctx n a)
        | _ -> Z3.Arithmetic.Integer.mk_int2bv ctx n e)
    | Some Z3enums.OP_MOD when Atomic.get int_to_bv_mod_pow2 -> (
        match args () with
        | [ a; b ] when Z3.Arithmetic.is_int_numeral b -> (
            let d = Z.of_string (Z3.Arithmetic.Integer.numeral_to_string b) in
            let k = Z.log2 d in
            if Z.(gt d one) && Z.equal d (Z.shift_left Z.one k) then
              if k >= n then push_int2bv ctx n a
              else
                Z3.BitVector.mk_and ctx (push_int2bv ctx n a)
                  (Z3.BitVector.mk_numeral ctx
                     (Z.to_string (Z.pred d))
                     n)
            else Z3.Arithmetic.Integer.mk_int2bv ctx n e)
        | _ -> Z3.Arithmetic.Integer.mk_int2bv ctx n e)
    | Some (Z3enums.OP_BV2INT | Z3enums.OP_SBV2INT) -> (
        match args () with
        | [ x ]
          when Z3.BitVector.is_bv x
               && Z3.BitVector.get_size (Z3.Expr.get_sort x) = n ->
            x
        | _ -> Z3.Arithmetic.Integer.mk_int2bv ctx n e)
    | _ -> Z3.Arithmetic.Integer.mk_int2bv ctx n e

let is_decl_kind expr kinds =
  match decl_kind_opt expr with
  | Some k -> List.mem kinds k ~equal:Stdlib.( = )
  | None -> false

let rec sort_of z3_dtenv s =
  if false then print_endline @@ "converting " ^ Z3.Sort.to_string s;
  match Z3.Sort.get_sort_kind s with
  | Z3enums.UNINTERPRETED_SORT -> (
      let name = Z3.Symbol.get_string @@ Z3.Sort.get_name s in
      if String.is_prefix ~prefix:unint_svar_prefix name then
        let svar =
          String.sub name
            ~pos:(String.length unint_svar_prefix)
            ~len:(String.length name - String.length unint_svar_prefix)
        in
        Sort.SVar (Ident.Svar svar)
      else if String.is_prefix ~prefix:unint_arrow_prefix name then (
        let s =
          String.sub name
            ~pos:(String.length unint_arrow_prefix)
            ~len:(String.length name - String.length unint_arrow_prefix)
        in
        let c =
          (* ToDo: assuming that LogicOld.ref_dtenv is properly set *)
          (*LogicOld.update_dtenv dtenv;
            if false then
              print_endline @@ sprintf "datatype env:\n%s" @@ DTEnv.str_of dtenv;*)
          RtypeParser.comp_ty RtypeLexer.token (Lexing.from_string s)
            Map.Poly.empty (*ToDo*)
        in
        if false then
          print_endline
          @@ sprintf "parsed %s from %s"
               (Rtype.str_of_comp ~config:!Rtype.cgen_config c)
               s;
        Rtype.sort_of_comp c)
      else if String.(name = unint_unsupported) then failwith "not supported"
      else if String.(name = unint_fintrace) then T_trace.STrace true
      else if String.(name = unint_inftrace) then T_trace.STrace false
      else
        match
          with_pool_lock (fun () -> Hashtbl.Poly.find sus_instances name)
        with
        | Some sort -> sort
        | None -> T_dt.SUS (name, []))
  | Z3enums.BOOL_SORT -> T_bool.SBool
  | Z3enums.INT_SORT -> T_int.SInt
  | Z3enums.REAL_SORT -> T_real.SReal
  | Z3enums.BV_SORT -> T_bv.SBV (Some (Z3.BitVector.get_size s))
  | Z3enums.ARRAY_SORT ->
      T_array.SArray
        ( sort_of z3_dtenv @@ Z3.Z3Array.get_domain s,
          sort_of z3_dtenv @@ Z3.Z3Array.get_range s )
  | Z3enums.DATATYPE_SORT -> (
      match Set.find z3_dtenv ~f:(snd >> Stdlib.( = ) s) with
      | Some (dt, _) -> T_dt.SDT dt
      | _ ->
          if
            String.is_prefix ~prefix:unint_tuple_prefix
            @@ unescape_z3 @@ Z3.Sort.to_string s
          then
            T_tuple.STuple
              (List.map ~f:(Z3.FuncDecl.get_range >> sort_of z3_dtenv)
              @@ Z3.Tuple.get_field_decls s)
          else failwith @@ "[z3:sort_of] unknown dt type:" ^ Z3.Sort.to_string s
      )
  | Z3enums.RELATION_SORT -> failwith "RELATION_SORT not supported"
  | Z3enums.FINITE_DOMAIN_SORT -> failwith "FINITE_DOMAIN_SORT not supported"
  | Z3enums.FLOATING_POINT_SORT -> failwith "FLOATING_POINT_SORT not supported"
  | Z3enums.ROUNDING_MODE_SORT -> failwith "ROUNDING_MODE_SORT not supported"
  | Z3enums.SEQ_SORT -> (
      (* Z3's string sort is a sequence of characters, so the kind does not
         separate the two; the name does, and a sequence this tool encoded is
         registered under it. *)
      match
        with_pool_lock (fun () ->
            Hashtbl.Poly.find seq_instances @@ Z3.Sort.to_string s)
      with
      | Some sort -> sort
      | None ->
          if String.(Z3.Sort.to_string s = "String") then T_string.SString
          else
            (* a sequence sort this tool did not encode.  Answering with the
               string sort -- which is what this branch did unconditionally
               while [(Seq s)] could not be parsed at all, and was harmless
               exactly because of that -- would silently give the term a sort
               with no length, concatenation or indexing. *)
            failwith
            @@ sprintf "[z3:sort_of] unregistered sequence sort: %s"
            @@ Z3.Sort.to_string s)
  | Z3enums.RE_SORT -> T_regex.SRegEx
  | Z3enums.CHAR_SORT -> failwith "CHAR_SORT not supported"
  | Z3enums.UNKNOWN_SORT ->
      if String.(Z3.Sort.to_string s = "Proof") then
        Sort.SVar (Ident.Svar "Proof") (*ToDo*)
      else
        failwith @@ "[z3:sort_of] UNKNOWN_SORT not supported:"
        ^ Z3.Sort.to_string s
  | Z3enums.TYPE_VAR -> failwith "TYPE_VAR not supported"

let look_up_func_of_dt dt sort func =
  if Datatype.is_undef dt then `Unkonwn
  else
    let verbose = false in
    if verbose then
      Debug.print
      @@ lazy
           (sprintf "[look_up_func] finding (#%d) %s in %s"
              (Z3.FuncDecl.get_id func)
              (Z3.FuncDecl.to_string func)
              (Z3.Sort.to_string sort));
    let id = Z3.FuncDecl.get_id func in
    let z3_conses = Z3.Datatype.get_constructors sort in
    let z3_selss = Z3.Datatype.get_accessors sort in
    let z3_testers = Z3.Datatype.get_recognizers sort in
    let z3_funcs = List.zip3_exn z3_conses z3_testers z3_selss in
    List.fold2_exn (Datatype.conses_of dt) z3_funcs ~init:`Unkonwn
      ~f:(fun ret cons (z3_cons, z3_tester, z3_sels) ->
        match ret with
        | `Unkonwn ->
            if id = Z3.FuncDecl.get_id z3_cons then (
              if verbose then Debug.print @@ lazy "constructor found";
              `Cons cons)
            else if id = Z3.FuncDecl.get_id z3_tester then (
              if verbose then Debug.print @@ lazy "tester found";
              `IsCons cons)
            else
              List.fold2_exn (Datatype.sels_of_cons cons) z3_sels ~init:ret
                ~f:(fun ret sel z3_sel ->
                  if verbose then
                    Debug.print
                    @@ lazy
                         (sprintf "search_sel %d =? (#%d) %s" id
                            (Z3.FuncDecl.get_id z3_sel)
                            (Z3.FuncDecl.to_string z3_sel));
                  match ret with
                  | `Unkonwn ->
                      if id = Z3.FuncDecl.get_id z3_sel then (
                        if verbose then Debug.print @@ lazy "selector found";
                        `Sel sel)
                      else ret
                  | _ -> ret)
        | _ -> ret)

let look_up_func dtenv func =
  Set.find_map dtenv ~f:(fun (dt, sort) ->
      match look_up_func_of_dt dt sort func with
      | `Unkonwn -> None
      | ret -> Some (dt, ret))

let parse_root_obj = function
  | Sexp.List [ Sexp.Atom "root-obj"; t; n ] ->
      let rec parse_term = function
        | Sexp.Atom "x" -> Term.mk_var (Ident.Tvar "x") T_real.SReal
        | Sexp.Atom ident -> (
            (*try T_int.mk_int (Z.of_string ident) with _ ->*)
            try T_real.mk_real (Q.of_string ident)
            with exn_ when not (Common.Timer.is_async exn_) ->
              failwith "[z3:parse_term]")
        | Sexp.List [ Sexp.Atom "-"; t ] ->
            T_real.mk_rneg (*ToDo*) (parse_term t)
        | Sexp.List (Sexp.Atom "+" :: arg :: args) ->
            List.fold args ~init:(parse_term arg) ~f:(fun acc t ->
                T_real.mk_radd (*ToDo*) acc (parse_term t))
        | Sexp.List (Sexp.Atom "*" :: arg :: args) ->
            List.fold args ~init:(parse_term arg) ~f:(fun acc t ->
                T_real.mk_rmul (*ToDo*) acc (parse_term t))
        | Sexp.List [ Sexp.Atom "^"; t1; t2 ] ->
            T_real.mk_rpower (*ToDo*) (parse_term t1) (parse_term t2)
        | _ -> failwith "[z3:parse_term]"
      in
      let t = parse_term t in
      (t, int_of_string @@ Sexp.to_string n)
  | e ->
      failwith @@ "[z3:parse_root_obj]" ^ Sexp.to_string e ^ " is not root-obj"

(* [free_const_names_of dtenv body] is the names a free constant of the Z3
   expression [body] decodes to, and [fresh_binder_avoiding names senv ~prefix]
   the name a decoded binder is given: [Ident.mk_fresh_tvar ~prefix] drawn again
   while the name is in [names] or already in the decoding environment [senv].
   Why: a Z3 binder is a de Bruijn index and comes back as its symbol followed
   by a process-global counter, which is fresh against the names this process
   has drawn and NOT against the names the input spells.  A free constant [x3]
   in the body of a lambda whose symbol is [x] decoded, once the counter stood
   at 3, to the very variable the lambda binds -- a capture that silently
   changes the term.  Contract: the result is in neither [names] nor [senv];
   with no collision it is the first draw, so the name and the counter advance
   are exactly those of one [Ident.mk_fresh_tvar] call.
   The walk visits each shared Z3 node once (Z3 terms are DAGs, so a naive
   recursion is exponential on them) and records a constant under both its raw
   spelling and the name [term_of] decodes it to; that over-approximates what
   the body can contribute and costs at most an extra draw. *)
let free_const_names_of dtenv body =
  let seen = Hash_set.create (module Int) in
  let names = Hash_set.create (module String) in
  let rec walk e =
    let ast = Z3.Expr.ast_of_expr e in
    let id = Z3.AST.get_id ast in
    if not (Hash_set.mem seen id) then (
      Hash_set.add seen id;
      if Z3.AST.is_var ast then ()
      else if Z3.AST.is_quantifier ast then
        walk @@ Z3.Quantifier.get_body @@ Z3.Quantifier.quantifier_of_expr e
      else if Stdlib.(Z3.AST.get_ast_kind ast = Z3enums.APP_AST) then
        match Z3.Expr.get_args e with
        | [] -> (
            match decl_kind_opt e with
            | Some Z3enums.OP_UNINTERPRETED -> (
                let func = Z3.Expr.get_func_decl e in
                let raw =
                  unescape_z3 @@ Z3.Symbol.get_string
                  @@ Z3.FuncDecl.get_name func
                in
                Hash_set.add names raw;
                try
                  Hash_set.add names
                  @@ InstanceName.decode
                       ~sort:(sort_of dtenv @@ Z3.FuncDecl.get_range func)
                       raw
                with exn_ when not (Common.Timer.is_async exn_) -> ())
            | _ -> ())
        | args -> List.iter args ~f:walk)
  in
  walk body;
  names

let fresh_binder_avoiding names (senv : sort_env_list) ~prefix =
  Ident.mk_fresh_tvar_avoiding ~prefix
    ~taken:(fun x ->
      Hash_set.mem names (Ident.name_of_tvar x)
      || List.exists senv ~f:(fun (y, _) -> Ident.tvar_equal x y))
    ()

(* raised past the term decoder's own [Failure] handlers, which would otherwise
   turn the refusal into a free function symbol *)
exception Unsupported_bool_application of string

(* Is [expr] -- a [to_int] -- the encoder's spelling of an integer power, that
   is, [to_int] applied to a [^] whose two arguments are integer-sorted? *)
let is_int_power_arg expr =
  match Z3.Expr.get_args expr with
  | [ pw ] ->
      is_decl_kind pw Z3enums.[ OP_POWER ]
      && List.for_all (Z3.Expr.get_args pw) ~f:(fun e ->
          Stdlib.(
            Z3.Sort.get_sort_kind (Z3.Expr.get_sort e) = Z3enums.INT_SORT))
  | _ -> false

(* The regular expression each trace-membership predicate name was made from.
   The encoder spells [T_trace.TrInRegExp (fin, r)] as an uninterpreted
   predicate whose NAME carries [r]'s printed form, and that form cannot be
   parsed back unambiguously: a symbol is printed bare, so a symbol named "eps"
   and the empty word print alike.  So the encoder records here which
   expression each name was made from, and the decoder reads it back by name;
   a name this process never encoded, or one two different expressions
   printed to, is refused rather than guessed.  Guarded by a mutex because
   encoders run in several domains. *)
let trace_regexps : (string, string Grammar.RegWordExp.t list) Hashtbl.Poly.t =
  Hashtbl.Poly.create ()

let trace_regexps_mutex = Caml_threads.Mutex.create ()

let with_trace_regexps f =
  Caml_threads.Mutex.lock trace_regexps_mutex;
  Exn.protect ~f ~finally:(fun () ->
      Caml_threads.Mutex.unlock trace_regexps_mutex)

let record_trace_regexp name regexp =
  with_trace_regexps (fun () ->
      Hashtbl.Poly.update trace_regexps name ~f:(function
        | None -> [ regexp ]
        | Some rs ->
            if List.mem rs regexp ~equal:Stdlib.( = ) then rs
            else regexp :: rs))

let trace_regexp_of_name name =
  match with_trace_regexps (fun () -> Hashtbl.Poly.find trace_regexps name) with
  | Some [ r ] -> r
  | Some _ ->
      failwith
      @@ sprintf
           "[z3:term_of] %s names more than one regular expression (they print alike), so the membership cannot be decoded"
           name
  | None ->
      failwith
      @@ sprintf
           "[z3:term_of] %s is a trace-membership name this process did not encode, so its regular expression is unknown"
           name

let is_trace_pred_name name =
  List.exists
    [
      unint_is_in_reg_exp_fin_prefix;
      unint_is_in_reg_exp_inf_prefix;
      unint_is_prefix_of_fin;
      unint_is_prefix_of_inf;
    ]
    ~f:(fun prefix -> String.is_prefix name ~prefix)

(* the trace predicates the encoder spells as uninterpreted names, decoded
   from the name and the decoded arguments; [None] when [name] is not one *)
let trace_atom_of_name name ts =
  let bad () =
    failwith
    @@ sprintf "[z3:term_of] %s applied to %d arguments" name (List.length ts)
  in
  if String.is_prefix name ~prefix:unint_is_in_reg_exp_fin_prefix then
    match ts with
    | [ t ] ->
        Some (T_trace.mk_is_in_regexp true (trace_regexp_of_name name) t)
    | _ -> bad ()
  else if String.is_prefix name ~prefix:unint_is_in_reg_exp_inf_prefix then
    match ts with
    | [ t ] ->
        Some (T_trace.mk_is_in_regexp false (trace_regexp_of_name name) t)
    | _ -> bad ()
  else if String.is_prefix name ~prefix:unint_is_prefix_of_fin then
    match ts with
    | [ t1; t2 ] -> Some (T_trace.mk_is_prefix true t1 t2)
    | _ -> bad ()
  else if String.is_prefix name ~prefix:unint_is_prefix_of_inf then
    match ts with
    | [ t1; t2 ] -> Some (T_trace.mk_is_prefix false t1 t2)
    | _ -> bad ()
  else None

let rec apply ctx senv penv dtenv op expr =
  match List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr with
  | e :: es -> List.fold ~init:e es ~f:op
  | _ -> assert false

and apply_uop ctx senv penv dtenv op expr =
  match Z3.Expr.get_args expr with
  | [ e1 ] -> op (term_of ctx senv penv dtenv e1)
  | _ -> assert false

and apply_urel ctx senv penv dtenv op expr =
  match Z3.Expr.get_args expr with
  | [ e1 ] -> op (term_of ctx senv penv dtenv e1)
  | _ -> assert false

and apply_bop ctx senv penv dtenv op expr =
  match Z3.Expr.get_args expr with
  | [ e1; e2 ] ->
      op (term_of ctx senv penv dtenv e1) (term_of ctx senv penv dtenv e2)
  | _ -> assert false

(* Z3 flattens n-ary applications *)
and apply_nop ctx senv penv dtenv op expr =
  match Z3.Expr.get_args expr with
  | e1 :: (_ :: _ as rest) ->
      List.fold rest ~init:(term_of ctx senv penv dtenv e1) ~f:(fun acc e ->
          op acc (term_of ctx senv penv dtenv e))
  | _ -> assert false

and apply_brel ctx senv penv dtenv op expr =
  match Z3.Expr.get_args expr with
  | [ e1; e2 ] ->
      op (term_of ctx senv penv dtenv e1) (term_of ctx senv penv dtenv e2)
  | _ -> assert false

(* Conversion from Z3 expressions to terms *)
(* [as_atom] is set by [atom_of] when it hands an application it has no case
   for to the term decoder.  The term decoder's own fallback for a Bool-valued
   application it does not know is to retry it as a formula, and the formula
   decoder hands a non-connective to [atom_of]: without the flag the three would
   pass one expression around until the stack is exhausted.  With it, each
   direction tries the other at most once, and an application neither knows
   raises "unsupported Z3 operator" naming it. *)
and term_of ?(as_atom = false) ctx (senv : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (dtenv : dtenv)
    expr =
  Debug.print @@ lazy (sprintf "[z3:term_of] %s" @@ Z3.Expr.to_string expr);
  if Z3.Boolean.is_true expr then T_bool.mk_true ()
  else if Z3.Boolean.is_false expr then T_bool.mk_false ()
  else if Z3.Boolean.is_ite expr then
    match Z3.Expr.get_args expr with
    | [ e1; e2; e3 ] ->
        T_bool.ifte
          (formula_of ctx senv penv dtenv e1)
          (term_of ctx senv penv dtenv e2)
          (term_of ctx senv penv dtenv e3)
    | _ -> failwith @@ "[z3:term_of] " ^ Z3.Expr.to_string expr
  else if Z3.Arithmetic.is_int_numeral expr then
    T_int.mk_int @@ Z3.Arithmetic.Integer.get_big_int expr
  else if Z3.Arithmetic.is_rat_numeral expr then
    T_real.mk_real @@ Z3.Arithmetic.Real.get_ratio expr
  else if Z3.Arithmetic.is_algebraic_number expr then
    let t, n = parse_root_obj @@ Sexp.of_string @@ Z3.Expr.to_string expr in
    T_real.mk_alge t n
  else if Z3.Arithmetic.is_uminus expr then
    (* Z3 has one unary minus for both arithmetic sorts; the sort of the
       application says which negation it is *)
    match sort_of dtenv @@ Z3.Expr.get_sort expr with
    | T_real.SReal -> apply_uop ctx senv penv dtenv T_real.mk_rneg expr
    | _ -> apply_uop ctx senv penv dtenv T_int.mk_neg expr
  else if Z3.Arithmetic.is_int2real expr then
    apply_uop ctx senv penv dtenv T_irb.mk_int_to_real expr
  else if Z3.Arithmetic.is_real2int expr && is_int_power_arg expr then
    (* the encoder's integer power: Z3's [^] has sort Real even when both
       arguments are integers, so [of_term] writes [T_int.Power] as
       [to_int (^ x n)] to keep it integer-valued, and this is its inverse *)
    match Z3.Expr.get_args expr with
    | [ pw ] -> apply_bop ctx senv penv dtenv T_int.mk_power pw
    | _ -> assert false
  else if Z3.Arithmetic.is_real2int expr then
    apply_uop ctx senv penv dtenv T_irb.mk_real_to_int expr
  else if is_decl_kind expr Z3enums.[ OP_POWER ] then
    (* an integer-sorted power, should a Z3 ever give one that sort, is the
       integer power; a real-sorted one is the real power *)
    match sort_of dtenv @@ Z3.Expr.get_sort expr with
    | T_int.SInt -> apply_bop ctx senv penv dtenv T_int.mk_power expr
    | _ -> apply_bop ctx senv penv dtenv T_real.mk_rpower expr
  else if Z3.Arithmetic.is_add expr then
    match sort_of dtenv @@ Z3.Expr.get_sort expr with
    | T_int.SInt -> apply ctx senv penv dtenv T_int.mk_add expr
    | T_real.SReal -> apply ctx senv penv dtenv T_real.mk_radd expr
    | _ ->
        failwith @@ "[z3:term_of]" ^ Z3.Sort.to_string @@ Z3.Expr.get_sort expr
  else if Z3.Arithmetic.is_sub expr then
    match sort_of dtenv @@ Z3.Expr.get_sort expr with
    | T_int.SInt -> apply ctx senv penv dtenv T_int.mk_sub expr
    | T_real.SReal -> apply ctx senv penv dtenv T_real.mk_rsub expr
    | _ ->
        failwith @@ "[z3:term_of]" ^ Z3.Sort.to_string @@ Z3.Expr.get_sort expr
  else if Z3.Arithmetic.is_mul expr then
    match sort_of dtenv @@ Z3.Expr.get_sort expr with
    | T_int.SInt -> apply ctx senv penv dtenv T_int.mk_mul expr
    | T_real.SReal -> apply ctx senv penv dtenv T_real.mk_rmul expr
    | _ ->
        failwith @@ "[z3:term_of] " ^ Z3.Sort.to_string @@ Z3.Expr.get_sort expr
  else if Z3.Arithmetic.is_idiv expr then
    apply_bop ctx senv penv dtenv (T_int.mk_div Value.Euclidean) expr
  else if Z3.Arithmetic.is_div expr then
    apply_bop ctx senv penv dtenv T_real.mk_rdiv expr
  else if Z3.Arithmetic.is_modulus expr then
    apply_bop ctx senv penv dtenv (T_int.mk_rem Value.Euclidean) expr
  else if Z3.Arithmetic.is_remainder expr then
    (* z3 rem is not Euclidean mod (https://github.com/Z3Prover/z3/issues/6462) *)
    match Z3.Expr.get_args expr with
    | [ _; e ] ->
        let m =
          apply_bop ctx senv penv dtenv (T_int.mk_rem Value.Euclidean) expr
        in
        T_bool.mk_if_then_else
          (T_bool.of_atom
          @@ T_int.mk_geq (term_of ctx senv penv dtenv e) (T_int.zero ()))
          m (T_int.mk_neg m)
    | _ -> assert false
  else if Z3.BitVector.is_bv_numeral expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    T_bv.mk_bvnum ~size @@ Z.of_string @@ Z3.BitVector.numeral_to_string expr
  else if Z3.BitVector.is_bv_uminus expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_uop ctx senv penv dtenv (T_bv.mk_bvneg ~size) expr
  else if Z3.BitVector.is_bv_not expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_uop ctx senv penv dtenv (T_bv.mk_bvnot ~size) expr
  else if Z3.BitVector.is_int2bv expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_uop ctx senv penv dtenv (T_irb.mk_int_to_bv ~size) expr
  else if Z3.BitVector.is_bv2int expr then
    let size =
      match Z3.Expr.get_args expr with
      | [ e ] -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e))
      | _ -> failwith "[z3:term_of]"
    in
    (* Z3's [OP_BV2INT] is [bv2nat]: [mk_bv2int ~signed:true] produces
       [ite (bvslt t 0) (bv2nat t - 2^n) (bv2nat t)] around it, so the node
       itself is always the unsigned conversion *)
    let signed = Some false in
    apply_uop ctx senv penv dtenv (T_irb.mk_bv_to_int ~size ~signed) expr
  else if Z3.BitVector.is_bv_and expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_nop ctx senv penv dtenv (T_bv.mk_bvand ~size) expr
  else if Z3.BitVector.is_bv_or expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_nop ctx senv penv dtenv (T_bv.mk_bvor ~size) expr
  else if Z3.BitVector.is_bv_xor expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_nop ctx senv penv dtenv (T_bv.mk_bvxor ~size) expr
  else if Z3.BitVector.is_bv_nand expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvnand ~size) expr
  else if Z3.BitVector.is_bv_nor expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvnor ~size) expr
  else if Z3.BitVector.is_bv_xnor expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvxnor ~size) expr
  else if Z3.BitVector.is_bv_add expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_nop ctx senv penv dtenv (T_bv.mk_bvadd ~size) expr
  else if Z3.BitVector.is_bv_sub expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvsub ~size) expr
  else if Z3.BitVector.is_bv_mul expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_nop ctx senv penv dtenv (T_bv.mk_bvmul ~size) expr
  else if Z3.BitVector.is_bv_sdiv expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    let signed = Some true in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvdiv ~size ~signed) expr
  else if Z3.BitVector.is_bv_udiv expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    let signed = Some false in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvdiv ~size ~signed) expr
  else if Z3.BitVector.is_bv_SRem expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    let signed = Some true in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvrem ~size ~signed) expr
  else if Z3.BitVector.is_bv_urem expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    let signed = Some false in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvrem ~size ~signed) expr
  else if Z3.BitVector.is_bv_smod expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvsmod ~size) expr
  else if
    is_decl_kind expr
      Z3enums.
        [
          OP_BSDIV_I;
          OP_BUDIV_I;
          OP_BSREM_I;
          OP_BUREM_I;
          OP_BSMOD_I;
          OP_BSDIV0;
          OP_BUDIV0;
          OP_BSREM0;
          OP_BUREM0;
          OP_BSMOD0;
        ]
  then
    (* Z3's internal "interpreted" division operators: [Expr.simplify] rewrites
       even [bvsdiv x y] to [bvsdiv_i x y]; they denote the SMT-LIB total
       functions (x div 0 = all ones, x rem 0 = x), which is what the CoAR
       operators mean, and [bvXdiv0 x] is the divisor-zero value *)
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    let all_ones =
      T_bv.mk_bvnum ~size (Z.pred (Z.shift_left Z.one (T_bv.bits_of size)))
    in
    match decl_kind_opt expr with
    | Some Z3enums.OP_BSDIV_I ->
        apply_bop ctx senv penv dtenv
          (T_bv.mk_bvdiv ~size ~signed:(Some true))
          expr
    | Some Z3enums.OP_BUDIV_I ->
        apply_bop ctx senv penv dtenv
          (T_bv.mk_bvdiv ~size ~signed:(Some false))
          expr
    | Some Z3enums.OP_BSREM_I ->
        apply_bop ctx senv penv dtenv
          (T_bv.mk_bvrem ~size ~signed:(Some true))
          expr
    | Some Z3enums.OP_BUREM_I ->
        apply_bop ctx senv penv dtenv
          (T_bv.mk_bvrem ~size ~signed:(Some false))
          expr
    | Some Z3enums.OP_BSMOD_I ->
        apply_bop ctx senv penv dtenv (T_bv.mk_bvsmod ~size) expr
    | Some (Z3enums.OP_BSDIV0 | Z3enums.OP_BUDIV0) ->
        apply_uop ctx senv penv dtenv (fun _ -> all_ones) expr
    | Some (Z3enums.OP_BSREM0 | Z3enums.OP_BUREM0 | Z3enums.OP_BSMOD0) ->
        apply_uop ctx senv penv dtenv Fn.id expr
    | _ -> assert false
  else if Z3.BitVector.is_bv_shiftleft expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvshl ~size) expr
  else if Z3.BitVector.is_bv_shiftrightlogical expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvlshr ~size) expr
  else if Z3.BitVector.is_bv_shiftrightarithmetic expr then
    let size = Some (Z3.BitVector.get_size (Z3.Expr.get_sort expr)) in
    apply_bop ctx senv penv dtenv (T_bv.mk_bvashr ~size) expr
  else if Z3.BitVector.is_bv_extract expr then
    let size =
      Z3.BitVector.get_size @@ Z3.Expr.get_sort @@ List.hd_exn
      @@ Z3.Expr.get_args expr
    in
    let h, l =
      match Z3.FuncDecl.get_parameters (Z3.Expr.get_func_decl expr) with
      | [ ph; pl ] ->
          (Z3.FuncDecl.Parameter.get_int ph, Z3.FuncDecl.Parameter.get_int pl)
      | _ -> failwith "[z3:term_of] extract without its two bit positions"
    in
    apply_uop ctx senv penv dtenv (T_bv.mk_bvextract ~size:(Some size) h l) expr
  else if Z3.BitVector.is_bv_signextension expr then
    let size =
      Z3.BitVector.get_size @@ Z3.Expr.get_sort @@ List.hd_exn
      @@ Z3.Expr.get_args expr
    in
    let size' = Z3.BitVector.get_size @@ Z3.Expr.get_sort expr in
    apply_uop ctx senv penv dtenv
      (T_bv.mk_bvsext ~size:(Some size) (size' - size))
      expr
  else if Z3.BitVector.is_bv_zeroextension expr then
    let size =
      Z3.BitVector.get_size @@ Z3.Expr.get_sort @@ List.hd_exn
      @@ Z3.Expr.get_args expr
    in
    let size' = Z3.BitVector.get_size @@ Z3.Expr.get_sort expr in
    apply_uop ctx senv penv dtenv
      (T_bv.mk_bvzext ~size:(Some size) (size' - size))
      expr
  else if Z3.BitVector.is_bv_concat expr then
    (* Z3 flattens n-ary concat into a single application *)
    match Z3.Expr.get_args expr with
    | _ :: _ :: _ as es ->
        let size_of e = Z3.BitVector.get_size (Z3.Expr.get_sort e) in
        let rec build = function
          | [] -> assert false
          | [ e ] -> (term_of ctx senv penv dtenv e, size_of e)
          | e :: rest ->
              let t_rest, size_rest = build rest in
              ( T_bv.mk_bvconcat
                  ~size1:(Some (size_of e))
                  ~size2:(Some size_rest)
                  (term_of ctx senv penv dtenv e)
                  t_rest,
                size_of e + size_rest )
        in
        fst (build es)
    | _ -> failwith "[z3:term_of] bv_concat requires at least two arguments"
  else if Z3.Z3Array.is_store expr then
    match
      ( List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr,
        sort_of dtenv @@ Z3.Expr.get_sort expr )
    with
    | [ t1; t2; t3 ], T_array.SArray (s1, s2) -> T_array.mk_store s1 s2 t1 t2 t3
    | _ -> failwith "[z3:term_of]"
  else if Z3.Z3Array.is_constant_array expr then
    match
      ( List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr,
        sort_of dtenv @@ Z3.Expr.get_sort expr )
    with
    | [ t1 ], T_array.SArray (s1, s2) -> T_array.mk_const_array s1 s2 t1
    | _ -> failwith "[z3:term_of]"
  else if Z3.Z3Array.is_select expr then
    let args = Z3.Expr.get_args expr in
    match (args, List.map ~f:(term_of ctx senv penv dtenv) args) with
    | [ e1; _e2 ], [ t1; t2 ] -> (
        match
          (T_array.eval_select t1 t2, sort_of dtenv @@ Z3.Expr.get_sort e1)
        with
        | Some te, _ -> te
        | _, T_array.SArray (s1, s2) -> T_array.mk_select s1 s2 t1 t2
        | _ -> failwith "[z3:term_of]")
    | _ -> failwith "[z3:term_of]"
  else if Z3.Z3Array.is_as_array expr then
    (* [(_ as-array f)] denotes the graph of [f] as interpreted in the model it
       occurs in, so it cannot be decoded without that model.  [model_of] calls
       [expand_as_array] beforehand to eliminate the decodable cases; reaching
       here means either there was no model at hand or the underlying function
       has an arity other than one (i.e. a non-binary Z3 array). *)
    failwith
    @@ sprintf "[z3:term_of] %s not supported (as-array unresolved)"
    @@ Z3.Expr.to_string expr
  else if
    Z3.AST.is_quantifier (Z3.Expr.ast_of_expr expr)
    && Stdlib.(
         Z3.Sort.get_sort_kind (Z3.Expr.get_sort expr) = Z3enums.ARRAY_SORT)
  then
    (* an array-sorted quantifier is Z3's [lambda].  It must be recognised
       before [formula_of], whose [is_universal]/[is_existential] test cannot
       tell it apart: the OCaml binding defines the latter as the negation of
       the former, so a lambda would silently decode as an existential.
       [Z3.Z3Array.is_array] is no use here either -- it requires the
       expression to be an application, which a quantifier is not. *)
    let q = Z3.Quantifier.quantifier_of_expr expr in
    match
      ( Z3.Quantifier.get_bound_variable_names q,
        Z3.Quantifier.get_bound_variable_sorts q )
    with
    | [ name ], [ sort ] ->
        let x =
          fresh_binder_avoiding
            (free_const_names_of dtenv @@ Z3.Quantifier.get_body q)
            senv
            ~prefix:(try Z3.Symbol.get_string name with exn_ when not (Common.Timer.is_async exn_) -> "lam")
        in
        let si = sort_of dtenv sort in
        let se =
          sort_of dtenv @@ Z3.Z3Array.get_range @@ Z3.Expr.get_sort expr
        in
        T_array.mk_lambda (x, si) se
        @@ term_of ctx (senv @ [ (x, si) ]) penv dtenv
        @@ Z3.Quantifier.get_body q
    | _ ->
        (* several binders denote a non-binary Z3 array *)
        failwith
        @@ sprintf "[z3:term_of] %s not supported (multi-parameter lambda)"
        @@ Z3.Expr.to_string expr
  else if Z3.Seq.is_string ctx expr then
    T_string.make (Z3.Seq.get_string ctx expr)
  else if
    is_decl_kind expr
      Z3enums.[ OP_SEQ_EMPTY; OP_SEQ_UNIT; OP_SEQ_CONCAT; OP_SEQ_EXTRACT ]
  then
    (* a sequence VALUE as a model prints it: the empty sequence, a one-element
       sequence, or a concatenation of those, and the extract the encoder
       emits.  Only these operators are taken here: a free sequence or string
       constant, a selector or an uninterpreted function returning a sequence
       is an ordinary application and decodes below like one of any other
       sort. *)
    let se =
      match sort_of dtenv @@ Z3.Expr.get_sort expr with
      | T_seq.SSeq se -> se
      | s ->
          failwith
          @@ sprintf "[z3:term_of] not a sequence sort: %s"
               (Term.str_of_sort s)
    in
    match Z3.FuncDecl.get_decl_kind @@ Z3.Expr.get_func_decl expr with
    | Z3enums.OP_SEQ_EMPTY -> T_seq.mk_empty se
    | Z3enums.OP_SEQ_UNIT -> (
        match List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr with
        | [ t ] -> T_seq.mk_unit se t
        | _ -> failwith "[z3:term_of] seq.unit takes one argument")
    | Z3enums.OP_SEQ_CONCAT -> (
        match List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr with
        | [] -> T_seq.mk_empty se
        | t :: ts -> List.fold ts ~init:t ~f:(T_seq.mk_concat se))
    | Z3enums.OP_SEQ_EXTRACT -> (
        match List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr with
        | [ t; off; len ] -> T_seq.mk_extract se t off len
        | _ -> failwith "[z3:term_of] seq.extract takes three arguments")
    | _ ->
        failwith
        @@ sprintf "[z3:term_of] unsupported sequence operator in %s"
        @@ Z3.Expr.to_string expr
  else if is_decl_kind expr Z3enums.[ OP_SEQ_LENGTH; OP_SEQ_NTH ] then
    (* the length and the read the encoder emits for [T_seq.SqLen] and
       [T_seq.SqNth]; the element sort is the sequence argument's *)
    let args = Z3.Expr.get_args expr in
    let se =
      match args with
      | e :: _ -> (
          match sort_of dtenv @@ Z3.Expr.get_sort e with
          | T_seq.SSeq se -> se
          | s ->
              failwith
              @@ sprintf
                   "[z3:term_of] unsupported Z3 operator in %s: the argument has sort %s, not a sequence sort of this tree"
                   (Z3.Expr.to_string expr) (Term.str_of_sort s))
      | [] -> failwith "[z3:term_of] a sequence operator with no argument"
    in
    match (decl_kind_opt expr, List.map ~f:(term_of ctx senv penv dtenv) args) with
    | Some Z3enums.OP_SEQ_LENGTH, [ t ] -> T_seq.mk_len se t
    | Some Z3enums.OP_SEQ_NTH, [ t; i ] -> T_seq.mk_nth se t i
    | _ ->
        failwith @@ "[z3:term_of] ill-formed sequence operator in "
        ^ Z3.Expr.to_string expr
  else if
    Z3.Seq.is_re_sort ctx (Z3.Expr.get_sort expr)
    && not (is_decl_kind expr Z3enums.[ OP_UNINTERPRETED ])
  then
    (* the regular expressions, one case per constructor [of_term] emits; a
       free regex constant is an ordinary application and decodes below *)
    let args = Z3.Expr.get_args expr in
    let unsupported () =
      failwith
      @@ sprintf "[z3:term_of] unsupported Z3 regex operator %s in %s"
           (Z3.Symbol.to_string @@ Z3.FuncDecl.get_name
          @@ Z3.Expr.get_func_decl expr)
           (Z3.Expr.to_string expr)
    in
    let fold op =
      match List.map ~f:(term_of ctx senv penv dtenv) args with
      | t :: ts -> List.fold ts ~init:t ~f:(fun acc t -> op acc t)
      | [] -> unsupported ()
    in
    let unary op =
      match List.map ~f:(term_of ctx senv penv dtenv) args with
      | [ t ] -> op t
      | _ -> unsupported ()
    in
    match decl_kind_opt expr with
    | Some Z3enums.OP_RE_EMPTY_SET -> T_regex.mk_empty ()
    | Some Z3enums.OP_RE_FULL_SET -> T_regex.mk_full ()
    | Some Z3enums.OP_RE_FULL_CHAR_SET -> T_regex.mk_allchar ()
    | Some Z3enums.OP_RE_RANGE -> (
        (* [of_term] writes the one-character strings as the range over the
           whole SMT-LIB alphabet; no other range has a constructor here *)
        match args with
        | [ lo; hi ]
          when Z3.Expr.equal lo (Z3.Seq.mk_string ctx "\\u{0}")
               && Z3.Expr.equal hi (Z3.Seq.mk_string ctx "\\u{2FFFF}") ->
            T_regex.mk_allchar ()
        | _ -> unsupported ())
    | Some Z3enums.OP_SEQ_TO_RE -> (
        match args with
        | [ e ] when Z3.Seq.is_string ctx e && String.is_empty (Z3.Seq.get_string ctx e) ->
            T_regex.mk_eps ()
        | _ -> unary T_regex.mk_str_to_re)
    | Some Z3enums.OP_RE_COMPLEMENT -> unary T_regex.mk_complement
    | Some Z3enums.OP_RE_STAR -> unary T_regex.mk_star
    | Some Z3enums.OP_RE_PLUS -> unary T_regex.mk_plus
    | Some Z3enums.OP_RE_OPTION -> unary T_regex.mk_opt
    | Some Z3enums.OP_RE_CONCAT -> fold T_regex.mk_concat
    | Some Z3enums.OP_RE_UNION -> fold T_regex.mk_union
    | Some Z3enums.OP_RE_INTERSECT -> fold T_regex.mk_inter
    | _ -> unsupported ()
  else if Z3.AST.is_var @@ Z3.Expr.ast_of_expr expr then
    (* bound variables *)
    let _ =
      Debug.print @@ lazy ("[z3:term_of] bound var: " ^ Z3.Expr.to_string expr)
    in
    try
      let tvar, sort =
        List.nth_exn senv
        @@ List.length senv
           - Scanf.sscanf (Z3.Expr.to_string expr) "(:var %d)" Fn.id
           - 1
      in
      Debug.print
      @@ lazy
           ("[z3:term_of] identifier: " ^ Ident.name_of_tvar tvar ^ " : "
          ^ Term.str_of_sort sort);
      Term.mk_var tvar sort
    with exn_ when not (Common.Timer.is_async exn_) ->
      failwith @@ "[z3:term_of] " ^ Z3.Expr.to_string expr ^ " not found"
    (*else if Z3.AST.is_quantifier @@ Z3.Expr.ast_of_expr expr then
      let q = Z3.Quantifier.quantifier_of_expr expr in
      let _ =
        if Z3.Quantifier.is_universal q then
          Debug.print @@ lazy ("universally quantified: " ^ Z3.Expr.to_string expr)
        else if Z3.Quantifier.is_existential q then
          Debug.print
          @@ lazy ("existentially quantified: " ^ Z3.Expr.to_string expr)
        else assert false
      in
      T_bool.of_formula @@ formula_of ctx senv penv dtenv expr*)
  else
    try
      (* function applications (and constants) *)
      Debug.print @@ lazy "function applications and constants";
      let func =
        try Z3.Expr.get_func_decl expr
        with e ->
          Debug.print @@ lazy "get_func_decl failed";
          raise e
      in
      let ret_sort =
        try sort_of dtenv @@ Z3.FuncDecl.get_range func
        with Failure err ->
          Debug.print @@ lazy ("error: " ^ err);
          failwith err
      in
      let name =
        InstanceName.decode ~sort:ret_sort
        @@ unescape_z3 @@ Z3.Symbol.get_string @@ Z3.FuncDecl.get_name func
      in
      let ts =
        List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr
      in
      let arg_sorts = List.map ~f:Term.sort_of ts in
      (* the following causes an exception if [expr] contains a bound variable:
         let arg_sorts =
          List.map ~f:(Expr.get_sort >> sort_of dtenv) @@ Z3.Expr.get_args expr
         in *)
      if String.(name = "mp" || name = "hyper-res" || name = "asserted") then
        Term.mk_fvar_app (Ident.Tvar name) arg_sorts ret_sort ts
      else
        try
          (* algebraic data types *)
          Debug.print @@ lazy "algebraic data types";
          match look_up_func dtenv func with
          | Some (dt, `Cons cons) ->
              Debug.print @@ lazy "constructor";
              T_dt.mk_cons dt (Datatype.name_of_cons cons) ts
          | Some (dt, `IsCons cons) ->
              Debug.print @@ lazy "tester";
              T_bool.of_atom
              @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons)
              @@ List.hd_exn ts
          | Some (dt, `Sel sel) ->
              Debug.print @@ lazy "accessor";
              T_dt.mk_sel dt (Datatype.name_of_sel sel) @@ List.hd_exn ts
          | None when T_dt.is_sdt ret_sort && List.is_empty ts ->
              Debug.print @@ lazy "no definition";
              Term.mk_var (Ident.Tvar name) ret_sort
          | _ -> failwith "[z3:term_of] not an ADT term"
        with Failure err -> (
          Debug.print @@ lazy ("error: " ^ err);
          try
            (* integers *)
            if String.(name = "^") then
              match ts with
              | [ t1; t2 ] -> T_real.mk_rpower t1 t2
              | _ -> failwith "[z3:term_of] not a valid integer power term"
            else if
              (* tuples *)
              String.is_prefix ~prefix:unint_tuple_prefix name
            then T_tuple.mk_tuple_cons arg_sorts ts
            else if
              String.is_prefix ~prefix:unint_tuple_sel_prefix name
              && List.length ts = 1
            then
              let pre_length = String.length unint_tuple_sel_prefix in
              let i =
                Int.of_string
                @@ String.sub name ~pos:pre_length
                     ~len:(String.length name - pre_length)
              in
              match (ts, arg_sorts) with
              | [ t ], [ T_tuple.STuple elem_sorts ] ->
                  T_tuple.mk_tuple_sel elem_sorts t i
              | _ -> failwith "[z3:term_of] not a valid tuple/sequence term"
            else if
              String.(
                name
                = "is" (*ToDo: Z3 automatically generates a tester of the name*))
              && List.length ts = 1
            then
              match (ts, arg_sorts) with
              | [ _t ], [ T_tuple.STuple _elem_sorts ] ->
                  (*ToDo*)
                  T_bool.mk_true
                    () (*T_bool.of_atom @@ T_tuple.mk_is_tuple elem_sorts t*)
              | _ -> failwith "[z3:term_of] not a valid tuple/sequence term"
            else if String.(name = unint_epsilon) && List.is_empty ts then
              T_trace.mk_eps ()
            else if
              String.is_prefix ~prefix:unint_symbol_prefix name
              && List.is_empty ts
            then
              let pre_length = String.length unint_symbol_prefix in
              let symbol =
                String.sub name ~pos:pre_length
                  ~len:(String.length name - pre_length)
              in
              T_trace.mk_symbol symbol
            else if String.(name = unint_concat_fin) then
              match ts with
              | [ t1; t2 ] -> T_trace.mk_concat ~fin:true t1 t2
              | _ -> failwith "[z3:term_of] not a valid tuple/sequence term"
            else if String.(name = unint_concat_inf) && List.length ts = 2 then
              match ts with
              | [ t1; t2 ] -> T_trace.mk_concat ~fin:false t1 t2
              | _ -> failwith "[z3:term_of] not a valid tuple/sequence term"
            else
              match trace_atom_of_name name ts with
              | Some atm -> T_bool.of_atom atm
              | None -> failwith "[z3:term_of] not a tuple/sequence term"
          with Failure err -> (
            Debug.print @@ lazy ("error: " ^ err);
            (* function applications *)
            match Map.Poly.find (get_fenv ()) (Ident.Tvar name) with
            | Some (params, sret, _, _, _) ->
                Term.mk_fvar_app (Ident.Tvar name) (List.map params ~f:snd)
                  (*arg_sorts*) sret (*ret_sort*)
                  ts
            | _ -> (
                try
                  (* formulas *)
                  match sort_of dtenv @@ Z3.Expr.get_sort expr with
                  | T_bool.SBool ->
                      if List.is_empty ts then
                        Term.mk_var (Ident.Tvar name) T_bool.SBool
                      else if
                        List.Assoc.mem ~equal:Stdlib.( = ) penv (Ident.Pvar name)
                        (* Z3's fixedpoint engine names its own query predicate
                           [query!N] when a query has free variables, and a
                           refutation's proof term mentions it inside [mp] and
                           [hyper-res]; nobody declares it, so it is not in
                           [penv], and [atom_of] decodes it as an application
                           of a predicate of that name.  Refusing it here made
                           every counterexample whose proof reaches such a
                           query undecodable. *)
                        || String.is_prefix name ~prefix:"query!"
                      then
                        T_bool.of_formula @@ formula_of ctx senv penv dtenv expr
                      else if
                        Stdlib.(
                          Z3.FuncDecl.get_decl_kind func
                          = Z3enums.OP_UNINTERPRETED)
                      then
                        (* A predicate variable and a Bool-valued uninterpreted
                           function are the same thing to Z3, and reading one as
                           the other silently changes what is an unknown; the
                           caller that encoded predicate variables passes them
                           in [penv], so one that is absent is refused here. *)
                        let msg =
                          sprintf
                            "[z3:term_of] %s is a Bool-valued uninterpreted application with no declaration in the predicate environment: a predicate variable must be passed to the decoder in [penv], and a Bool-valued function is not decoded"
                            (Z3.Expr.to_string expr)
                        in
                        raise (Unsupported_bool_application msg)
                      else if as_atom then
                        (* [atom_of] has already tried this expression and
                           found no case for it; retrying as a formula would
                           return it here *)
                        failwith "[z3:term_of] not a formula"
                      else
                        T_bool.of_formula @@ formula_of ctx senv penv dtenv expr
                  | _ -> failwith "[z3:term_of] not a formula"
                with Failure err ->
                  Debug.print @@ lazy ("error: " ^ err);
                  (* variables / function variable applications *)
                  (match Z3.FuncDecl.get_decl_kind func with
                  | Z3enums.OP_UNINTERPRETED -> ()
                  | _ ->
                      (* a Z3 built-in the decoder does not know; inventing a
                         free function symbol for it silently changes the
                         meaning *)
                      let msg =
                        sprintf "[z3:term_of] unsupported Z3 operator %s in %s"
                          name (Z3.Expr.to_string expr)
                      in
                      Debug.print @@ lazy msg;
                      failwith msg);
                  if List.is_empty ts then
                    Term.mk_var (Ident.Tvar name) ret_sort
                  else Term.mk_fvar_app (Ident.Tvar name) arg_sorts ret_sort ts)))
    with
    | Unsupported_bool_application msg -> failwith msg
    | exn_
      when (not (Common.Timer.is_async exn_))
           && (not as_atom)
           && Stdlib.(
                Z3.Sort.get_sort_kind (Z3.Expr.get_sort expr)
                = Z3enums.BOOL_SORT) ->
        (* a Bool-valued expression the term decoder has no case for -- a
           quantifier, a connective in term position -- is decoded as a
           formula, once: [as_atom] is set when the formula decoder's atom case
           hands the expression back, and then the failure is raised *)
        T_bool.of_formula @@ formula_of ctx senv penv dtenv expr

and
    (* Conversion from Z3 expressions to atoms *)
    atom_of ctx (senv : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (dtenv : dtenv)
    expr =
  Debug.print @@ lazy ("[z3:atom_of] " ^ Z3.Expr.to_string expr);
  if Z3.Boolean.is_true expr then Atom.mk_true ()
  else if Z3.Boolean.is_false expr then Atom.mk_false ()
  else if Z3.Boolean.is_eq expr then
    match Z3.Expr.get_args expr with
    | [ e1; e2 ]
      when Stdlib.(Term.is_bool_sort @@ sort_of dtenv @@ Z3.Expr.get_sort e1) ->
        T_bool.mk_eq
          (T_bool.of_formula @@ formula_of ctx senv penv dtenv e1)
          (T_bool.of_formula @@ formula_of ctx senv penv dtenv e2)
    | _ -> apply_brel ctx senv penv dtenv T_bool.mk_eq expr
  else if Z3.Arithmetic.is_real_is_int expr then
    apply_urel ctx senv penv dtenv T_irb.mk_is_int expr
  else if Z3.Arithmetic.is_le expr then
    Typeinf.typeinf_atom ~print:Debug.print ~default:None
    @@ apply_brel ctx senv penv dtenv T_num.mk_nleq expr
  else if Z3.Arithmetic.is_ge expr then
    Typeinf.typeinf_atom ~print:Debug.print ~default:None
    @@ apply_brel ctx senv penv dtenv T_num.mk_ngeq expr
  else if Z3.Arithmetic.is_lt expr then
    Typeinf.typeinf_atom ~print:Debug.print ~default:None
    @@ apply_brel ctx senv penv dtenv T_num.mk_nlt expr
  else if Z3.Arithmetic.is_gt expr then
    Typeinf.typeinf_atom ~print:Debug.print ~default:None
    @@ apply_brel ctx senv penv dtenv T_num.mk_ngt expr
  else if Z3.BitVector.is_bv_sle expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e))
      | _ -> failwith "[z3:atom_of]"
    in
    let signed = Some true in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvleq ~size ~signed) expr
  else if Z3.BitVector.is_bv_ule expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e))
      | _ -> failwith "[z3:atom_of]"
    in
    let signed = Some false in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvleq ~size ~signed) expr
  else if Z3.BitVector.is_bv_sge expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e))
      | _ -> failwith "[z3:atom_of]"
    in
    let signed = Some true in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvgeq ~size ~signed) expr
  else if Z3.BitVector.is_bv_uge expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e))
      | _ -> failwith "[z3:atom_of]"
    in
    let signed = Some false in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvgeq ~size ~signed) expr
  else if Z3.BitVector.is_bv_slt expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e))
      | _ -> failwith "[z3:atom_of]"
    in
    let signed = Some true in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvlt ~size ~signed) expr
  else if Z3.BitVector.is_bv_ult expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e))
      | _ -> failwith "[z3:atom_of]"
    in
    let signed = Some false in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvlt ~size ~signed) expr
  else if Z3.BitVector.is_bv_sgt expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e))
      | _ -> failwith "[z3:atom_of]"
    in
    let signed = Some true in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvgt ~size ~signed) expr
  else if Z3.BitVector.is_bv_ugt expr then
    let size =
      match Z3.Expr.get_args expr with
      | e :: _ -> Some (Z3.BitVector.get_size (Z3.Expr.get_sort e))
      | _ -> failwith "[z3:atom_of]"
    in
    let signed = Some false in
    apply_brel ctx senv penv dtenv (T_bv.mk_bvgt ~size ~signed) expr
  else if is_decl_kind expr Z3enums.[ OP_SEQ_IN_RE ] then
    apply_brel ctx senv penv dtenv T_regex.mk_str_in_regexp expr
  else if Z3.AST.is_var @@ Z3.Expr.ast_of_expr expr then
    (* bound variables *)
    let _ =
      Debug.print @@ lazy ("[z3:atom_of] bound var: " ^ Z3.Expr.to_string expr)
    in
    try
      let tvar, _sort (* assume bool*) =
        List.nth_exn senv
        @@ List.length senv
           - Scanf.sscanf (Z3.Expr.to_string expr) "(:var %d)" Fn.id
           - 1
      in
      Debug.print @@ lazy ("[z3:atom_of] identifier: " ^ Ident.name_of_tvar tvar);
      match
        List.Assoc.find ~equal:Stdlib.( = ) penv (Ident.tvar_to_pvar tvar)
      with
      | Some _ -> Atom.mk_pvar_app (Ident.tvar_to_pvar tvar) [] [] (*ToDo*)
      | _ -> Atom.of_bool_term @@ Term.mk_var tvar T_bool.SBool
    with exn_ when not (Common.Timer.is_async exn_) ->
      failwith @@ "[z3:atom_of] " ^ Z3.Expr.to_string expr ^ " not found"
  else
    let func = Z3.Expr.get_func_decl expr in
    let name =
      InstanceName.decode ~sort:(sort_of dtenv @@ Z3.FuncDecl.get_range func)
      @@ unescape_z3 @@ Z3.Symbol.get_string @@ Z3.FuncDecl.get_name func
    in
    let pvar = Ident.Pvar name in
    let atm =
      let ts =
        List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr
      in
      Atom.mk_pvar_app pvar (List.map ts ~f:Term.sort_of) ts
    in
    if String.is_prefix name ~prefix:"query!" then (*ToDo*)
      atm
    else
      match List.Assoc.find ~equal:Stdlib.( = ) penv pvar with
      | Some _ -> atm
      | None -> (
          if false then
            print_endline @@ name ^ " is not bound in the environment";
          if is_trace_pred_name name then
            (* the trace predicates are atoms of their own, not Bool terms *)
            match
              trace_atom_of_name name
              @@ List.map ~f:(term_of ctx senv penv dtenv)
              @@ Z3.Expr.get_args expr
            with
            | Some atm -> atm
            | None -> assert false
          else
          try Atom.of_bool_term @@ term_of ~as_atom:true ctx senv penv dtenv expr
          with Failure err ->
            failwith
            @@ sprintf "[z3:atom_of] %s caused %s" (Z3.Expr.to_string expr) err)

and
    (* Conversion from Z3 expressions to formulas *)
    formula_of ctx (senv : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (dtenv : dtenv)
    expr =
  Debug.print @@ lazy ("[z3:formula_of] " ^ Z3.Expr.to_string expr);
  if Z3.Boolean.is_not expr then
    match Z3.Expr.get_args expr with
    | [ body ] -> Formula.negate (formula_of ctx senv penv dtenv body)
    | _ -> failwith "[z3:formula_of]"
  else if Z3.Boolean.is_and expr then
    Formula.and_of
    @@ List.map ~f:(formula_of ctx senv penv dtenv)
    @@ Z3.Expr.get_args expr
  else if Z3.Boolean.is_or expr then
    Formula.or_of
    @@ List.map ~f:(formula_of ctx senv penv dtenv)
    @@ Z3.Expr.get_args expr
  else if Z3.Boolean.is_iff expr then
    Z3.Expr.get_args expr |> List.map ~f:(formula_of ctx senv penv dtenv)
    |> function
    | [ phi1; phi2 ] -> Formula.mk_iff phi1 phi2
    | _ -> failwith "[z3:formula_of]"
  else if Z3.Boolean.is_implies expr then
    Z3.Expr.get_args expr |> List.map ~f:(formula_of ctx senv penv dtenv)
    |> function
    | [ phi1; phi2 ] -> Formula.mk_imply phi1 phi2
    | _ -> failwith "[z3:formula_of]"
  else if Z3.Boolean.is_xor expr then
    Z3.Expr.get_args expr |> List.map ~f:(formula_of ctx senv penv dtenv)
    |> function
    | [ phi1; phi2 ] -> Formula.mk_xor phi1 phi2
    | _ -> failwith "[z3:formula_of]"
  else if Z3.Boolean.is_distinct expr then
    (* [distinct t1 .. tn] is the conjunction of the pairwise disequalities;
       without this case [formula_of], [atom_of] and [term_of] cycled forever
       on it *)
    let ts =
      List.map ~f:(term_of ctx senv penv dtenv) @@ Z3.Expr.get_args expr
    in
    Formula.and_of
    @@ List.concat_mapi ts ~f:(fun i ti ->
        List.filter_mapi ts ~f:(fun j tj ->
            if i < j then Some (Formula.neq ti tj) else None))
  else if Z3.Boolean.is_ite expr then
    match Z3.Expr.get_args expr with
    | [ e1; e2; e3 ] ->
        Formula.of_bool_term
        @@ T_bool.ifte
             (formula_of ctx senv penv dtenv e1)
             (term_of ctx senv penv dtenv e2)
             (term_of ctx senv penv dtenv e3)
    | _ -> failwith "[z3:formula_of]"
  else if Z3.AST.is_quantifier @@ Z3.Expr.ast_of_expr expr then
    let q = Z3.Quantifier.quantifier_of_expr expr in
    let binder =
      if Z3.Quantifier.is_universal q then Formula.Forall
      else if Z3.Quantifier.is_existential q then Formula.Exists
      else assert false
    in
    (* each binder avoids the body's free constants and the environment it is
       decoded in.  Two binders of this quantifier cannot meet: each name ends
       in its own counter value after the prefix's closing underscore. *)
    let names = free_const_names_of dtenv @@ Z3.Quantifier.get_body q in
    let bounds =
      List.zip_exn
        (List.map ~f:(fun x ->
             fresh_binder_avoiding names senv
               ~prefix:(Z3.Symbol.get_string x ^ "_"))
        @@ Z3.Quantifier.get_bound_variable_names q)
        (List.map ~f:(sort_of dtenv) @@ Z3.Quantifier.get_bound_variable_sorts q)
    in
    let senv = senv @ bounds in
    Formula.mk_bind binder bounds
    @@ formula_of ctx senv penv dtenv
    @@ Z3.Quantifier.get_body q
  else Formula.mk_atom @@ atom_of ctx senv penv dtenv expr

let dummy_term_map_of terms =
  Map.of_set_exn
  @@ Set.Poly.filter_map terms ~f:(function
    | tvar, (T_dt.SUS (name, _) as sort) ->
        let tvar' = Ident.mk_fresh_dummy_tvar name in
        LogicOld.add_dummy_term tvar' sort;
        Some (tvar, Term.mk_var tvar' sort)
    | _ -> None)

let add_dummy_term model =
  List.filter_map model ~f:(function _, Some t -> Some t | _ -> None)
  |> List.fold_left ~init:Set.Poly.empty ~f:(fun ret term ->
      Set.filter ~f:(function _, T_dt.SUS _ -> true | _ -> false)
      @@ Set.union ret @@ Term.term_sort_env_of term)
  |> Set.iter ~f:(Tuple2.uncurry add_dummy_term)

(** [(_ as-array f)] is Z3's indirect representation of an array value: it
    denotes the graph of the function [f], whose interpretation lives in the
    same model. [term_of] receives no model and hence cannot decode it, so
    rewrite every such node into an equivalent [const]/[store] chain first. Only
    unary [f] is handled, since a wider one denotes a non-binary Z3 array, which
    [sort_of] cannot represent either; such nodes are left untouched and
    reported by [term_of]. *)
let rec expand_as_array ctx model expr =
  if Z3.Z3Array.is_as_array expr then
    match
      List.filter_map ~f:(fun param ->
          try Some (Z3.FuncDecl.Parameter.get_func_decl param)
          with exn_ when not (Common.Timer.is_async exn_) -> None)
      @@ Z3.FuncDecl.get_parameters @@ Z3.Expr.get_func_decl expr
    with
    | [ decl ] when Z3.FuncDecl.get_arity decl = 1 -> (
        match Z3.Model.get_func_interp model decl with
        | Some fi ->
            let init =
              Z3.Z3Array.mk_const_array ctx
                (Z3.Z3Array.get_domain @@ Z3.Expr.get_sort expr)
                (expand_as_array ctx model @@ Z3.Model.FuncInterp.get_else fi)
            in
            List.fold (Z3.Model.FuncInterp.get_entries fi) ~init
              ~f:(fun acc entry ->
                match Z3.Model.FuncInterp.FuncEntry.get_args entry with
                | [ arg ] ->
                    Z3.Z3Array.mk_store ctx acc
                      (expand_as_array ctx model arg)
                      (expand_as_array ctx model
                      @@ Z3.Model.FuncInterp.FuncEntry.get_value entry)
                | _ -> acc)
        | None -> expr)
    | _ -> expr
  else if
    (* bound variables and quantifiers (including lambdas) have no arguments to
       descend into via [Z3.Expr.update] *)
    let ast = Z3.Expr.ast_of_expr expr in
    Z3.AST.is_var ast || Z3.AST.is_quantifier ast
  then expr
  else
    match Z3.Expr.get_args expr with
    | [] -> expr
    | args ->
        let args' = List.map args ~f:(expand_as_array ctx model) in
        (* rebuild only when a child actually changed, so that an expression
           free of [as-array] is returned untouched *)
        if List.for_all2_exn args args' ~f:phys_equal then expr
        else Z3.Expr.update expr args'

(** Does [expr] apply a function of arity at least one whose interpretation
    lives in [model]?  Such an application is how Z3 writes an array value found
    by model-based quantifier instantiation: [x0 = lambda i. ite (k!18 i = 1236)
    ...], where [k!18] is a projection function the solver invented and
    interprets in the same model.  The decoder below cannot follow it, because
    a constant's value is decoded on its own and the model lists a function
    with no value, so the application would reach the caller as a free
    function symbol -- a value
    that no longer denotes the model's array, and a function-sorted name that
    nothing downstream can bind or look up.  Descends into quantifier bodies,
    since that is where these applications sit. *)
let rec applies_interpreted_function model expr =
  let ast = Z3.Expr.ast_of_expr expr in
  if Z3.AST.is_var ast then false
  else if Z3.AST.is_quantifier ast then
    applies_interpreted_function model
    @@ Z3.Quantifier.get_body
    @@ Z3.Quantifier.quantifier_of_expr expr
  else
    (Stdlib.(Z3.AST.get_ast_kind ast = Z3enums.APP_AST)
    &&
    let decl = Z3.Expr.get_func_decl expr in
    Z3.FuncDecl.get_arity decl > 0
    && Stdlib.(Z3.FuncDecl.get_decl_kind decl = Z3enums.OP_UNINTERPRETED)
    && Option.is_some (Z3.Model.get_func_interp model decl))
    || List.exists (Z3.Expr.get_args expr)
         ~f:(applies_interpreted_function model)

(* Does [expr] mention a bound variable outside every binder it contains, i.e.
   one bound by an enclosing context rather than by [expr] itself? *)
let rec has_loose_var expr =
  let ast = Z3.Expr.ast_of_expr expr in
  if Z3.AST.is_var ast then true
  else if Z3.AST.is_quantifier ast then false
  else List.exists (Z3.Expr.get_args expr) ~f:has_loose_var

(** Does [expr] contain an [(_ as-array g)] that [expand_as_array] cannot turn
    into an equivalent [const]/[store] chain?  That expansion reads [g]'s
    interpretation as a finite table of entries plus a default, and is exact
    only when every entry and the default are closed values.  Two shapes break
    it, both produced by model-based quantifier instantiation when an array is
    constrained pointwise by a quantifier: a default that mentions [g]'s own
    argument (it becomes a bound variable with no binder once lifted into a
    constant array, and decoding then fails), and an entry or default that
    applies another function the model interprets (the auxiliary function would
    reach the caller as a free symbol).  Walks every node, quantifier bodies
    included, and follows nested [as-array]s into their interpretations. *)
let rec has_unexpandable_as_array model expr =
  let ast = Z3.Expr.ast_of_expr expr in
  if Z3.AST.is_var ast then false
  else if Z3.AST.is_quantifier ast then
    has_unexpandable_as_array model
    @@ Z3.Quantifier.get_body
    @@ Z3.Quantifier.quantifier_of_expr expr
  else if Z3.Z3Array.is_as_array expr then
    List.exists (Z3.FuncDecl.get_parameters @@ Z3.Expr.get_func_decl expr)
      ~f:(fun param ->
        match
          try Some (Z3.FuncDecl.Parameter.get_func_decl param)
          with exn_ when not (Common.Timer.is_async exn_) -> None
        with
        | None -> false
        | Some decl -> (
            match Z3.Model.get_func_interp model decl with
            | None -> false
            | Some fi ->
                let bad v =
                  has_loose_var v
                  || applies_interpreted_function model v
                  || has_unexpandable_as_array model v
                in
                bad (Z3.Model.FuncInterp.get_else fi)
                || List.exists (Z3.Model.FuncInterp.get_entries fi)
                     ~f:(fun entry ->
                       bad (Z3.Model.FuncInterp.FuncEntry.get_value entry)
                       || List.exists ~f:bad
                            (Z3.Model.FuncInterp.FuncEntry.get_args entry))))
  else
    List.exists (Z3.Expr.get_args expr) ~f:(has_unexpandable_as_array model)

(** Must a constant's interpretation [expr] be read through the model's own
    evaluator rather than decoded as it stands?  True exactly for the two shapes
    the plain decoding gets wrong: an application of a function the model
    interprets, and an [as-array] whose expansion is not exact. *)
let needs_model_eval model expr =
  applies_interpreted_function model expr
  || has_unexpandable_as_array model expr

(* Ask Z3 directly whether an expression is a [lambda].  The OCaml binding
   exposes [is_universal] and [is_existential] but not [is_lambda], so this
   reaches the native entry point, which needs [Obj.magic] to view the
   quantifier as the pointer the binding wraps.

   Preserved from the branch that wrote it, and deliberately **not** what the
   reader below uses: that tests the quantifier's sort kind for [ARRAY_SORT]
   instead, which needs no unsafe cast and is documented at the site.  Kept
   because it is the direct question and a later reader may want it. *)
(* PORTED, UNCALLED. *)
let _is_lambda_native (expr : Z3.Expr.expr) : bool =
  try
    let q = Z3.Quantifier.quantifier_of_expr expr in
    let ptr : Z3native.ptr = Obj.magic q in
    Z3native.is_lambda (Z3native.context_of_ast ptr) ptr
  with exn_ when not (Common.Timer.is_async exn_) -> false

(* Turn a solver's function interpretation into a Z3 [lambda], by folding its
   entries into an [ite] chain over the else-branch.  Preserved from the branch
   that wrote it for reading an array-valued model back when the solver reports
   it as a function rather than as a const/store chain; the model reader below
   decodes a [lambda] exactly, so nothing here calls this today.  Single
   argument only, which is what the assertion says.

   Its tracing went through [print_endline] on the branch; here it goes through
   the module's [Debug.print], like everything else. *)
let interp_to_lambda ctx interp =
  let body = ref (Z3.Model.FuncInterp.get_else interp) in
  let entries = List.rev (Z3.Model.FuncInterp.get_entries interp) in
  assert (not @@ List.is_empty entries);
  List.iter entries ~f:(fun entry ->
      let args = Z3.Model.FuncInterp.FuncEntry.get_args entry in
      assert (List.is_singleton args);
      let arg = List.hd_exn args in
      let expr = Z3.Model.FuncInterp.FuncEntry.get_value entry in
      Debug.print
      @@ lazy
           (sprintf "[interp_to_lambda] %s |-> %s" (Z3.Expr.to_string arg)
              (Z3.Expr.to_string expr));
      let a =
        Z3.Expr.mk_const ctx
          (Z3.Symbol.mk_string ctx "arg")
          (Z3.Arithmetic.Integer.mk_sort ctx)
      in
      body := Z3.Boolean.mk_ite ctx (Z3.Boolean.mk_eq ctx a arg) expr !body);
  let arg =
    Z3.(
      Expr.mk_const ctx
        (Symbol.mk_string ctx "arg")
        (Arithmetic.Integer.mk_sort ctx))
  in
  Z3.Quantifier.(expr_of_quantifier @@ mk_lambda_const ctx [ arg ] !body)

(* The permutation the solver chose, read back as ordinary model entries.

   A query built by [qsat_preamble] carries [perm : Int -> Int] asserted to be
   a bijection of [1..n], and [n] as the constant [#number-of-quantifiers] so
   that the reader need not be told it.  A declaration of arity > 0 is dropped
   by the decoding below -- this tree keeps no interpretation for one -- so the
   choice would be lost; these entries carry it as [#perm-1 … #perm-n], which
   the consumer reads by name.

   The name is looked up without the vertical bars the preamble writes it
   with, because the Z3 API reports a quoted symbol unquoted. *)
(* [decls] is the caller's already-materialised declaration list, not a fresh
   query: see the note in [model_of]. Returns [] -- on every decode of every
   ordinary run -- unless the query was built with the QSAT preamble, which is
   the only thing that declares [#number-of-quantifiers]. *)
(* DUBIOUS: the permutation leaves the model as invented variable names
   [#perm-1] .. [#perm-n], because [model_of] lists a declaration of arity > 0
   with no value. This is a side channel through the name space; the honest
   form is [fun_values_of] below, which decodes [perm]'s interpretation, and
   the channel stays only because its consumer reads these names. *)
let perm_values_of ctx model decls =
  match
    List.find decls ~f:(fun decl ->
        String.equal "#number-of-quantifiers"
        @@ Z3.Symbol.get_string @@ Z3.FuncDecl.get_name decl)
  with
  | None -> []
  | Some count_decl -> (
      match
        ( Z3.Model.get_const_interp model count_decl,
          List.find decls ~f:(fun decl ->
              String.equal "perm"
              @@ Z3.Symbol.get_string @@ Z3.FuncDecl.get_name decl) )
      with
      | Some count, Some perm_decl ->
          (* safe: [#number-of-quantifiers] is defined as the template's
             native-int count, so the model's value is that count *)
          let n = Z.to_int @@ Z3.Arithmetic.Integer.get_big_int count in
          List.filter_mapi (List.init n ~f:Fn.id) ~f:(fun i _ ->
              let i = i + 1 in
              match
                Z3.Model.eval model
                  (Z3.Expr.mk_app ctx perm_decl
                     [ Z3.Arithmetic.Integer.mk_numeral_i ctx i ])
                  false
              with
              | Some v ->
                  Some
                    ( (Ident.Tvar (sprintf "#perm-%d" i), T_int.SInt),
                      Some
                        (T_int.mk_int @@ Z3.Arithmetic.Integer.get_big_int v) )
              | None -> None)
      | _ -> [])

let model_of ctx dtenv model_in =
  let model = model_in in
  (* The declaration list is taken once and shared with the permutation
     reader below.  Asking Z3 for a model's declarations a second time is not
     free: reading a model allocates in the context, and a later query can
     then come back with a different -- equally valid -- model. *)
  let decls =
    try Z3.Model.get_decls model
    with exn_ when not (Common.Timer.is_async exn_) -> Z3.Model.get_func_decls model @ Z3.Model.get_const_decls model
  in
  (* decode entry by entry: one undecodable value must not discard the whole
     model *)
  let warn what e =
    Debug.print
    @@ lazy
         (sprintf
            "[warning] Z3 model entry %s could not be decoded and was dropped: \
             %s"
            what (Exn.to_string e))
  in
  try
    let model =
      List.filter_map
        decls
        ~f:(fun decl ->
          try
            let s =
              Sort.mk_fun
              @@ List.map ~f:(sort_of dtenv)
              @@ Z3.FuncDecl.get_domain decl
              @ [ Z3.FuncDecl.get_range decl ]
            in
            let x =
              InstanceName.decode
                ~sort:(sort_of dtenv @@ Z3.FuncDecl.get_range decl)
              @@ Z3.Symbol.get_string @@ Z3.FuncDecl.get_name decl
            in
            Some
              ( (Ident.Tvar x, s),
                if Z3.FuncDecl.get_arity decl = 0 then
                  match Z3.Model.get_const_interp model decl with
                  | Some expr ->
                      (* the model's own evaluator inlines the interpretations
                         of the functions the value applies, under binders
                         too, and turns an [as-array] of such a function into a
                         [lambda] over its argument, which yields the same
                         value with no function symbol and no unbound variable
                         left in it (Z3 4.15.2); asked only where the plain
                         decoding is wrong, so that every other model is read
                         exactly as before, and its answer is kept only when it
                         is itself free of both shapes *)
                      let expr =
                        if needs_model_eval model expr then
                          match
                            Z3.Model.eval model
                              (Z3.Expr.mk_const_f ctx decl)
                              false
                          with
                          | Some expr' when not (needs_model_eval model expr')
                            ->
                              expr'
                          | _ -> expr
                        else expr
                      in
                      let t =
                        term_of ctx [] [] dtenv
                        @@ expand_as_array ctx model expr
                      in
                      if Term.is_var t then (*ToDo*)
                        LogicOld.add_dummy_term (Term.tvar_of t) s;
                      Some t
                  | None -> None
                else
                  match Z3.Model.get_func_interp model decl with
                  | Some _func ->
                      (* NO VALUE IN THIS LIST, on purpose: a model is
                         applied by substitution, which maps a function symbol
                         only to another symbol (a non-variable replacement
                         raises); the don't-care reading turns an absent value
                         into a fresh dummy function, and several consumers
                         drop the solver's own helpers ([div0], [mod0],
                         [array-ext]) by recognising exactly this absent value.
                         So the entry is kept with no value, which every
                         consumer reads as "any function".  A caller that
                         needs the interpretation reads it with
                         [fun_values_of] below, which decodes it into a value
                         applied per application. *)
                      Debug.print
                      @@ lazy
                           (sprintf
                              "[warning] Z3 model entry %s is a function; the \
                               model carries no value for it (its \
                               interpretation is read by fun_values_of)"
                              x);
                      None
                  | None -> None )
          with e when not (Common.Timer.is_async e) ->
            warn (Z3.FuncDecl.to_string decl) e;
            None)
    in
    (* REACHABLE ON THE DEFAULT PATH. [perm_values_of] scans [decls] for the
       marker the QSAT preamble embeds and returns [] when it is absent, which
       is every ordinary run; the cost is one pass over a list this function
       has already built. *)
    let model = model @ perm_values_of ctx model_in decls in
    Debug.print @@ lazy ("model is: " ^ str_of_model model);
    model
  with e when not (Common.Timer.is_async e) ->
    (* only the declaration enumeration itself can fail here now *)
    warn "(declaration list)" e;
    []

(** The interpretations of the model's declarations of arity greater than
    zero, which [model_of] lists with no value (see the note there), decoded
    into [FunValue.t]: fresh parameters, the table of entries and the default.

    Z3 writes an interpretation's default with the arguments as de Bruijn
    variables, [(:var i)] standing for argument [i]; they are replaced by
    constants named after the fresh parameters and decoded as those.  An entry
    or a default that applies another function the model interprets -- how
    model-based quantifier instantiation writes one, through a projection
    function it invented -- is read through the model's own evaluator, which
    inlines those interpretations; one whose value still applies such a
    function after that is dropped with a warning rather than returned
    denoting something other than the model's function.  A declaration whose
    decoding fails is dropped alone, as in [model_of].

    Guarantees: every returned value meets [FunValue]'s contract -- as many
    parameters as the declaration's arity at its domain sorts, entries of that
    width, and no free variable in the default but the parameters (checked;
    a value violating it is dropped).  Names are decoded as [model_of] decodes
    them, so a value is found under the name the problem gave the function. *)
let fun_values_of ctx dtenv model =
  let decls =
    try Z3.Model.get_decls model
    with exn_ when not (Common.Timer.is_async exn_) ->
      Z3.Model.get_func_decls model
  in
  let warn what msg =
    Debug.print
    @@ lazy
         (sprintf
            "[warning] Z3 function interpretation %s could not be decoded and \
             was dropped: %s"
            what msg)
  in
  List.filter_map decls ~f:(fun decl ->
      if Z3.FuncDecl.get_arity decl = 0 then None
      else
        match Z3.Model.get_func_interp model decl with
        | None -> None
        | Some fi -> (
            try
              let dom = Z3.FuncDecl.get_domain decl in
              let sargs = List.map dom ~f:(sort_of dtenv) in
              let sret = sort_of dtenv @@ Z3.FuncDecl.get_range decl in
              let name =
                InstanceName.decode ~sort:sret @@ Z3.Symbol.get_string
                @@ Z3.FuncDecl.get_name decl
              in
              let params =
                List.map sargs ~f:(fun s -> (Ident.mk_fresh_tvar (), s))
              in
              let consts =
                List.map2_exn params dom ~f:(fun (x, _) zs ->
                    Z3.Expr.mk_const ctx
                      (Z3.Symbol.mk_string ctx
                      @@ String.escaped @@ Ident.name_of_tvar x)
                      zs)
              in
              (* a value that applies an auxiliary function the model
                 interprets is inlined by the model's evaluator; [None] when
                 even that leaves one behind *)
              let settle e =
                let e =
                  if needs_model_eval model e then
                    match Z3.Model.eval model e false with
                    | Some e' when not (needs_model_eval model e') -> Some e'
                    | _ -> None
                  else Some e
                in
                Option.map e ~f:(fun e ->
                    term_of ctx [] [] dtenv @@ expand_as_array ctx model e)
              in
              let entries =
                List.map (Z3.Model.FuncInterp.get_entries fi) ~f:(fun entry ->
                    let args =
                      List.map ~f:settle
                      @@ Z3.Model.FuncInterp.FuncEntry.get_args entry
                    in
                    let v =
                      settle @@ Z3.Model.FuncInterp.FuncEntry.get_value entry
                    in
                    match (Option.all args, v) with
                    | Some args, Some v -> Some (args, v)
                    | _ -> None)
              in
              let default =
                settle
                @@ Z3.Expr.substitute_vars (Z3.Model.FuncInterp.get_else fi)
                     consts
              in
              match (Option.all entries, default) with
              | Some entries, Some default ->
                  let allowed = Set.Poly.of_list @@ List.map ~f:fst params in
                  let stray =
                    Set.diff (Term.fvs_of default) allowed
                    |> Set.union
                         (Set.Poly.union_list
                         @@ List.concat_map entries ~f:(fun (args, v) ->
                             List.map ~f:Term.fvs_of (v :: args)))
                  in
                  if
                    List.exists entries ~f:(fun (args, _) ->
                        List.length args <> List.length params)
                  then (
                    warn name "an entry of the wrong width";
                    None)
                  else if not (Set.is_empty stray) then (
                    warn name
                      ("free variables other than the parameters: "
                      ^ String.concat_map_set ~sep:", " stray
                          ~f:Ident.name_of_tvar);
                    None)
                  else
                    Some
                      ( (Ident.Tvar name, Sort.mk_fun (sargs @ [ sret ])),
                        { FunValue.params; entries; default } )
              | _ ->
                  warn name
                    "a value still applies a function the model interprets";
                  None
            with e when not (Common.Timer.is_async e) ->
              warn (Z3.FuncDecl.to_string decl) (Exn.to_string e);
              None))

(** encoding *)

(* Symbols supplied through the API are their names, not OCaml string literals.
   Escaping here inserted a backslash before a quotation mark in the name,
   while [pred_decl_of] retained the original name, splitting a Boolean used
   in formula and term positions. Z3's
   printer is responsible for quoting a symbol when it serializes an expression. *)
let of_var ctx (Ident.Tvar var) = Z3.Symbol.mk_string ctx var
let list_type s ctx = Z3.Z3List.mk_sort ctx (Z3.Symbol.mk_string ctx "list") s
let array_type t1 t2 ctx = Z3.Z3Array.mk_sort ctx t1 t2
let sorts_of_tuple sort = sort |> Z3.Tuple.get_mk_decl |> Z3.FuncDecl.get_domain

(* Conversion from sorts to Z3 sorts *)

let str_of_z3_env env =
  Set.fold ~init:"z3_env:" env ~f:(fun ret (dt, sort) ->
      sprintf "%s\nLogicOld: %s\nZ3: %s\n%s\n%s" ret (Datatype.str_of dt)
        (Z3.Sort.to_string sort)
        (String.concat_map_list ~sep:"\n"
           (List.zip_exn
              (Z3.Datatype.get_constructors sort)
              (Z3.Datatype.get_accessors sort))
           ~f:(fun (cons, sels) ->
             String.concat ~sep:"\n"
             @@ sprintf "(#%d) %s" (Z3.FuncDecl.get_id cons)
                  (Z3.FuncDecl.to_string cons)
                :: List.map sels ~f:(fun sel ->
                    sprintf "(#%d) %s" (Z3.FuncDecl.get_id sel)
                      (Z3.FuncDecl.to_string sel))))
        (String.concat_map_list ~sep:"\n" (Z3.Datatype.get_recognizers sort)
           ~f:(fun iscons ->
             sprintf "(#%d) %s"
               (Z3.FuncDecl.get_id iscons)
               (Z3.FuncDecl.to_string iscons))))

(* Display names still index actual datatypes. Until registration/export use
   structural names too, a same-spelled instance must be refused rather than
   silently returned for different parameters. This key never expands fields. *)
let check_datatype_instance declared requested =
  if
    (not (phys_equal declared requested))
    && not
         (Sexp.equal
            (sus_sort_key (T_dt.SDT declared))
            (sus_sort_key (T_dt.SDT requested)))
  then
    failwith
    @@ sprintf "[z3] datatype instance collision for %s: %s versus %s"
         (Datatype.full_name_of requested)
         (Sexp.to_string (sus_sort_key (T_dt.SDT declared)))
         (Sexp.to_string (sus_sort_key (T_dt.SDT requested)))

let find_z3_datatype dtenv dt =
  let found =
    Set.find dtenv
      ~f:
        (fst >> Datatype.full_name_of >> String.( = ) (Datatype.full_name_of dt))
  in
  Option.iter found ~f:(fun (declared, _) ->
      check_datatype_instance declared dt);
  found

let rec of_sort ctx dtenv = function
  | Sort.SVar (Ident.Svar svar) ->
      Z3.Sort.mk_uninterpreted_s ctx @@ unint_svar_prefix ^ svar
  (*| Sort.SArrow (s1, (s2, Sort.Pure)) ->
    Z3Array.mk_sort ctx (of_sort ctx dtenv s1) (of_sort ctx dtenv s2)*)
  | Sort.SArrow (_, _) as s ->
      Z3.Sort.mk_uninterpreted_s ctx @@ unint_arrow_prefix ^ Term.str_of_sort s
  | T_bool.SBool -> Z3.Boolean.mk_sort ctx
  | T_int.SInt -> Z3.Arithmetic.Integer.mk_sort ctx
  | T_real.SReal -> Z3.Arithmetic.Real.mk_sort ctx
  | T_bv.SBV size -> Z3.BitVector.mk_sort ctx (T_bv.bits_of size)
  | T_tuple.STuple sorts -> tuple_sort_of ctx dtenv sorts
  | T_dt.SUS (name, params) ->
      (* one Z3 sort per instantiation; [sort_of] inverts the name through
         [sus_instances] *)
      Z3.Sort.mk_uninterpreted_s ctx (z3_name_of_sus name params)
  | T_dt.SDT dt when Datatype.is_undef dt ->
      (* API callers may still carry an uninterpreted declaration as a datatype.
         Resolve it structurally, without a display-name environment lookup. *)
      of_sort ctx dtenv (Datatype.sort_of dt)
  | T_dt.SDT dt -> (
      match find_z3_datatype dtenv dt with
      | Some (_, sort) -> sort
      | None ->
          Debug.print
          @@ lazy
               (sprintf "[z3:of_sort] adding %s to %s"
                  (Term.str_of_sort @@ T_dt.SDT dt)
                  (str_of_z3_env dtenv));
          of_sort ctx (update_z3env ctx dtenv dt) (T_dt.SDT dt))
  | T_array.SArray (si, se) ->
      Z3.Z3Array.mk_sort ctx (of_sort ctx dtenv si) (of_sort ctx dtenv se)
  | T_seq.SSeq se ->
      let z3sort = Z3.Seq.mk_seq_sort ctx (of_sort ctx dtenv se) in
      with_pool_lock (fun () ->
          Hashtbl.Poly.set seq_instances
            ~key:(Z3.Sort.to_string z3sort)
            ~data:(T_seq.SSeq se));
      z3sort
  | T_trace.STrace fin ->
      Z3.Sort.mk_uninterpreted_s ctx
        (if fin then unint_fintrace else unint_inftrace)
  | T_string.SString -> Z3.Seq.mk_string_sort ctx
  | T_regex.SRegEx -> Z3.Seq.mk_re_sort ctx @@ Z3.Seq.mk_string_sort ctx
  | sort ->
      failwith @@ sprintf "[z3:of_sort] %s is unknown" @@ Term.str_of_sort sort

and tuple_sort_of ctx dtenv sorts =
  let tuple_num = List.length sorts in
  Z3.Tuple.mk_sort ctx
    (Z3.Symbol.mk_string ctx
    @@ sprintf "%s(%s)" unint_tuple_prefix
    (*tuple_num*)
    @@ String.concat_map_list ~sep:"," ~f:Term.short_name_of_sort sorts)
    (* (tuple_prefix ^ string_of_int tuple_num |> Idnt.make |> sym_of_var) *)
    (List.init tuple_num ~f:(fun i ->
         Z3.Symbol.mk_string ctx @@ unint_tuple_sel_prefix ^ string_of_int i))
    (List.map sorts ~f:(of_sort ctx dtenv))

(* Two datatypes can carry constructors of the same name -- one parametric
   datatype instantiated twice gives [int Lst] and [bool Lst], each with [nil]
   and [cons] -- and Z3's API accepts that, because a term built through it
   names a declaration and not a symbol.  A *printed* file has only the symbol:
   `nil` there stands for two constructors of two sorts, and every reader of the
   file is then stuck.  Z3 itself answers "ambiguous constant reference ... use
   a qualified expression (as nil <sort>)" and, having said so, goes on to
   answer about the assertions it could read.  So a printer asks for the names
   to be made distinct, and nothing else does: within this process a constructor
   is found by position against our own datatype and a declaration is decoded by
   its identity, so what the symbol is called changes nothing. *)
and update_z3env ?(qualify = fun _dt_name name -> name) ?(pending = []) ctx
    dtenv t =
  if Datatype.is_dt t then (
    ignore (find_z3_datatype dtenv t);
    if
      List.exists pending ~f:(fun key ->
          Sexp.equal key (sus_sort_key (T_dt.SDT t)))
    then
      failwith
      @@ sprintf "[z3] cyclic datatype field dependency for %s"
           (Datatype.full_name_of t));
  match Datatype.flag_of t with
  | Undef ->
      (* [declare-sort S n] with [n > 0] arrives here as an [Undef] datatype
         whose [params] are the instantiation; name the Z3 sort by them too *)
      Set.add dtenv
        ( t,
          Z3.Sort.mk_uninterpreted_s ctx
            (z3_name_of_sus (Datatype.name_of t) (Datatype.params_of t)) )
  | Alias _ | FCodt -> failwith "not supported"
  | FDt ->
      let dts =
        List.filter_map (Datatype.full_dts_of t) ~f:(fun dt ->
            if List.is_empty @@ Datatype.conses_of_dt dt then None else Some dt)
      in
      (* Field encoding can create another datatype, but [of_sort] returns
         only a sort. Register those dependencies first and keep the resulting
         environment for both the fields and the eventual model decoder.
         [InSel] references within this group stay in [mk_sorts_s]'s reference
         array; following them as external dependencies would recurse forever. *)
      let pending =
        List.map dts ~f:(fun dt ->
            sus_sort_key
              (T_dt.SDT (Datatype.update_name t (Datatype.name_of_dt dt))))
        @ pending
      in
      let rec register_sort env = function
        | T_dt.SDT dt when Datatype.is_undef dt ->
            register_sorts env (Datatype.params_of dt)
        | T_dt.SDT dt -> (
            match find_z3_datatype env dt with
            | Some _ -> env
            | None -> update_z3env ~qualify ~pending ctx env dt)
        | T_array.SArray (index, elem) -> register_sorts env [ index; elem ]
        | T_seq.SSeq elem | T_ref.SRef elem -> register_sort env elem
        | T_tuple.STuple elems | T_dt.SUS (_, elems) -> register_sorts env elems
        | _ -> env
      and register_sorts env sorts =
        List.fold sorts ~init:env ~f:register_sort
      in
      let dtenv =
        List.fold dts ~init:dtenv ~f:(fun env dt ->
            List.fold (Datatype.conses_of_dt dt) ~init:env ~f:(fun env cons ->
                List.fold (Datatype.sels_of_cons cons) ~init:env
                  ~f:(fun env -> function
                  | Datatype.Sel (_, sort) -> register_sort env sort
                  | Datatype.InSel _ -> env)))
      in
      let sorts =
        Tuple2.uncurry (Z3.Datatype.mk_sorts_s ctx)
        @@ List.unzip
        @@ List.map dts ~f:(fun dt ->
            let dt_name = Datatype.full_name_of_dt dt in
            ( dt_name,
              List.map (Datatype.conses_of_dt dt) ~f:(fun cons ->
                  let name = qualify dt_name (Datatype.name_of_cons cons) in
                  Debug.print
                  @@ lazy
                       (sprintf "[update_z3env] %s constructor: %s" dt_name name);
                  let is_cons_name =
                    Z3.Symbol.mk_string ctx @@ unint_is_cons_prefix ^ name
                  in
                  Debug.print
                  @@ lazy
                       (sprintf "[update_z3env] %s tester: %s" dt_name
                       @@ Z3.Symbol.get_string is_cons_name);
                  let sels_names, ret_sorts, ref_sorts =
                    List.fold_left (Datatype.sels_of_cons cons)
                      ~init:([], [], [])
                      ~f:(fun (sels_names, ret_sorts, ref_sorts) -> function
                      | Datatype.Sel (name, ret_sort) ->
                          let name = qualify dt_name name in
                          Debug.print
                          @@ lazy
                               (sprintf "[update_z3env] %s accessor: %s" dt_name
                                  name);
                          ( Z3.Symbol.mk_string ctx name :: sels_names,
                            Some (of_sort ctx dtenv ret_sort) :: ret_sorts,
                            0 :: ref_sorts )
                      | Datatype.InSel (name, ret_name, args) -> (
                          Debug.print
                          @@ lazy
                               (sprintf "[update_z3env] %s rec. accessor: %s"
                                  dt_name name);
                          let target =
                            Datatype.make ret_name
                              [ Datatype.mk_dt ret_name args ]
                              FDt
                          in
                          match find_z3_datatype dtenv target with
                          | Some (_, sort) ->
                              ( Z3.Symbol.mk_string ctx (qualify dt_name name)
                                :: sels_names,
                                Some sort :: ret_sorts,
                                0 :: ref_sorts )
                          | None -> (
                              match
                                List.findi dts ~f:(fun _ ->
                                    Datatype.name_of_dt >> String.( = ) ret_name)
                              with
                              | Some (i, member) ->
                                  (* A local index names exactly this instance.
                                     Pending inference must not turn a different
                                     recursive target into that index. *)
                                  check_datatype_instance
                                    (Datatype.make ret_name [ member ] FDt)
                                    target;
                                  if false then
                                    Debug.print @@ lazy (sprintf "ref id:%d" i);
                                  ( Z3.Symbol.mk_string ctx
                                      (qualify dt_name name)
                                    :: sels_names,
                                    None :: ret_sorts,
                                    i :: ref_sorts )
                              | _ -> assert false)))
                  in
                  let z3cons =
                    Z3.Datatype.mk_constructor ctx
                      (Z3.Symbol.mk_string ctx name)
                      is_cons_name (List.rev sels_names) (List.rev ret_sorts)
                      (List.rev ref_sorts)
                  in
                  if false then (
                    Debug.print
                    @@ lazy
                         ("z3 tester: " ^ Z3.FuncDecl.to_string
                         @@ Z3.Datatype.Constructor.get_tester_decl z3cons);
                    List.iter
                      (Z3.Datatype.Constructor.get_accessor_decls z3cons)
                      ~f:(fun sel ->
                        Debug.print
                        @@ lazy ("z3 sel:" ^ Z3.FuncDecl.to_string sel)));
                  z3cons) ))
      in
      List.fold2_exn dts sorts ~init:dtenv ~f:(fun dtenv dt sort ->
          Set.add dtenv
            ( Datatype.update_name (Datatype.update_dts t dts)
              @@ Datatype.name_of_dt dt,
              sort ))

and z3_dtenv_of_dtenv ?(init = Set.Poly.empty) ?(disambiguate_among = []) ctx
    dtenv =
  if false then
    Debug.print @@ lazy (sprintf "mk z3 dtenv from:\n%s" @@ DTEnv.str_of dtenv);
  (* A name is qualified only where it would otherwise stand for two things, so
     a problem whose datatypes do not collide prints exactly as before. *)
  (* [disambiguate_among] names the datatypes a caller is about to *write*, and
     a name is qualified only where two of those would spell it the same.  A
     caller that writes nothing passes nothing and every name is left alone. *)
  let qualify =
    if List.is_empty disambiguate_among then fun _ name -> name
    else
      let counts = Stdlib.Hashtbl.create 64 in
      (* count over the datatypes that will actually be declared, which is what
         the fold below emits: one per distinct full name, the rest skipped.
         Counting over the environment's entries instead reports a collision
         between an instantiation and the template it came from, and qualifies
         names in files that declare one datatype and are not ambiguous at
         all. *)
      List.iter (Map.Poly.data dtenv) ~f:(fun data ->
          List.iter (Datatype.full_dts_of data) ~f:(fun dt ->
              if
                List.mem disambiguate_among
                  (Datatype.full_name_of_dt dt)
                  ~equal:String.equal
              then
                let owner = Datatype.full_name_of_dt dt in
                List.iter (Datatype.conses_of_dt dt) ~f:(fun cons ->
                    let note n =
                      let owners =
                        try Stdlib.Hashtbl.find counts n
                        with Stdlib.Not_found -> []
                      in
                      if not (List.mem owners owner ~equal:String.equal) then
                        Stdlib.Hashtbl.replace counts n (owner :: owners)
                    in
                    note (Datatype.name_of_cons cons);
                    List.iter (Datatype.sels_of_cons cons) ~f:(function
                        | Datatype.Sel (n, _) | Datatype.InSel (n, _, _) ->
                        note n))));
      fun dt_name name ->
        match Stdlib.Hashtbl.find_opt counts name with
        | Some (_ :: _ :: _) -> name ^ "@" ^ dt_name
        | _ -> name
  in
  (* Keep declared names and their instances indexed, recomputing only after
     an addition. Scanning [env] for every skipped declaration was costly on
     inputs with hundreds of datatypes. Presence still selects the skip branch,
     but actual datatypes must also have matching structural instance keys.
     Retaining the instance beside the name permits that check without
     restoring the per-declaration scan. *)
  let names_of env =
    Set.fold env ~init:Map.Poly.empty ~f:(fun names (dt, _) ->
        let name = Datatype.full_name_of dt in
        Option.iter (Map.Poly.find names name) ~f:(fun declared ->
            if Datatype.is_dt dt then check_datatype_instance declared dt);
        Map.Poly.set names ~key:name ~data:dt)
  in
  let z3_dtenv, _ =
    Map.Poly.fold dtenv
      ~init:(init, names_of init)
      ~f:(fun ~key ~data (env, names) ->
        if false then
          Debug.print
          @@ lazy (sprintf "mk sort:%s \n%s" key (Datatype.str_of data));
        let name = Datatype.full_name_of data in
        match Map.Poly.find names name with
        | Some declared ->
            if Datatype.is_dt data then check_datatype_instance declared data;
            (env, names)
        | None ->
            let env = update_z3env ~qualify ctx env data in
            (env, names_of env))
  in
  if false then Debug.print @@ lazy (str_of_z3_env z3_dtenv);
  z3_dtenv

let z3_dtenv_of_formula ?(init = Set.Poly.empty) ctx phi =
  update_dtenv @@ DTEnv.of_formula phi;
  Debug.print
  @@ lazy (sprintf "[z3_dtenv_of] from:\n%s" @@ DTEnv.str_of @@ get_dtenv ());
  z3_dtenv_of_dtenv ~init ctx @@ get_dtenv ()

let z3_dt_of (dtenv : dtenv) dt =
  match find_z3_datatype dtenv dt with
  | Some (_, sort) -> sort
  | None ->
      (* Do not relabel a collision, interrupt or exhausted budget as a
         missing datatype. Only an absent lookup gets this diagnostic. *)
      failwith
      @@ sprintf
           "[z3_dt_of] %s not found among the %d datatype(s) declared to the \
            solver: %s"
           (Datatype.full_name_of dt) (Set.length dtenv)
           (String.concat ~sep:", "
           @@ List.map ~f:(fst >> Datatype.full_name_of)
           @@ Set.to_list dtenv)

let z3_cons_of (dtenv : dtenv) dt name =
  List.find_map_exn
    (List.zip_exn (Datatype.conses_of dt)
       (Z3.Datatype.get_constructors @@ z3_dt_of dtenv dt))
    ~f:(fun (cons, z3_cons) ->
      if String.(Datatype.name_of_cons cons = name) then Some z3_cons else None)

let z3_sel_of (dtenv : dtenv) dt name =
  List.find_map_exn
    (List.zip_exn (Datatype.conses_of dt)
       (Z3.Datatype.get_accessors @@ z3_dt_of dtenv dt))
    ~f:(fun (cons, z3_sels) ->
      List.find_map
        (List.zip_exn (Datatype.sels_of_cons cons) z3_sels)
        ~f:(fun (sel, z3_sel) ->
          if String.(name = Datatype.name_of_sel sel) then Some z3_sel else None))

let z3_iscons_of (dtenv : dtenv) dt name =
  List.find_map_exn
    (List.zip_exn (Datatype.conses_of dt)
       (Z3.Datatype.get_recognizers @@ z3_dt_of dtenv dt))
    ~f:(fun (cons, z3_tester) ->
      if String.(Datatype.name_of_cons cons = name) then Some z3_tester
      else None)

let z3_epsilon ctx =
  Z3.FuncDecl.mk_func_decl_s ctx unint_epsilon []
  @@ Z3.Sort.mk_uninterpreted_s ctx unint_fintrace

let z3_symbol_of ctx str =
  Z3.FuncDecl.mk_func_decl_s ctx
    (unint_symbol_prefix ^ str (*ToDo: need to avoid escaping by z3?*))
    []
  @@ Z3.Sort.mk_uninterpreted_s ctx unint_fintrace

let z3_concat ctx fin =
  let sort =
    if fin then Z3.Sort.mk_uninterpreted_s ctx unint_fintrace
    else Z3.Sort.mk_uninterpreted_s ctx unint_inftrace
  in
  Z3.FuncDecl.mk_func_decl_s ctx
    (if fin then unint_concat_fin else unint_concat_inf)
    [ Z3.Sort.mk_uninterpreted_s ctx unint_fintrace; sort ]
    sort

let z3_is_prefix_of ctx fin =
  Z3.FuncDecl.mk_func_decl_s ctx
    (if fin then unint_is_prefix_of_fin else unint_is_prefix_of_inf)
    [
      Z3.Sort.mk_uninterpreted_s ctx unint_fintrace;
      (Z3.Sort.mk_uninterpreted_s ctx
      @@ if fin then unint_fintrace else unint_inftrace);
    ]
    (Z3.Boolean.mk_sort ctx)

let z3_is_in_reg_exp ctx fin regexp =
  let name =
    (if fin then unint_is_in_reg_exp_fin_prefix
     else unint_is_in_reg_exp_inf_prefix)
    ^ String.paren
    @@ Grammar.RegWordExp.str_of Fn.id regexp
  in
  (* keyed by the name as the decoder will read it back, which is without
     the vertical bars an alternation prints *)
  record_trace_regexp (unescape_z3 name) regexp;
  Z3.FuncDecl.mk_func_decl_s ctx name
    [
      (Z3.Sort.mk_uninterpreted_s ctx
      @@ if fin then unint_fintrace else unint_inftrace);
    ]
    (Z3.Boolean.mk_sort ctx)

(* The real algebraic number [T_real.Alge n] over [poly]: the [n]-th real root,
   counted from 1 in increasing order, of the univariate polynomial [poly] in
   the variable [x] -- exactly Z3's [root-obj], which is what the decoder reads
   it from.  The OCaml binding has no constructor for one, but Z3's SMT-LIB
   parser accepts [root-obj], so the number is written in that syntax and
   parsed; the polynomial is printed here from the shapes [parse_root_obj]
   builds (the variable, numerals, negation, sums, products, powers), so that
   no printer of this tree's terms is relied on. *)
let alge_of ctx poly n =
  let num q =
    let a = Q.abs q in
    let s =
      if Z.equal (Q.den a) Z.one then Z.to_string (Q.num a)
      else sprintf "(/ %s %s)" (Z.to_string (Q.num a)) (Z.to_string (Q.den a))
    in
    if Q.sign q < 0 then sprintf "(- %s)" s else s
  in
  let rec pr = function
    | Term.Var (Ident.Tvar "x", _, _) -> "x"
    | Term.FunApp (T_real.Real q, [], _) -> num q
    | Term.FunApp (T_int.Int z, [], _) -> num (Q.of_bigint z)
    | Term.FunApp (T_real.RNeg, [ t ], _) -> sprintf "(- %s)" (pr t)
    | Term.FunApp (T_real.RAdd, [ t1; t2 ], _) ->
        sprintf "(+ %s %s)" (pr t1) (pr t2)
    | Term.FunApp (T_real.RMul, [ t1; t2 ], _) ->
        sprintf "(* %s %s)" (pr t1) (pr t2)
    | Term.FunApp (T_real.RPower, [ t1; t2 ], _) ->
        sprintf "(^ %s %s)" (pr t1) (pr t2)
    | t ->
        failwith
        @@ sprintf
             "[z3:of_term] %s is not a polynomial in x, so the algebraic \
              number over it cannot be encoded"
             (Term.str_of t)
  in
  let src =
    sprintf "(declare-const |#alge| Real)(assert (= |#alge| (root-obj %s %d)))"
      (pr poly) n
  in
  match
    Z3.AST.ASTVector.to_expr_list @@ Z3.SMT.parse_smtlib2_string ctx src [] [] [] []
  with
  | [ eq ] -> (
      match Z3.Expr.get_args eq with
      | [ _; v ] when Z3.Arithmetic.is_algebraic_number v || Z3.Arithmetic.is_rat_numeral v -> v
      | _ -> failwith @@ "[z3:of_term] root-obj did not parse to a number: " ^ src)
  | _ -> failwith @@ "[z3:of_term] root-obj did not parse: " ^ src

let pred_decl_of ctx dtenv (pvar, sorts) =
  ( pvar,
    Z3.FuncDecl.mk_func_decl_s ctx (Ident.name_of_pvar pvar)
      (List.map sorts ~f:(of_sort ctx dtenv))
      (Z3.Boolean.mk_sort ctx) )

let mk_tdiv ctx a b =
  let zero = Z3.Arithmetic.Integer.mk_numeral_i ctx 0 in
  Z3.Arithmetic.mk_add ctx
    [
      Z3.Arithmetic.mk_div ctx a b;
      Z3.Boolean.mk_ite ctx
        (Z3.Boolean.mk_eq ctx (Z3.Arithmetic.Integer.mk_mod ctx a b) zero)
        zero
        (Z3.Boolean.mk_ite ctx
           (Z3.Arithmetic.mk_ge ctx a zero)
           zero
           (Z3.Boolean.mk_ite ctx
              (Z3.Arithmetic.mk_ge ctx b zero)
              (Z3.Arithmetic.Integer.mk_numeral_i ctx 1)
              (Z3.Arithmetic.Integer.mk_numeral_i ctx (-1))));
    ]

let mk_tmod ctx a b =
  Z3.Arithmetic.mk_sub ctx
    [ a; Z3.Arithmetic.mk_mul ctx [ b; mk_tdiv ctx a b ] ]

(* WHICH Z3 DEFECTS THIS PROCESS STILL HAS TO WORK AROUND.

   Two workarounds below exist for defects of Z3 4.x that Z3 5.1.0 no longer
   has: the rewrite of an equality between array literals over a finite index
   sort (a wrong [sat] in 4.15.2), and the refusal to ask a query that mentions
   a regular expression (a call that did not return in 4.15.2, whatever budget
   it was given).  Each is switched on exactly when the Z3 LIBRARY this process
   is linked against -- read at run time, not at build time -- has major
   version below 5, so a build against a 4.x library stays defended.

   What 5.1.0 was checked on: the array-literal equality over thirty-seven
   variants (enumerations of one to three elements, Bool, records, an
   option-like datatype, arrays of arrays two and three deep, Int values, a
   free default, variable and repeated store indices, a free array variable
   bound to the literal, the equality under an [ite], under an existential and
   under a universal, the disequality, and the question asked after a
   [push]/[pop] or after earlier assertions), every answer correct where 4.15.2
   answered twenty-one of them wrongly; the regular-expression queries that
   4.15.2 did not return from (free regex variables under union, complement
   and intersection), each answered within 0.2 s under a 3 s budget.  A test
   asks the same shapes of the linked library and fails if a gate is off while
   the defect is present.

   The switches are writable only so that a test can exercise both sides in
   one build; nothing else sets them, and they are read, never written, once
   solving has started. *)
let z3_major_version = Z3.Version.major

let finite_array_literal_eq_rewrite = Atomic.make (z3_major_version < 5)
let regex_query_refusal = Atomic.make (z3_major_version < 5)

(* WORKAROUND FOR A SOLVER DEFECT, ON ONLY FOR A Z3 LIBRARY OLDER THAN 5
   ([finite_array_literal_eq_rewrite] above; Z3 5.1.0 answers every variant of
   the shape below correctly).  The reproducer that says whether a given Z3
   still has it lives beside the benchmarks and is named for it.

   Z3 4.15.2 does not answer an equality between two constant-array literals
   whose INDEX SORT IS FINITE.  Asked whether [store (const true) a0 false =
   const false] over a two-element sort it answers [sat], and in the same model
   reports the two arrays differing at the very index the equality constrains;
   it answers [sat] to the negation as well.  cvc5 answers [unsat], and with an
   [Int] index both solvers are right.  The index sort need not be an
   enumeration: the same wrong [sat] comes back over [Bool] and over a record
   whose fields are finite -- [store (const true) (mk f0 f1) false = const
   false] with [mk] a two-field constructor over a two-element sort -- which is
   what a front end that monomorphises by name makes of [Mut<T>] once [T] has
   been fixed to a finite sort.  The literature names the same boundary:
   Preiner, Niemetz and Barrett, "Satisfiability Modulo Extensional Constant
   Arrays", observe that existing implementations support only a fragment of
   the theory for finite index domains and give a procedure for arbitrary ones.

   It matters here because several callers read [Sat] as PERMISSION to take a
   step rather than as a report, so a wrong [sat] becomes a wrong [unsat] for a
   whole problem -- one was produced on a shipped benchmark by a resolution step
   that derived a negative example not following from its clause, and another
   by a conflict between two examples whose arguments were two different
   literals over [Mut<T>] and were taken to be equal.

   Over a finite index sort the equality is decidable by reading every element,
   which is exact rather than approximate, and both solvers then answer it
   correctly.  So it is rewritten before being asked.  It is done at this
   boundary and not at one caller because the defect is the solver's: every site
   that asks such a question inherits it. *)

(* The elements of a finite index sort, as ground terms: [Bool], and a datatype
   every constructor of which has only fields that are themselves such sorts.
   The walk is depth-bounded, which is what makes a recursive datatype answer
   [None] rather than diverge, and the element count is bounded, since past it
   the rewrite hands the solver more reads than the literal it replaces. *)
let elements_of_finite_index =
  let max_elements = 64 in
  let max_depth = 4 in
  let rec elements depth srt =
    if depth > max_depth then None
    else
      match srt with
      | T_bool.SBool -> Some [ T_bool.mk_true (); T_bool.mk_false () ]
      | T_dt.SDT dt when not (List.is_empty (Datatype.conses_of dt)) ->
          let per_cons c =
            Option.bind
              (Option.all
              @@ List.map (Datatype.sorts_of_cons dt c)
                   ~f:(elements (depth + 1)))
              ~f:(fun choices ->
                (* the size is checked before the product is built *)
                let size =
                  List.fold choices ~init:1 ~f:(fun acc es ->
                      if acc > max_elements then acc else acc * List.length es)
                in
                if size > max_elements then None
                else
                  Some
                    (List.map
                       (List.fold_right choices ~init:[ [] ] ~f:(fun es acc ->
                            List.concat_map es ~f:(fun e ->
                                List.map acc ~f:(fun tl -> e :: tl))))
                       ~f:(fun args ->
                         T_dt.mk_cons dt (Datatype.name_of_cons c) args)))
          in
          Option.bind
            (Option.all @@ List.map (Datatype.conses_of dt) ~f:per_cons)
            ~f:(fun ls ->
              let es = List.concat ls in
              if List.length es <= max_elements then Some es else None)
      | _ -> None
  in
  elements 0

(* [Some b] when two terms built only from constructors and boolean constants
   are ([b = true]) or are not ([b = false]) the same value; [None] when either
   is anything else, which leaves the question to the solver *)
let rec ground_value_equal t1 t2 =
  match (t1, t2) with
  | ( Term.FunApp (T_dt.DTCons (n1, _, _), args1, _),
      Term.FunApp (T_dt.DTCons (n2, _, _), args2, _) ) ->
      if not (String.equal n1 n2) then Some false
      else if List.length args1 <> List.length args2 then None
      else
        List.fold2_exn args1 args2 ~init:(Some true) ~f:(fun acc a b ->
            match acc with
            | Some true -> ground_value_equal a b
            | other -> other)
  | _ ->
      if (T_bool.is_true t1 || T_bool.is_false t1)
         && (T_bool.is_true t2 || T_bool.is_false t2)
      then Some (Bool.equal (T_bool.is_true t1) (T_bool.is_true t2))
      else None

let array_sorts_of_literal = function
  | Term.FunApp (T_array.AConst (si, se), _, _) -> Some (si, se)
  | Term.FunApp (T_array.AStore (si, se), _, _) -> Some (si, se)
  | _ -> None

(* whether [t1 = t2] is an equality the expansion below rewrites: one side an
   array literal whose index sort is finite *)
let is_finite_array_literal_eq t1 t2 =
  match
    match array_sorts_of_literal t1 with
    | Some p -> Some p
    | None -> array_sorts_of_literal t2
  with
  | Some (si, _) -> (
      match elements_of_finite_index si with Some (_ :: _) -> true | _ -> false)
  | None -> false

(* A read of a literal at a constructor of a finite index sort, computed rather
   than left to the solver: [select (const v) e] is [v], and
   [select (store a i v) e] is [v] when [i] and [e] are the same ground value
   and [select a e] when they are different ones.  Anything else
   stays a [select].

   The computing is what makes the expansion below complete.  A curried
   universal function over the finite sort is an array whose VALUE is again an
   array, so reading an equality of two such literals at each element leaves
   equalities between the values, and those are literals of array sort once
   more -- the very equality the solver answers wrongly, one level down.  Left
   as [select (const (store ...)) e] the value is not syntactically a literal,
   the expansion did not look inside it, and the solver was handed
   [const (store (const (const true)) b0 (const false)) =
    const (const (const false))] over two two-element sorts, answered [sat], and
   a conflict between two examples that do not unify refuted a satisfiable
   instance. *)
let rec read_finite_literal si se t e =
  match t with
  | Term.FunApp (T_array.AConst _, [ v ], _) -> v
  | Term.FunApp (T_array.AStore _, [ a; i; v ], _) -> (
      match ground_value_equal i e with
      | Some true -> v
      | Some false -> read_finite_literal si se a e
      | None -> T_array.mk_select si se t e)
  | _ -> T_array.mk_select si se t e

(* Recursive: an element read off the equality is again an equality, and when
   its sides are array literals over a finite index it is expanded in turn,
   down to the first element sort that is not such an array.  It terminates
   because each level strips one array constructor from the sort. *)
let rec expand_finite_array_eq_atom atom =
  match atom with
  | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) -> (
      match
        match array_sorts_of_literal t1 with
        | Some p -> Some p
        | None -> array_sorts_of_literal t2
      with
      | Some (si, se) -> (
          match elements_of_finite_index si with
          | Some (_ :: _ as es) ->
              Formula.and_of
              @@ List.map es ~f:(fun e ->
                     expand_finite_array_eq_atom
                     @@ T_bool.mk_eq
                          (read_finite_literal si se t1 e)
                          (read_finite_literal si se t2 e))
          | _ -> Formula.mk_atom atom)
      | None -> Formula.mk_atom atom)
  | _ -> Formula.mk_atom atom

(* The rewrite whatever the linked library: for a query whose TEXT may go to a
   Z3 process of another version (see [elimination_solver]), the rewrite being
   exact and the process's version unknown here. *)
let expand_finite_array_eqs_always phi =
  Formula.fold phi
    ~f:
      (object
         method fatom atom = expand_finite_array_eq_atom atom
         method fand p1 p2 = Formula.mk_and p1 p2
         method for_ p1 p2 = Formula.mk_or p1 p2
         method fnot p1 = Formula.mk_neg p1
         method fimply p1 p2 = Formula.mk_imply p1 p2
         method fiff p1 p2 = Formula.mk_iff p1 p2
         method fxor p1 p2 = Formula.mk_xor p1 p2
         method fletrec funcs p1 = Formula.mk_letrec funcs p1
         method flet var sort def body = Formula.mk_let_formula var sort def body
         method fbind binder senv p1 = Formula.mk_bind binder senv p1
      end)

(* The rewrite for a query this process asks its own library: the identity
   where that library answers the equality correctly *)
let expand_finite_array_eqs phi =
  if Atomic.get finite_array_literal_eq_rewrite then
    expand_finite_array_eqs_always phi
  else phi

(* WORKAROUND FOR A SOLVER DEFECT OF Z3 5.1.0 (the default library), ON FOR
   EVERY VERSION.

   Z3 5.1.0 answers [sat] to an equality between two [store]s whose base is an
   array [lambda]: [store (lambda x. x) 7 0 = store (const 3) 7 0] and
   [store (lambda x. x) 7 0 = store (lambda x. 3) 7 0] are both answered
   [sat], although the two sides differ at index [0]; the same happens with
   the [lambda] bound to an array variable by an equation.  The equality
   without the [store]s, or with a [store] on one side only, is answered
   correctly, and so is the extensional form
   [forall x. ite (x = 7, 0, x) = ite (x = 7, 0, 3)] ([unsat]).  The
   reproducer is [benchmarks/SMT/simple/z3_lambda_store_eq_unsound.smt2].

   It matters because a [lambda] is how a model is read back into an example
   (an array the solver gave as a function, or one an elimination rebuilt from
   its cells), and the labeling asks whether two examples' arguments CAN be
   equal and reads [sat] as a refutation step: two different arrays were taken
   to be the same atom, a negative example was derived for a reachable state,
   and a satisfiable problem answered [unsat].

   So an equality between two array terms one of which contains a [lambda] is
   handed to the solver extensionally, [forall x. t1[x] = t2[x]], with the
   reads computed where the term says what they are ([select] through [store]
   as an [ite], a [lambda] applied by substitution, a constant array as its
   value).  This is exact in every model of the array theory (extensionality),
   and an element that is again an array equality containing a [lambda] is
   rewritten in turn when it is converted, down to an element sort that is
   not an array.  Writable only so that a test can exercise both sides. *)
let lambda_array_eq_rewrite = Atomic.make true

let rec term_contains_lambda (t : Term.t) =
  match t with
  | Term.Var _ -> false
  | Term.FunApp (T_array.ALambda _, _, _) -> true
  | Term.FunApp (_, args, _) -> List.exists args ~f:term_contains_lambda
  | Term.LetTerm (_, _, def, body, _) ->
      term_contains_lambda def || term_contains_lambda body

let is_lambda_array_eq t1 t2 =
  Atomic.get lambda_array_eq_rewrite
  && (match Term.sort_of t1 with T_array.SArray _ -> true | _ -> false)
  && (term_contains_lambda t1 || term_contains_lambda t2)

(* [t[x]], computed through [store], [lambda] and constant arrays; a [select]
   anywhere else.  [x] is a fresh variable, so substituting it into a
   [lambda]'s body captures nothing. *)
let rec read_array_at si se (t : Term.t) x =
  match t with
  | Term.FunApp (T_array.AConst _, [ v ], _) -> v
  | Term.FunApp (T_array.AStore _, [ a; i; v ], _) ->
      T_bool.ifte (Formula.eq i x) v (read_array_at si se a x)
  | Term.FunApp (T_array.ALambda ((y, _), _), [ body ], _) ->
      Term.subst (Map.Poly.singleton y x) body
  | _ -> T_array.mk_select si se t x

(* [t1 = t2] for two array terms, as [forall x. t1[x] = t2[x]] *)
let extensional_array_eq t1 t2 =
  match Term.sort_of t1 with
  | T_array.SArray (si, se) ->
      let x = Ident.mk_fresh_tvar () in
      let xv = Term.mk_var x si in
      Formula.mk_forall [ (x, si) ]
        (Formula.eq (read_array_at si se t1 xv) (read_array_at si se t2 xv))
  | _ -> Formula.eq t1 t2

(* Whether a nest of [And] ([Or]) is handed to Z3 as one n-ary [and] ([or])
   over its operands, left to right, instead of as the nest of binary ones.
   Z3 flattens a nest when it asserts it, and it does so at every level of
   the nest, copying the operands gathered below each time: on a chain
   nested to the left, as [Formula.and_of] and [or_of] build it, that is
   quadratic in the chain's length, and a clause of some ten thousand
   conjuncts spent tens of seconds in [Z3_solver_assert] before the solver
   was asked anything.  The n-ary form is what the flattening arrives at, so
   the formula Z3 works on is the same; the text it prints is not.
   Process-wide, written once when a configuration asks for it. *)
let flat_and_or = Atomic.make false
let set_flat_and_or b = Atomic.set flat_and_or b

(* Conversion from formulas to Z3 expressions *)
let rec of_formula_aux ~id ctx (env : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (fenv : fenv)
    (dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t) phi =
  if false then Debug.print @@ lazy ("[z3:of_formula_aux] " ^ Formula.str_of phi);
  match phi with
  | Formula.Atom (Atom.App (Predicate.Var (pvar, []), [], _) as atom, _)
    when not (List.Assoc.mem ~equal:Stdlib.( = ) penv pvar) ->
      (* A nullary symbol absent from the caller's predicate environment is a
         free Boolean constant. Let [of_atom] apply the same instance suffix
         as its term occurrences, instead of auto-declaring an unsuffixed
         predicate. Explicitly supplied predicate declarations stay shared. *)
      of_atom ~id ctx env penv fenv dtenv atom
  | Formula.Atom ((Atom.App (Predicate.Var (pvar, sorts), _, _) as atom), _) ->
      let penv' =
        if not @@ List.Assoc.mem ~equal:Stdlib.( = ) penv pvar then
          pred_decl_of ctx dtenv (pvar, sorts) :: penv
        else penv
      in
      of_atom ~id ctx env penv' fenv dtenv atom
  | Formula.Atom (atom, _) -> of_atom ~id ctx env penv fenv dtenv atom
  | Formula.UnaryOp (Not, phi1, _) ->
      Z3.Boolean.mk_not ctx @@ of_formula_aux ~id ctx env penv fenv dtenv phi1
  | Formula.BinaryOp (And, _, _, _) when Atomic.get flat_and_or ->
      Z3.Boolean.mk_and ctx
        (of_operands_right_first ~id ctx env penv fenv dtenv
           (Formula.conjuncts_list_of phi))
  | Formula.BinaryOp (Or, _, _, _) when Atomic.get flat_and_or ->
      Z3.Boolean.mk_or ctx
        (of_operands_right_first ~id ctx env penv fenv dtenv
           (Formula.disjuncts_list_of phi))
  | Formula.BinaryOp (And, phi1, phi2, _) ->
      Z3.Boolean.mk_and ctx
        [
          of_formula_aux ~id ctx env penv fenv dtenv phi1;
          of_formula_aux ~id ctx env penv fenv dtenv phi2;
        ]
  | Formula.BinaryOp (Or, phi1, phi2, _) ->
      Z3.Boolean.mk_or ctx
        [
          of_formula_aux ~id ctx env penv fenv dtenv phi1;
          of_formula_aux ~id ctx env penv fenv dtenv phi2;
        ]
  | Formula.BinaryOp (Iff, phi1, phi2, _) ->
      Z3.Boolean.mk_iff ctx
        (of_formula_aux ~id ctx env penv fenv dtenv phi1)
        (of_formula_aux ~id ctx env penv fenv dtenv phi2)
  | Formula.BinaryOp (Xor, phi1, phi2, _) ->
      Z3.Boolean.mk_xor ctx
        (of_formula_aux ~id ctx env penv fenv dtenv phi1)
        (of_formula_aux ~id ctx env penv fenv dtenv phi2)
  | Formula.BinaryOp (Imply, phi1, phi2, _) ->
      Z3.Boolean.mk_implies ctx
        (of_formula_aux ~id ctx env penv fenv dtenv phi1)
        (of_formula_aux ~id ctx env penv fenv dtenv phi2)
  | Formula.Bind (binder, bounds, body, _) ->
      let vars = List.map bounds ~f:(fst >> of_var ctx) in
      let sorts = List.map bounds ~f:(snd >> of_sort ctx dtenv) in
      let env = List.rev bounds @ env in
      let body = of_formula_aux ~id ctx env penv fenv dtenv body in
      Z3.Quantifier.expr_of_quantifier
      @@ (match binder with
         | Formula.Forall -> Z3.Quantifier.mk_forall
         | Formula.Exists -> Z3.Quantifier.mk_exists
         | _ ->
             failwith
             @@ "[z3:of_formula_aux] Z3 does not support random quantifiers")
           ctx sorts vars body None [] [] None None
  | Formula.LetRec ([], phi, _) ->
      of_formula_aux ~id ctx env penv fenv dtenv phi
  | Formula.LetRec (_, _, _) ->
      failwith @@ "[z3:of_formula_aux] Z3 does not support fixpoint predicates"
  | Formula.LetFormula (_, _, _, _, _) ->
      failwith @@ "[z3:of_formula_aux] let-expressions not supported"

(* the operands converted from the last to the first, which is the order the
   binary nest converts its leaves in (an application's argument list is
   evaluated right to left), so that the terms are created in the same order
   either way; Z3 orders the operands of what it simplifies by creation *)
and of_operands_right_first ~id ctx env penv fenv dtenv phis =
  List.fold (List.rev phis) ~init:[] ~f:(fun acc phi ->
      of_formula_aux ~id ctx env penv fenv dtenv phi :: acc)

and of_var_term ~id ctx env dtenv t =
  let (var, sort), _ = Term.let_var t in
  if false then
    Debug.print
    @@ lazy
         (sprintf "[z3:of_var_term] %s : %s" (Ident.name_of_tvar var)
            (Term.str_of_sort sort));
  match List.findi env ~f:(fun _ (key, _) -> Stdlib.(key = var)) with
  | Some (i, (_, sort')) ->
      if
        match (sort, sort') with
        | T_bv.SBV None, T_bv.SBV _ | T_bv.SBV _, T_bv.SBV None -> false
        | _ -> Stdlib.(sort <> sort')
      then
        failwith
        @@ sprintf "%s is assigned inconsistent types %s and %s"
             (Ident.name_of_tvar var) (Term.str_of_sort sort)
             (Term.str_of_sort sort');
      if false then Debug.print @@ lazy "[z3:of_var_term] mk quantifier";
      (* lock (); (fun ret -> unlock (); ret) @@   *)
      Z3.Quantifier.mk_bound ctx i @@ of_sort ctx dtenv sort
  | None ->
      let name = Ident.name_of_tvar var in
      if false then
        Debug.print
        @@ lazy
             ("[z3:of_var_term] mk const var " ^ name ^ " : "
            ^ Term.str_of_sort sort);
      let symbol =
        of_var ctx
        @@
        match id with
        | None -> var
        | Some id -> Ident.Tvar (InstanceName.encode ~id ~sort name)
      in
      Z3.Expr.mk_const ctx symbol @@ of_sort ctx dtenv sort

(* Conversion from terms to Z3 expressions *)
and of_term ~id ctx (env : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (fenv : fenv)
    (dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t) t =
  if false then Debug.print @@ lazy (sprintf "[z3:of_term] %s" @@ Term.str_of t);
  match t with
  | Var (var, T_bool.SBool, _)
    when not (List.Assoc.mem ~equal:Stdlib.( = ) env var) -> (
      (* A supplied nullary predicate declaration also names its free Boolean
         term occurrences. A binder in [env] shadows the declaration. *)
      match List.Assoc.find ~equal:Stdlib.( = ) penv (Ident.tvar_to_pvar var) with
      | Some decl when Z3.FuncDecl.get_arity decl = 0 ->
          Z3.FuncDecl.apply decl []
      | _ -> of_var_term ~id ctx env dtenv t)
  | Var _ -> of_var_term ~id ctx env dtenv t
  | LetTerm (_, _, _, _, _) ->
      failwith @@ "[z3:of_term] not supported: " ^ Term.str_of t
  | FunApp (T_seq.SqStore se, [ sq; i; e ], _) ->
      (* Z3 has no sequence write, so the symbol is expanded here -- at the
         boundary, once, rather than at every site that builds one.  Keeping it
         a single node up to this point is the whole reason it exists: a
         qualifier and a read-over-write rewrite have something to match. *)
      of_term ~id ctx env penv fenv dtenv @@ T_seq.store_expansion_of se sq i e
  | FunApp (T_array.ALambda ((x, si), _se), [ body ], _) ->
      (* Z3's [lambda] denotes an array value, which is exactly what
         [T_array.ALambda] means; the body is encoded with the binder pushed
         onto [env] so that [of_var_term] gives it a de Bruijn index *)
      Z3.Quantifier.expr_of_quantifier
      @@ Z3.Quantifier.mk_lambda ctx [ (of_var ctx x, of_sort ctx dtenv si) ]
      @@ of_term ~id ctx ((x, si) :: env) penv fenv dtenv body
  | FunApp (fsym, args, _) -> (
      match (fsym, List.map ~f:(of_term ~id ctx env penv fenv dtenv) args) with
      | T_bool.Formula phi, [] -> of_formula_aux ~id ctx env penv fenv dtenv phi
      | T_bool.IfThenElse, [ cond; then_; else_ ] ->
          Z3.Boolean.mk_ite ctx cond then_ else_
      | T_int.Int n, [] ->
          Z3.Arithmetic.Integer.mk_numeral_s ctx (Z.to_string n)
      | T_real.Real r, [] -> (
          match Q.classify r with
          | Q.ZERO | Q.NZERO -> (
              try Z3.Arithmetic.Real.mk_numeral_s ctx (Q.to_string r)
              with exn_ when not (Common.Timer.is_async exn_) ->
                failwith @@ Q.to_string r ^ " cannot be parsed")
          | Q.UNDEF ->
              Z3.Arithmetic.mk_div ctx
                (Z3.Arithmetic.Real.mk_numeral_i ctx 0)
                (Z3.Arithmetic.Real.mk_numeral_i ctx 0)
          | Q.INF ->
              Z3.Arithmetic.mk_div ctx
                (Z3.Arithmetic.Real.mk_numeral_i ctx 1)
                (Z3.Arithmetic.Real.mk_numeral_i ctx 0)
          | Q.MINF ->
              Z3.Arithmetic.mk_div ctx
                (Z3.Arithmetic.Real.mk_numeral_i ctx (-1))
                (Z3.Arithmetic.Real.mk_numeral_i ctx 0))
      | T_real.Alge n, [ _ ] -> alge_of ctx (List.hd_exn args) n
      | (T_int.Neg | T_real.RNeg), [ n ] ->
          if Z3.Expr.is_const n then (*ToDo*) Z3.Arithmetic.mk_unary_minus ctx n
          else Z3.Arithmetic.mk_unary_minus ctx n
      | T_int.Nop, [ n ] -> n
      | ((T_int.Abs | T_real.RAbs) as op), [ n ] ->
          (*ToDo*)
          let is_minus =
            Z3.Arithmetic.mk_lt ctx n
              (match op with
              | T_int.Abs -> Z3.Arithmetic.Integer.mk_numeral_i ctx 0
              | T_real.RAbs -> Z3.Arithmetic.Real.mk_numeral_i ctx 0
              | _ -> assert false)
          in
          let minus_n =
            of_term ~id ctx env penv fenv dtenv
              (T_int.mk_neg @@ List.hd_exn args)
          in
          Z3.Boolean.mk_ite ctx is_minus minus_n n
      | (T_int.Add | T_real.RAdd), [ t1; t2 ] ->
          Z3.Arithmetic.mk_add ctx [ t1; t2 ]
      | (T_int.Sub | T_real.RSub), [ t1; t2 ] ->
          Z3.Arithmetic.mk_sub ctx [ t1; t2 ]
      | (T_int.Mul | T_real.RMul), [ t1; t2 ] ->
          Z3.Arithmetic.mk_mul ctx [ t1; t2 ]
      | T_int.Div Euclidean, [ t1; t2 ] -> Z3.Arithmetic.mk_div ctx t1 t2
      | T_int.Div Truncated, [ t1; t2 ] -> mk_tdiv ctx t1 t2
      | T_real.RDiv, [ t1; t2 ] ->
          (*ToDo: necessary? *)
          Z3.Arithmetic.mk_div ctx
            (if Z3.Arithmetic.is_int t1 then
               Z3.Arithmetic.Integer.mk_int2real ctx t1
             else t1)
            (if Z3.Arithmetic.is_int t2 then
               Z3.Arithmetic.Integer.mk_int2real ctx t2
             else t2)
      | T_int.Rem Euclidean, [ t1; t2 ] ->
          Z3.Arithmetic.Integer.mk_mod ctx t1 t2
      | T_int.Rem Truncated, [ t1; t2 ] -> mk_tmod ctx t1 t2
      | T_int.Power, [ t1; t2 ] ->
          (* Z3's [^] has sort Real even over two integers, so the integer
             power is wrapped in [to_int] to stay integer-valued: an integer
             equation then compares integers, and the decoder reads the pair
             back as [T_int.Power].  For a non-negative exponent the power of
             integers is an integer, so the wrapper changes no value there; a
             negative exponent has no meaning in this tree's integer power. *)
          let pw = Z3.Arithmetic.mk_power ctx t1 t2 in
          if Z3.Arithmetic.is_int pw then pw
          else Z3.Arithmetic.Real.mk_real2int ctx pw
      | T_real.RPower, [ t1; t2 ] -> Z3.Arithmetic.mk_power ctx t1 t2
      | T_irb.IntToReal, [ t ] -> Z3.Arithmetic.Integer.mk_int2real ctx t
      | T_irb.RealToInt, [ t ] -> Z3.Arithmetic.Real.mk_real2int ctx t
      | T_irb.IntToBV size, [ t ] when Atomic.get int_to_bv_range ->
          push_int2bv ctx (T_bv.bits_of size) t
      | T_irb.IntToBV size, [ t ] ->
          Z3.Arithmetic.Integer.mk_int2bv ctx (T_bv.bits_of size) t
      | T_irb.BVToInt (_size, signed), [ t ] ->
          Z3.BitVector.mk_bv2int ctx t (T_bv.is_signed signed)
      | T_bv.BVNum (size, n), [] ->
          Z3.BitVector.mk_numeral ctx (Z.to_string n) (T_bv.bits_of size)
      | T_bv.BVNot _size, [ t1 ] -> Z3.BitVector.mk_not ctx t1
      | T_bv.BVAnd _size, [ t1; t2 ] -> Z3.BitVector.mk_and ctx t1 t2
      | T_bv.BVOr _size, [ t1; t2 ] -> Z3.BitVector.mk_or ctx t1 t2
      | T_bv.BVXor _size, [ t1; t2 ] -> Z3.BitVector.mk_xor ctx t1 t2
      | T_bv.BVNand _size, [ t1; t2 ] -> Z3.BitVector.mk_nand ctx t1 t2
      | T_bv.BVNor _size, [ t1; t2 ] -> Z3.BitVector.mk_nor ctx t1 t2
      | T_bv.BVXnor _size, [ t1; t2 ] -> Z3.BitVector.mk_xnor ctx t1 t2
      | T_bv.BVNeg _size, [ t1 ] -> Z3.BitVector.mk_neg ctx t1
      | T_bv.BVAdd _size, [ t1; t2 ] -> Z3.BitVector.mk_add ctx t1 t2
      | T_bv.BVSub _size, [ t1; t2 ] -> Z3.BitVector.mk_sub ctx t1 t2
      | T_bv.BVMul _size, [ t1; t2 ] -> Z3.BitVector.mk_mul ctx t1 t2
      | T_bv.BVDiv (_size, signed), [ t1; t2 ] ->
          (if T_bv.is_signed signed then Z3.BitVector.mk_sdiv
           else Z3.BitVector.mk_udiv)
            ctx t1 t2
      | T_bv.BVRem (_size, signed), [ t1; t2 ] ->
          (if T_bv.is_signed signed then Z3.BitVector.mk_srem
           else Z3.BitVector.mk_urem)
            ctx t1 t2
      | T_bv.BVSMod _size, [ t1; t2 ] -> Z3.BitVector.mk_smod ctx t1 t2
      | T_bv.BVSHL _size, [ t1; t2 ] -> Z3.BitVector.mk_shl ctx t1 t2
      | T_bv.BVLSHR _size, [ t1; t2 ] -> Z3.BitVector.mk_lshr ctx t1 t2
      | T_bv.BVASHR _size, [ t1; t2 ] -> Z3.BitVector.mk_ashr ctx t1 t2
      | T_bv.BVEXTRACT (_size, h, l), [ t1 ] ->
          Z3.BitVector.mk_extract ctx h l t1
      | T_bv.BVSEXT (_size, ext), [ t1 ] -> Z3.BitVector.mk_sign_ext ctx ext t1
      | T_bv.BVZEXT (_size, ext), [ t1 ] -> Z3.BitVector.mk_zero_ext ctx ext t1
      | T_bv.BVCONCAT (_size1, _size2), [ t1; t2 ] ->
          Z3.BitVector.mk_concat ctx t1 t2
      | T_string.StrConst str, [] -> Z3.Seq.mk_string ctx str
      | T_trace.TrEpsilon, [] -> Z3.FuncDecl.apply (z3_epsilon ctx) []
      | T_trace.TrSymbol str, [] -> Z3.FuncDecl.apply (z3_symbol_of ctx str) []
      | T_trace.TrConcat fin, [ t1; t2 ] ->
          Z3.FuncDecl.apply (z3_concat ctx fin) [ t1; t2 ]
      | T_regex.RegEmpty, [] ->
          Z3.Seq.mk_re_empty ctx @@ Z3.Seq.mk_re_sort ctx
          @@ Z3.Seq.mk_string_sort ctx
      | T_regex.RegFull, [] ->
          Z3.Seq.mk_re_full ctx @@ Z3.Seq.mk_re_sort ctx
          @@ Z3.Seq.mk_string_sort ctx
      | T_regex.RegAllChar, [] ->
          (* The one-character strings, which is NOT [re.all]: that one holds
             every string, the empty one included.  SMT-LIB's UnicodeStrings
             theory fixes the alphabet at the code points 0 to 0x2FFFF, so this
             is exactly the range over the whole alphabet, and both z3 and cvc5
             confirm the two are the same language.  The range is used because
             the OCaml binding does not export the solver's own [allchar]
             constructor, only the C one, whose context type it does not
             expose. *)
          Z3.Seq.mk_re_range ctx
            (Z3.Seq.mk_string ctx "\\u{0}")
            (Z3.Seq.mk_string ctx "\\u{2FFFF}")
      | T_regex.RegEpsilon, [] ->
          Z3.Seq.mk_seq_to_re ctx (Z3.Seq.mk_string ctx "")
      | T_regex.RegStr, [ t1 ] -> Z3.Seq.mk_seq_to_re ctx t1
      | T_regex.RegComplement, [ t1 ] -> Z3.Seq.mk_re_complement ctx t1
      | T_regex.RegStar, [ t1 ] -> Z3.Seq.mk_re_star ctx t1
      | T_regex.RegPlus, [ t1 ] -> Z3.Seq.mk_re_plus ctx t1
      | T_regex.RegOpt, [ t1 ] -> Z3.Seq.mk_re_option ctx t1
      | T_regex.RegConcat, [ t1; t2 ] -> Z3.Seq.mk_re_concat ctx [ t1; t2 ]
      | T_regex.RegUnion, [ t1; t2 ] -> Z3.Seq.mk_re_union ctx [ t1; t2 ]
      | T_regex.RegInter, [ t1; t2 ] -> Z3.Seq.mk_re_intersect ctx [ t1; t2 ]
      | FVar (var, _sargs, _sret), ts when Map.Poly.mem fenv var ->
          Z3.FuncDecl.apply (Map.Poly.find_exn fenv var) ts
      | FVar (var, sargs, sret), ts ->
          Z3.Expr.mk_app ctx
            (Z3.FuncDecl.mk_func_decl ctx (of_var ctx var)
               (List.map ~f:(of_sort ctx dtenv) sargs)
               (of_sort ctx dtenv sret))
            ts
      | T_array.AConst (si, _se), [ t1 ] ->
          Z3.Z3Array.mk_const_array ctx (of_sort ctx dtenv si) t1
      | T_array.AStore (_si, _se), [ t1; t2; t3 ] ->
          Z3.Z3Array.mk_store ctx t1 t2 t3
      | T_array.ASelect (_si, _se), [ t1; t2 ] -> Z3.Z3Array.mk_select ctx t1 t2
      (* SMT-LIB's parametric sequences go to Z3's own sequence solver.  Do not
         confuse these with [T_trace], the word algebra over abstract
         symbols, which is encoded as an uninterpreted sort just above. *)
      | T_seq.SqEmpty se, [] ->
          Z3.Seq.mk_seq_empty ctx (of_sort ctx dtenv (T_seq.SSeq se))
      | T_seq.SqUnit _, [ t1 ] -> Z3.Seq.mk_seq_unit ctx t1
      | T_seq.SqConcat _, [ t1; t2 ] -> Z3.Seq.mk_seq_concat ctx [ t1; t2 ]
      | T_seq.SqLen _, [ t1 ] -> Z3.Seq.mk_seq_length ctx t1
      | T_seq.SqNth _, [ t1; t2 ] -> Z3.Seq.mk_seq_nth ctx t1 t2
      | T_seq.SqExtract _, [ t1; t2; t3 ] ->
          Z3.Seq.mk_seq_extract ctx t1 t2 t3
      | T_tuple.TupleSel (sorts, i), [ t ] ->
          let sort = of_sort ctx dtenv @@ T_tuple.STuple sorts in
          Z3.FuncDecl.apply
            (List.nth_exn (Z3.Tuple.get_field_decls sort) i)
            [ t ]
      | T_tuple.TupleCons sorts, ts ->
          let sort = of_sort ctx dtenv @@ T_tuple.STuple sorts in
          Z3.FuncDecl.apply (Z3.Tuple.get_mk_decl sort) ts
      | T_dt.DTCons (name, _tys, dt), ts ->
          (*let dt = Datatype.update_args dt tys in*)
          Z3.FuncDecl.apply (z3_cons_of dtenv dt name) ts
      | T_dt.DTSel (name, dt, _), ts ->
          Z3.FuncDecl.apply (z3_sel_of dtenv dt name) ts
      | _ -> failwith @@ "[z3:of_term] not supported: " ^ Term.str_of t)

and
    (* Conversion from atoms to Z3 expressions *)
    of_atom ~id ctx (env : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (fenv : fenv)
    (dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t) atom =
  if false then
    Debug.print @@ lazy (sprintf "[z3:of_atom] %s" @@ Atom.str_of atom);
  match atom with
  | True _ -> Z3.Boolean.mk_true ctx
  | False _ -> Z3.Boolean.mk_false ctx
  | App (Predicate.Var (pvar, sorts), args, _) ->
      if
        List.is_empty args
        && List.is_empty sorts
        && (List.Assoc.mem ~equal:Stdlib.( = ) env (Ident.pvar_to_tvar pvar)
           || not (List.Assoc.mem ~equal:Stdlib.( = ) penv pvar))
      then
        of_var_term ~id ctx env dtenv
        @@ Term.mk_var (Ident.pvar_to_tvar pvar) T_bool.SBool
      else
        let pred =
          match List.Assoc.find ~equal:Stdlib.( = ) penv pvar with
          | None ->
              failwith
              @@ sprintf "[z3:of_atom] %s not supported: "
              @@ Ident.name_of_pvar pvar
          | Some pred -> pred
        in
        Z3.Expr.mk_app ctx pred
        @@ List.map args ~f:(of_term ~id ctx env penv fenv dtenv)
  | App (Predicate.Fixpoint _, _, _) ->
      failwith @@ sprintf "[z3:of_atom] %s not supported" @@ Atom.str_of atom
  (* The array-literal equality over a finite index sort (see
     [expand_finite_array_eq_atom]) is rewritten HERE as well as in
     [check_sat], because not every query reaches the solver through
     [check_sat]: the unsat-core, optimisation and incremental entry points add
     their formulas directly, a disequality is a [Neq] atom the formula-level
     rewrite does not match, and an equality inside a term (an [ite] condition,
     an embedded formula) is not an atom of the formula at all.  Every one of
     them is converted by this function, so this is the one place no query can
     go around.  The guard admits only atoms the expansion changes, which is
     what keeps the recursion into [of_formula_aux] from coming back here with
     the same atom.  Off, like the formula-level rewrite, for a library that
     answers the equality correctly. *)
  | App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as sym), [ t1; t2 ], _)
    when Atomic.get finite_array_literal_eq_rewrite
         && is_finite_array_literal_eq t1 t2 ->
      let phi = expand_finite_array_eq_atom (T_bool.mk_eq t1 t2) in
      of_formula_aux ~id ctx env penv fenv dtenv
        (match sym with T_bool.Neq -> Formula.mk_neg phi | _ -> phi)
  (* an equality between array terms one of which contains a [lambda], asked
     extensionally ([lambda_array_eq_rewrite]); the element equality it leaves
     has a smaller sort, so the recursion ends *)
  | App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as sym), [ t1; t2 ], _)
    when is_lambda_array_eq t1 t2 ->
      let phi = extensional_array_eq t1 t2 in
      of_formula_aux ~id ctx env penv fenv dtenv
        (match sym with T_bool.Neq -> Formula.mk_neg phi | _ -> phi)
  | App (Predicate.Psym sym, args, _) -> (
      (* if Stdlib.(sym = T_bool.Eq || sym = T_bool.Neq) &&
          (match args with [Term.FunApp (T_bool.Formula phi, [], _); _] -> not (Formula.is_true phi || Formula.is_false phi) | _ -> false) ||
          (match args with [_; Term.FunApp (T_bool.Formula phi, [], _)] -> not (Formula.is_true phi || Formula.is_false phi) | _ -> false) then
         if Stdlib.(sym = T_bool.Eq) then
           Boolean.mk_iff ctx
             (of_formula_aux ctx env penv fenv dtenv @@ Formula.of_bool_term @@ List.hd_exn args)
             (of_formula_aux ctx env penv fenv dtenv @@ Formula.of_bool_term @@ List.hd_exn @@ List.tl_exn args)
         else if Stdlib.(sym = T_bool.Neq) then
           Boolean.mk_xor ctx
             (of_formula_aux ctx env penv fenv dtenv @@ Formula.of_bool_term @@ List.hd_exn args)
             (of_formula_aux ctx env penv fenv dtenv @@ Formula.of_bool_term @@ List.hd_exn @@ List.tl_exn args)
         else assert false
         else *)
      match (sym, List.map ~f:(of_term ~id ctx env penv fenv dtenv) args) with
      | T_bool.Eq, [ t1; t2 ] -> Z3.Boolean.mk_eq ctx t1 t2
      | T_bool.Neq, [ t1; t2 ] ->
          Z3.Boolean.mk_not ctx @@ Z3.Boolean.mk_eq ctx t1 t2
      | (T_int.Leq | T_real.RLeq), [ t1; t2 ] -> Z3.Arithmetic.mk_le ctx t1 t2
      | T_bv.BVLeq (_size, signed), [ t1; t2 ] ->
          (if T_bv.is_signed signed then Z3.BitVector.mk_sle
           else Z3.BitVector.mk_ule)
            ctx t1 t2
      | (T_int.Geq | T_real.RGeq), [ t1; t2 ] -> Z3.Arithmetic.mk_ge ctx t1 t2
      | T_bv.BVGeq (_size, signed), [ t1; t2 ] ->
          (if T_bv.is_signed signed then Z3.BitVector.mk_sge
           else Z3.BitVector.mk_uge)
            ctx t1 t2
      | (T_int.Lt | T_real.RLt), [ t1; t2 ] -> Z3.Arithmetic.mk_lt ctx t1 t2
      | T_bv.BVLt (_size, signed), [ t1; t2 ] ->
          (if T_bv.is_signed signed then Z3.BitVector.mk_slt
           else Z3.BitVector.mk_ult)
            ctx t1 t2
      | (T_int.Gt | T_real.RGt), [ t1; t2 ] -> Z3.Arithmetic.mk_gt ctx t1 t2
      | T_bv.BVGt (_size, signed), [ t1; t2 ] ->
          (if T_bv.is_signed signed then Z3.BitVector.mk_sgt
           else Z3.BitVector.mk_ugt)
            ctx t1 t2
      | T_int.PDiv, [ t1; t2 ] ->
          Z3.Boolean.mk_eq ctx
            (Z3.Arithmetic.Integer.mk_mod ctx t2 t1)
            (Z3.Arithmetic.Integer.mk_numeral_i ctx 0)
      | T_int.NotPDiv, [ t1; t2 ] ->
          Z3.Boolean.mk_not ctx
          @@ Z3.Boolean.mk_eq ctx
               (Z3.Arithmetic.Integer.mk_mod ctx t2 t1)
               (Z3.Arithmetic.Integer.mk_numeral_i ctx 0)
      | T_irb.IsInt, [ t ] -> Z3.Arithmetic.Real.mk_is_integer ctx t
      | (T_num.NLeq _ | T_num.NGeq _ | T_num.NLt _ | T_num.NGt _), [ _t1; _t2 ]
        ->
          failwith
          @@ sprintf "[z3:of_atom] polymorphic inequalities not supported: %s"
          @@ Atom.str_of atom
      | T_trace.IsPrefix fin, [ t1; t2 ] ->
          Z3.FuncDecl.apply (z3_is_prefix_of ctx fin) [ t1; t2 ]
      | T_trace.NotIsPrefix fin, [ t1; t2 ] ->
          Z3.Boolean.mk_not ctx
          @@ Z3.FuncDecl.apply (z3_is_prefix_of ctx fin) [ t1; t2 ]
      | T_trace.TrInRegExp (fin, regexp), [ t1 ] ->
          Z3.FuncDecl.apply (z3_is_in_reg_exp ctx fin regexp) [ t1 ]
      | T_trace.NotTrInRegExp (fin, regexp), [ t1 ] ->
          Z3.Boolean.mk_not ctx
          @@ Z3.FuncDecl.apply (z3_is_in_reg_exp ctx fin regexp) [ t1 ]
      | T_regex.StrInRegExp, [ t1; t2 ] -> Z3.Seq.mk_seq_in_re ctx t1 t2
      | T_regex.NotStrInRegExp, [ t1; t2 ] ->
          Z3.Boolean.mk_not ctx @@ Z3.Seq.mk_seq_in_re ctx t1 t2
      | T_tuple.IsTuple sorts, ts ->
          if true then Z3.Boolean.mk_true ctx (*ToDo*)
          else
            let _s = tuple_sort_of ctx dtenv sorts in
            let istuple = failwith "[z3:of_atom] is_tuple not supported" in
            Z3.FuncDecl.apply istuple ts
      | T_tuple.NotIsTuple sorts, ts ->
          if true then Z3.Boolean.mk_false ctx (*ToDo*)
          else
            let _s = tuple_sort_of ctx dtenv sorts in
            let istuple = failwith "[z3:of_atom] is_tuple not supported" in
            Z3.Boolean.mk_not ctx @@ Z3.FuncDecl.apply istuple ts
      | T_dt.IsCons (name, dt), ts ->
          Z3.FuncDecl.apply (z3_iscons_of dtenv dt name) ts
      | T_dt.NotIsCons (name, dt), ts ->
          Z3.Boolean.mk_not ctx
          @@ Z3.FuncDecl.apply (z3_iscons_of dtenv dt name) ts
      | _ ->
          failwith
          @@ sprintf "[z3:of_atom] %s not supported"
          @@ Atom.str_of atom)

(* The defined functions [phi] reaches, directly or through the definition
   or the recorded property of another reached function.  Every definition a
   context is told is registered as a recursive one, used or not, and a
   context holding one was measured to lose decisions a context without it
   makes. This is a reachability computation, not a model-extension check:
   omitted recursive equations can constrain even symbols the query uses
   without applying the defined function. See the precondition below. *)
let fenv_reached_by (fenv : FunEnv.t) phi =
  let called syms =
    Set.Poly.filter_map syms ~f:(function
      | FVar (v, _, _) when Map.Poly.mem fenv v -> Some v
      | _ -> None)
  in
  let rec close seen frontier =
    if Set.is_empty frontier then seen
    else
      let seen = Set.union seen frontier in
      let next =
        Set.Poly.union_list
        @@ List.map (Set.to_list frontier) ~f:(fun v ->
            let _, _, def, _, property = Map.Poly.find_exn fenv v in
            called
              (Set.union (Term.funsyms_of def) (Formula.funsyms_of property)))
      in
      close seen (Set.diff next seen)
  in
  let used = close Set.Poly.empty (called (Formula.funsyms_of phi)) in
  Map.Poly.filter_keys fenv ~f:(Set.mem used)

(* Off unless a configuration sets it (PCSat's
   [declare_reached_functions_only]).  When on, every entry point below that
   is handed a function environment together with the formulas of one query
   declares to Z3 only the functions those formulas reach ([fenv_reached_by]),
   rather than every function of the environment.

   Initial motivation: a three-clause loop stalled with an unused recursive
   definition, and dumped queries solved standalone. Later tracing identified
   a parametric qualifier that applies that function, generated because the
   hypothesis space reads the whole environment as vocabulary. That diagnosis supersedes the initial claim that no single formula
   causes the stall. Declaration filtering and problem-vocabulary pruning
   address different routes; neither observation proves generic exactness.

   Preservation precondition: each model of the retained context must admit
   an extension satisfying all omitted defining equations. Reachability alone
   does not establish this for recursive definitions, even consistent ones:
   an unused b(x) = b(x) xor p constrains p. This switch does not check the
   precondition. It is initially false; PCSat's initializer only enables the
   process-wide flag, so a later false configuration does not reset it.

   A kept context must also declare what each later batch reaches before
   converting it ([declare_reached]); an applied but undeclared function
   would otherwise be converted as an uninterpreted symbol. This incremental
   declaration obligation is separate from omitted-equation consistency. *)
let declare_reached_functions_only = Atomic.make false
let reached_functions_only () = Atomic.get declare_reached_functions_only

(* [fenv] itself when the switch is off or [fenv] is empty; otherwise the part
   of [fenv] that [phis] reach. *)
let fenv_for_query (fenv : FunEnv.t) phis =
  if (not (reached_functions_only ())) || Map.Poly.is_empty fenv then fenv
  else fenv_reached_by fenv (Formula.and_of phis)

(* Called with the context and the name at every recursive function
   declaration [z3_fenv_of] makes.  It does nothing unless a test sets it: a
   property check counts through it how often one context is given the same
   recursive function, since Z3 5.x refuses a second declaration of an already
   defined recursive function ("recursive function ... already defined") where
   4.x accepted it, so a build against a 4.x library cannot show the
   difference by itself. *)
let rec_func_decl_hook : (Z3.context -> string -> unit) ref =
  ref (fun _ _ -> ())

(* Declares and defines, in [ctx], every recursive function of [fenv] not
   already in [init] (a map this context was given earlier by this function).
   Precondition, not checked: [ctx] holds no declaration of a function of
   [fenv] outside [init].  A caller converting several formulas into one
   context must therefore call this ONCE and pass the result to
   [of_formula_with_z3fenv] (or use [formula_converter]), or keep the result as
   the next call's [init]; calling [of_formula] per formula re-declares every
   function, which Z3 5.x rejects. *)
let z3_fenv_of ?(init = Map.Poly.empty) ~id ctx (env : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (fenv : FunEnv.t)
    (dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t) =
  let z3_fenv =
    Map.Poly.fold fenv ~init
      ~f:(fun ~key:var ~data:(params, sret, _, _, _) acc ->
        if Map.Poly.mem acc var then acc
        else
          let data =
            !rec_func_decl_hook ctx (Ident.name_of_tvar var);
            Z3.FuncDecl.mk_rec_func_decl_s ctx (Ident.name_of_tvar var)
              (List.map params ~f:(snd >> of_sort ctx dtenv))
              (of_sort ctx dtenv sret)
          in
          Map.Poly.add_exn acc ~key:var ~data)
  in
  Map.Poly.iteri fenv ~f:(fun ~key:var ~data:(senv, _, def, _, _) ->
      if Map.Poly.mem init var then ()
      else
        (* Query normalization does not visit stored function bodies. Recursive
           definitions retain term/formula lets, both refused by the encoder.
           Remove them in a copy at registration, preserving the stored equation
           and the once-per-context declaration contract; without this an
           unused recursive definition with a let made the whole input refused. *)
        let def = if Term.is_let_free def then def else Term.elim_let def in
        Z3.FuncDecl.add_rec_def ctx
          (Map.Poly.find_exn z3_fenv var)
          (List.map senv
             ~f:
               (Tuple2.uncurry Term.mk_var
               >> of_term ~id ctx env penv z3_fenv dtenv))
          (of_term ~id ctx env penv z3_fenv dtenv def));
  z3_fenv

(* Declares in [ctx] the functions of [fenv] that [phis] reach and that
   [z3fenv] -- the map this context's earlier calls of [z3_fenv_of] returned --
   does not hold yet, and returns the extended map.  Precondition as for
   [z3_fenv_of]: [ctx] declares no function of [fenv] outside [z3fenv].  For a
   caller that keeps a context and converts formulas into it over time under
   [declare_reached_functions_only]. *)
let declare_reached ~id ctx z3fenv (fenv : FunEnv.t) dtenv phis =
  z3_fenv_of ~id ~init:z3fenv ctx [] []
    (fenv_reached_by fenv (Formula.and_of phis))
    dtenv

(* A diagnostic, inert unless [COAR_CONVERT_CENSUS] is set: for a formula
   about to be converted, the number of formula, atom and term nodes of its
   tree, of its physically distinct nodes, and of its structurally distinct
   ones, printed on stderr with a running total.  The conversion walks the
   tree, so the first number is its work; the last two say how much of that
   work repeats a subtree already converted. *)
module ConvertCensus = struct
  let on =
    Lazy.from_val
      (match Sys.getenv "COAR_CONVERT_CENSUS" with
      | None | Some "" -> false
      | Some _ -> true)

  let totals = Array.create ~len:3 0

  let run phi =
    let tree = ref 0 in
    let phys = Stdlib.Hashtbl.create 1024 in
    let strct = Stdlib.Hashtbl.create 1024 in
    let nphys = ref 0 and nstrct = ref 0 in
    let visit (o : Stdlib.Obj.t) =
      incr tree;
      let ph = Common.Ext.Hashtbl.phys_hash o in
      let l = Option.value ~default:[] (Stdlib.Hashtbl.find_opt phys ph) in
      if not (List.exists l ~f:(fun o' -> phys_equal o o')) then (
        Stdlib.Hashtbl.replace phys ph (o :: l);
        incr nphys);
      let h = Stdlib.Hashtbl.hash_param 100 1000 o in
      let l = Option.value ~default:[] (Stdlib.Hashtbl.find_opt strct h) in
      if not (List.exists l ~f:(fun o' -> phys_equal o o' || Stdlib.(o = o')))
      then (
        Stdlib.Hashtbl.replace strct h (o :: l);
        incr nstrct)
    in
    let rec term t =
      visit (Stdlib.Obj.repr t);
      match t with
      | Term.Var _ -> ()
      | Term.FunApp (T_bool.Formula phi, args, _) ->
          formula phi;
          List.iter args ~f:term
      | Term.FunApp (_, args, _) -> List.iter args ~f:term
      | Term.LetTerm (_, _, t1, t2, _) ->
          term t1;
          term t2
    and atom a =
      visit (Stdlib.Obj.repr a);
      match a with
      | Atom.App (_, args, _) -> List.iter args ~f:term
      | _ -> ()
    and formula phi =
      visit (Stdlib.Obj.repr phi);
      match phi with
      | Formula.Atom (a, _) -> atom a
      | Formula.UnaryOp (_, p, _) | Formula.Bind (_, _, p, _) -> formula p
      | Formula.BinaryOp (_, p1, p2, _) ->
          formula p1;
          formula p2
      | Formula.LetRec (_, p, _) -> formula p
      | Formula.LetFormula (_, _, t, p, _) ->
          term t;
          formula p
    in
    formula phi;
    totals.(0) <- totals.(0) + !tree;
    totals.(1) <- totals.(1) + !nphys;
    totals.(2) <- totals.(2) + !nstrct;
    Stdlib.Printf.eprintf
      "[convert-census] %s tree %d phys %d struct %d | total tree %d phys %d \
       struct %d\n%!"
      (Common.PhaseTime.current_path ())
      !tree !nphys !nstrct totals.(0) totals.(1) totals.(2)
end

let of_formula_with_z3fenv ~id ctx (uni_senv : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (fenv : fenv)
    (dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t) phi =
  Debug.print
  @@ lazy
       (sprintf "[z3:of_formula_with_z3fenv] phi:\n  %s" (Formula.str_of phi));
  let phi' =
    (* [normalize_let] alpha-renames the let binders and [elim_let_equi] lifts
       the bindings out as an existential; on a formula that binds nothing both
       rebuild it unchanged, and nothing the solver path converts binds
       anything -- over 51 benchmarks at 30 s, 0 of 115,978 conversions carried
       a let and the pair was character-for-character identical on every one of
       them, costing 16.7 s against the 1.4 s this test costs.  The test also
       leaves the fresh-variable counter where it was, because the renaming
       draws a name only at a let binder: skipping it on a let-free formula
       renames nothing and so moves no later name.  [is_let_free] answers
       [false] for a [let rec], which is the safe direction -- such a formula
       takes the original path. *)
    if Formula.is_let_free phi then phi
    else
      Formula.elim_let_equi false
      (*ToDo*) @@ Normalizer.normalize_let ~rename:true phi
  in
  Debug.print
  @@ lazy
       (sprintf "[z3:of_formula_with_z3fenv] phi':\n  %s" (Formula.str_of phi'));
  let res = of_formula_aux ~id ctx uni_senv penv fenv dtenv phi' in
  if false then Debug.print @@ lazy ("result: " ^ Z3.Expr.to_string res);
  res

let z3_solver_reset solver =
  (* lock (); (fun ret -> unlock (); ret) @@ *)
  Z3.Solver.reset solver

let z3_solver_add solver exprs =
  (* lock (); (fun ret -> unlock (); ret) @@ *)
  Z3.Solver.add solver exprs

let z3_goal_add goal exprs =
  (* lock (); (fun ret -> unlock (); ret) @@ *)
  Z3.Goal.add goal exprs

let z3_solver_get_model solver =
  (* lock (); (fun ret -> unlock (); ret) @@  *)
  Z3.Solver.get_model solver

let z3_solver_get_unsat_core solver =
  (* lock (); (fun ret -> unlock (); ret) @@  *)
  Z3.Solver.get_unsat_core solver

let z3_solver_assert_and_track solver e1 e2 =
  (* lock (); (fun ret -> unlock (); ret) @@  *)
  Z3.Solver.assert_and_track solver e1 e2

(* Which binders make a query to this solver unable to come back.

   A quantifier over a SEQUENCE is the measured case: the call does not return
   at all -- not slowly, and not bounded by the timeout the caller passes, which
   reaches the solver as a tactic's [try_for] and does not hold.  Forty seconds
   and counting on a four-line definition; a ten-line satisfiable problem whose
   only quantifier is over a sequence is not answered at 180 s, with the whole
   of it spent inside the call.  Nothing in this process can stop it either: the
   wall-clock timer raises from a signal handler and the runtime runs handlers
   at safe points, so a call that does not return is not interruptible.  A
   caller that must not hang therefore has to decide from the formula's SHAPE
   BEFORE asking, which is what this answers.

   Read the BOUND variables.  The environments named for the free ones
   ([sort_env_of], [term_sort_env_of]) subtract exactly what a quantifier binds,
   so a guard written against them inspects the parameters -- which are never
   what would be eliminated -- and fires on nothing.  That was written twice at
   two different call sites, compiled, ran, changed no behaviour, and was called
   a fix both times; it is the reason this lives in one place with one comment.

   The set is returned rather than a boolean so that a caller can say what it
   declined on: a guard nobody has seen fire is a guard nobody should believe. *)
(* The sequence half of [unsupported_binder_sort], remembered per sort and per
   domain: it is a function of the sort alone (a datatype sort carries its own
   definition), and computing it collects every sort the sort reaches into a
   set, which compares datatype sorts structurally -- on the large datatypes of
   Rust-derived inputs this made the shape test of one question cost up to a
   second.  A table keyed by the sort under polymorphic comparison, which stops
   at physically equal parts, answers a repeated sort at the cost of a hash and
   one comparison; the answer is the one the collection gives. *)
let seq_reaching_sort_memo : (Sort.t, bool) Hashtbl.Poly.t Stdlib.Domain.DLS.key
    =
  Stdlib.Domain.DLS.new_key (fun () -> Hashtbl.Poly.create ())

let reaches_seq_sort sort =
  let compute () =
    Set.exists (Term.sorts_of_sort sort) ~f:(function
      | T_seq.SSeq _ -> true
      | _ -> false)
  in
  match sort with
  | T_bool.SBool | T_int.SInt | T_real.SReal | T_bv.SBV _ | T_string.SString
  | Sort.SVar _ ->
      compute ()
  | _ ->
      let memo = Stdlib.Domain.DLS.get seq_reaching_sort_memo in
      Hashtbl.Poly.find_or_add memo sort ~default:compute

let unsupported_binder_sort sort =
  (* An ARROW-sorted binder is here because one of the four callers refuses it
     independently of the sequence case, and this function must not quietly
     weaken a site it replaces.  What it rests on is the first-order
     restriction rather than a measurement of its own: a variable of function
     sort can be neither bound in a query nor read back from a model, so asking
     is at best useless.

     It fires on no input: over 29 sequence benchmarks the sequence arm fires
     87 times and this one 0, and over 40 constrained Horn files neither fires
     at all.  That is what the first-order restriction predicts -- a universal
     declared with arguments becomes an array-sorted term variable applied by
     [select], never a variable of function sort, so nothing here binds one --
     and it means this arm is exercised only by a formula built for it.  It is
     kept rather than dropped because removing it would weaken a call site that
     refuses arrows; what would justify dropping it is an input in which a
     bound arrow sort is answered. *)
  Sort.is_arrow sort || reaches_seq_sort sort

let unsupported_binders phi =
  Set.filter (Formula.quantified_sort_env_of phi) ~f:(snd >> unsupported_binder_sort)

(* The same question on the path every query takes, answered without building the
   set: it stops at the first binder it refuses.  The traversal itself lives with
   the term language, because knowing WHICH function symbols bind is that
   language's business and a copy here would drift from it -- which is exactly
   what happened while the collector stopped at an atom and this did not. *)
(* A sort whose theory the solver will not come back from, WHEREVER it occurs --
   bound, free, or only inside a term.  This is a different question from the one
   above and the difference is measured rather than inherited.

   A quantifier over a sequence does not return while a FREE sequence variable
   must still be asked about, which is why that case is a test on binders.  A
   regular expression is the other way round: the query that exposed this has no
   quantifier at all, its two regex variables being free, and it does not return.
   So a guard written against binders fires on nothing here, and adding a regex
   case beside the sequence one above would have changed nothing -- which is what
   makes this a second arm rather than an entry in the first.

   On
   (and (= re.all (re.union r1 (re.comp (str.to_re "a"))))
        (= re.all (re.union r2 (re.comp (re.union r1 r2))))):
   the solver's own `timeout` parameter, which is what every call here sets, does
   NOT bound it -- killed at 42 s under a 5 s budget, where the same solver run as
   a process with a 5 s wall clock answers `timeout` in five.  Nor does
   cancellation: a watchdog thread calling the solver-local interrupt, and then
   the context-level one the API's documentation recommends over it, both fire and
   are both ignored, because the regex solver does not poll the cancellation flag.
   So there is no bound short of killing the process, and refusing to ask is the
   only thing between a best-effort call and a run that has to be killed.

   The refusal is safe at the four call sites for the same reason the sequence one
   is: each treats "no answer" as the conservative outcome -- the labeling keeps
   the guards it cannot discharge, and discharging one never shown to hold is what
   turns examples that apply nowhere into a refutation.

   With the refusal, two inputs that do not answer when asked do
   (`SyGuS/regex/ex1` and `ex3`, `sat,2` each in under a second), `ex4` keeps
   `sat,1`, and the two constrained-Horn regex reproducers keep `sat,0` and
   `unsat,0` -- those last being the evidence that the string/regex path works
   end to end, so they are what this must not break.

   ON ONLY FOR A Z3 LIBRARY OLDER THAN 5 ([regex_query_refusal]): Z3 5.1.0
   answers the query above, and the other free-regex equalities 4.15.2 did not
   return from, [unknown] within 0.2 s under a 3 s budget, so for it a regex
   query is asked like any other and a caller's conservative outcome for "no
   answer" is reached by the answer rather than by the refusal. *)
let unanswerable_sort_occurs phi =
  Atomic.get regex_query_refusal
  &&
  let bad sort =
    Set.exists (Term.sorts_of_sort sort) ~f:(function
      | T_regex.SRegEx -> true
      | _ -> false)
  in
  Set.exists (Formula.term_sort_env_of phi) ~f:(snd >> bad)
  || Set.exists (Formula.quantified_sort_env_of phi) ~f:(snd >> bad)

(* With COAR_COUNT_MAY_NOT_RETURN set in the environment (and the phase-time
   account on), every call is counted under the innermost open phase, as
   [may-not-return:refused] when the shape is refused and [may-not-return:asked]
   otherwise: how often the refusal fires, and from which phase.  The count
   decides nothing.  A refusal is also printed from a forked copy; the
   others are not, a copy may test thousands of shapes. *)
let count_may_not_return = Stdlib.(Sys.getenv_opt "COAR_COUNT_MAY_NOT_RETURN" <> None)

let may_not_return phi =
  let r =
    Formula.exists_quantified_sort ~f:unsupported_binder_sort phi
    || unanswerable_sort_occurs phi
  in
  if count_may_not_return then
    Common.PhaseTime.event_here ~in_copy:r
      (if r then "may-not-return:refused" else "may-not-return:asked");
  r

(* [recursive_function_under_binder fenv phi]: whether [phi] applies, inside
   the body of a quantifier or of an array lambda, a function of [fenv] that is
   recursive or whose body (transitively) applies one.

   Why: Z3 5.1.0 answers [sat] to such a question with a model that falsifies
   it.  For example,

     (define-fun-rec cnt ((x Int) (t Int) (a (Array Int Int))) Int
       (ite (<= t 0) 0 (+ (cnt x (- t 1) a) (ite (= (select a (- t 1)) x) 1 0))))
     (assert (and (<= 0 t) (<= t 3) (>= n 1) (<= x (- n 2)) (>= c0 2)))
     (assert (forall ((y Int)) (>= (select m y) 0)))
     (assert (forall ((k Int)) (or (> k (- n 1)) (<= (cnt k t m) 1))))
     (assert <c0 = the number of i < t with m[i] = x, unfolded by cases>)

   which is unsatisfiable -- its own instance at [k := x] makes Z3 answer
   [unsat] -- and which Z3 5.1.0 answers [sat]; Z3 4.15.4 and cvc5 answer
   [unknown].  Without the second universal Z3 5.1.0 answers [unsat].  So a
   [sat] (an [Invalid] of a validity question) about such a formula is not a
   model of it, and a caller that reads [sat] as a licence -- a countermodel
   that refutes a problem -- must not ask it.  A recursive application outside
   every binder is not affected: there each application is a ground term the
   solver unfolds, and a model is checked against it.  The test is syntactic and
   over-approximates (an application under a binder that mentions no bound
   variable is counted), which only makes a caller give up a question. *)
let recursive_function_under_binder (fenv : FunEnv.t) phi =
  if Map.Poly.for_all fenv ~f:(fun (_, _, _, is_rec, _) -> not is_rec) then
    false
  else
    (* the functions that are recursive or reach one through the bodies of
       [fenv]: a least fixpoint over the call graph *)
    let calls_one_of acc body =
      Set.exists (Term.funsyms_of body) ~f:(function
        | FVar (v, _, _) -> Set.mem acc v
        | _ -> false)
    in
    let reaching =
      let rec grow acc =
        let acc' =
          Map.Poly.fold fenv ~init:acc
            ~f:(fun ~key ~data:(_, _, body, is_rec, _) acc ->
              if Set.mem acc key then acc
              else if is_rec || calls_one_of acc body then
                Set.add acc key
              else acc)
        in
        if Set.length acc' = Set.length acc then acc else grow acc'
      in
      grow Set.Poly.empty
    in
    let rec term under (t : Term.t) =
      match t with
      | Term.Var _ -> false
      | Term.FunApp (FVar (v, _, _), args, _) ->
          (under && Set.mem reaching v) || List.exists args ~f:(term under)
      | Term.FunApp (T_bool.Formula phi, args, _) ->
          formula under phi || List.exists args ~f:(term under)
      | Term.FunApp (T_array.ALambda _, args, _) ->
          List.exists args ~f:(term true)
      | Term.FunApp (_, args, _) -> List.exists args ~f:(term under)
      | Term.LetTerm (_, _, def, body, _) -> term under def || term under body
    and formula under (phi : Formula.t) =
      match phi with
      | Formula.Atom (Atom.App (Predicate.Fixpoint def, args, _), _) ->
          formula true def.body || List.exists args ~f:(term under)
      | Formula.Atom (Atom.App (_, args, _), _) ->
          List.exists args ~f:(term under)
      | Formula.Atom ((Atom.True _ | Atom.False _), _) -> false
      | Formula.UnaryOp (_, phi, _) -> formula under phi
      | Formula.BinaryOp (_, phi1, phi2, _) ->
          formula under phi1 || formula under phi2
      | Formula.Bind (_, _, phi, _) -> formula true phi
      | Formula.LetRec (defs, phi, _) ->
          List.exists defs ~f:(fun def -> formula true def.body)
          || formula under phi
      | Formula.LetFormula (_, _, def, body, _) ->
          term under def || formula under body
    in
    (not (Set.is_empty reaching)) && formula false phi

(* [fun_values_out], when given, receives the interpretations of the model's
   declarations of arity greater than zero ([fun_values_of]) on [SATISFIABLE];
   it is left untouched otherwise.  [model] itself carries no value for such a
   declaration (see [model_of]), so this is the only way a caller that asked
   about an uninterpreted function learns what the solver chose for it. *)
let check_sat_z3 ?fun_values_out ctx solver dtenv phis =
  Common.PhaseTime.with_phase "assert" (fun () -> z3_solver_add solver phis);
  (* Dump the query as SMT-LIB2 when COAR_DUMP_Z3 is set in the environment.
     This was a dead [if false] branch, which is the same thing with the switch
     welded shut: the one investigation that needed it -- why a quantifier-free
     goal over datatypes with array fields comes back undecided -- could not
     answer "is the query what I think it is" without recompiling.  The lookup
     is done once, not per query. *)
  if dump_z3_queries then
    prerr_endline ("=== Z3 query ===\n" ^ Z3.Solver.to_string solver);
  let started = if dump_z3_queries then Common.Clock.now_float () else Time_float.epoch in
  let status = z3_check solver [] in
  (* The answer and the wall time of each dumped query, on the line after it:
     a run that spends its time in one query among hundreds is otherwise read
     by re-running every dumped query standalone, and a standalone run does not
     meet the pooled context's conditions (see [fresh_solver] in [check_sat]),
     so it does not say which query cost the run its budget. *)
  if dump_z3_queries then
    prerr_endline
      (sprintf "=== Z3 answer: %s in %.3f s ===\n"
         (match status with
         | SATISFIABLE -> "sat"
         | UNSATISFIABLE -> "unsat"
         | UNKNOWN -> "unknown (" ^ Z3.Solver.get_reason_unknown solver ^ ")")
         (Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) started)));
  match status with
  | SATISFIABLE -> (
      match z3_solver_get_model solver with
      | Some model ->
          if false then print_endline @@ Z3.Model.to_string model;
          (match fun_values_out with
          | Some out -> out := fun_values_of ctx dtenv model
          | None -> ());
          let model =
            Common.PhaseTime.with_phase "model" (fun () ->
                model_of ctx dtenv model)
          in
          if false then debug_print_z3_model model;
          `Sat model
      | None -> `Unknown "model production is not enabled?")
  | UNSATISFIABLE -> `Unsat
  | UNKNOWN -> (
      match Z3.Solver.get_reason_unknown solver with
      | "timeout" | "canceled" -> `Timeout
      | reason -> `Unknown reason)

(* A Z3 model describes everything its solver interprets, and the solvers here
   are pooled and reused, so a model can come back carrying a declaration left
   by an earlier query: a query whose variables were [$1:X] and [$2:X] returned
   a model over [$1:X List ; $2:X List ; $2:X ; $1:X] and three further names it
   had never mentioned.  That is harmless to a reader who looks up the variables
   it asked about, and fatal to one that turns the whole model into a
   substitution -- a term substitution is keyed by a variable *name*, so the two
   entries for one name collide, and the process died on [Map.of_alist_exn]
   about one run in six on a tracked benchmark.

   The repair keeps only what the query can be about, and it runs **only when
   some name really does occur twice**: a model without a repeated name is
   returned exactly as it was, so the common path is untouched and no sort has
   to be compared.  Comparing sorts is why the first version of this repair, at
   one of the consumers, cost 14% more CEGIS iterations: a sort can be a
   datatype, and polymorphic comparison does not order those reliably.  Where a
   repeated name *is* in the query, the entry whose sort the query uses is kept
   and the others dropped; where it is not in the query at all, both are
   dropped, since no consumer can mean either of them and a substitution would
   otherwise get an arbitrary one. *)
let restrict_model_to_query phis model =
  let counts =
    List.fold model ~init:Map.Poly.empty ~f:(fun acc ((x, _), _) ->
        Map.Poly.update acc x ~f:(function None -> 1 | Some n -> n + 1))
  in
  let repeated = Map.Poly.filter counts ~f:(fun n -> n > 1) in
  if Map.Poly.is_empty repeated then model
  else begin
    let query_sorts =
      Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
      @@ Set.to_list
      @@ Set.Poly.map ~f:(fun (x, srt) -> (x, Term.str_of_sort srt))
      @@ Set.Poly.union_list
      @@ List.map phis ~f:Formula.term_sort_env_of
    in
    Debug.print
    @@ lazy
         (sprintf
            "[z3:check_sat] the model repeats %d name(s); restricting it \
             to              the query"
            (Map.Poly.length repeated));
    List.filter model ~f:(fun ((x, srt), _) ->
        if not (Map.Poly.mem repeated x) then true
        else
          match Map.Poly.find query_sorts x with
          | None -> false
          | Some s -> String.(s = Term.str_of_sort srt))
  end

(* A deterministic budget for the queries asked while [with_rlimit] runs.

   Z3's [timeout] parameter is wall-clock time: the same query on the same
   binary is decided within its budget on an idle machine and runs out of it
   on a loaded one, so a verdict that rests on a budgeted query depends on what
   else the host is doing.  Z3's [rlimit] counts the solver's own work (its
   resource counter, incremented by the search steps it takes), so a query
   exhausts it at the same point whatever the load.  The price is that the unit
   has no fixed relation to time: a count that takes a second on one query can
   take a minute on another, so a count has to be chosen per input family by
   reading the counter ([(get-info :rlimit)] on the command line) and not
   converted from milliseconds.  The two are combined, never exchanged: a query
   asked under an rlimit keeps its wall-clock [timeout] too, which stays the
   bound on a query Z3 does not interrupt at all.

   The limit is per query: Z3 raises the counter's ceiling by the given amount
   when a check starts.  It is kept per domain, so a solver domain running in
   parallel does not see another's setting.  [None] (the default everywhere)
   leaves every query as it was: the parameter is then not even set. *)
let rlimit_key : int option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

(* A diagnostic of the resource counter, to choose an [rlimit] from: with
   [COAR_Z3_RLIMIT_LOG=FILE] in the environment, every check asked while a
   label is set ([with_rlimit ~label]) appends one line to FILE -- the process,
   the label, the counter's advance over the check (Z3's "rlimit count"
   statistic, which is the context's cumulative counter, read before and after
   the check), the wall-clock seconds, the outcome, the wall-clock budget in
   ms, the query's size, and whether it was quantified and asked in a fresh
   context.  A label already set is kept, so a check asked inside a labelled
   question is logged under the question's label.  A forked copy inherits the
   label and appends its own lines.
   Without the variable nothing is read or written, and a check is asked
   exactly as before. *)
(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let rlimit_log_file = Lazy.from_val (Sys.getenv "COAR_Z3_RLIMIT_LOG")

let rlimit_label_key : string option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let rlimit_log_line line =
  match Lazy.force rlimit_log_file with
  | None -> ()
  | Some file ->
      Out_channel.with_file file ~append:true ~f:(fun oc ->
          Out_channel.output_string oc line;
          Out_channel.newline oc)

let rlimit_log_line_lazy line =
  if Option.is_some (Lazy.force rlimit_log_file) then
    rlimit_log_line (Lazy.force line)

(* the counter of [solver]'s context; [None] when Z3 does not report it *)
let rlimit_count_of solver =
  try
    match
      Z3.Statistics.get (Z3.Solver.get_statistics solver) "rlimit count"
    with
    | Some e -> Float.of_string_opt (Z3.Statistics.Entry.to_string_value e)
    | None -> None
  with _ -> None

let with_rlimit ?label rlimit f =
  let f =
    match (label, Lazy.force rlimit_log_file) with
    | Some _, Some _
      when Option.is_none (Stdlib.Domain.DLS.get rlimit_label_key) ->
        fun () ->
          let saved = Stdlib.Domain.DLS.get rlimit_label_key in
          Stdlib.Domain.DLS.set rlimit_label_key label;
          Exn.protect ~f ~finally:(fun () ->
              Stdlib.Domain.DLS.set rlimit_label_key saved)
    | _ -> f
  in
  match rlimit with
  | None -> f ()
  | Some _ ->
      let saved = Stdlib.Domain.DLS.get rlimit_key in
      Stdlib.Domain.DLS.set rlimit_key rlimit;
      Exn.protect ~f ~finally:(fun () -> Stdlib.Domain.DLS.set rlimit_key saved)

(* The arithmetic solver Z3's [smt] core uses for the queries asked while
   [with_arith_solver] runs: Z3's [smt.arith.solver] parameter, whose default
   (6) is the [lp]-based [theory_lra] and whose 2 is the older simplex-based
   [theory_arith].  Both are decision procedures for linear arithmetic, so the
   choice changes how long a question takes and, on a question outside the
   decidable fragment (quantifiers, nonlinear terms), whether it is decided --
   never what a decision says.

   Why it is worth choosing: on quantifier-free template-coefficient
   questions (many bounded integer coefficients, in disjunctions of linear
   constraints) the default spends its time in bound propagation and the [lp]
   tableau, and [theory_arith] decided the same questions 5 to 30 times
   faster, [unsat] ones especially (Z3 5.1.0).  On some sequence questions it
   was slower, so it is chosen per call site and never process-wide.

   Kept per domain, like the rlimit.  A pooled query asked under a setting
   takes its instance from a pool of its own, one per setting, because Z3
   picks the arithmetic theory when a solver's core is first set up: a pooled
   solver already checked under one setting keeps that theory whatever its
   parameters say afterwards, so sharing instances across settings would
   silently ask some questions under the other.  [None] (the default
   everywhere) leaves every query as it was, the parameter not even set. *)
let arith_solver_key : int option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_arith_solver arith_solver f =
  match arith_solver with
  | None -> f ()
  | Some _ ->
      let saved = Stdlib.Domain.DLS.get arith_solver_key in
      Stdlib.Domain.DLS.set arith_solver_key arith_solver;
      Exn.protect ~f ~finally:(fun () ->
          Stdlib.Domain.DLS.set arith_solver_key saved)

let arith_solver_pools :
    ( int,
      (int option * (string * string) list, instance) Hashtbl.Poly.t )
    Hashtbl.Poly.t =
  Hashtbl.Poly.create ()

(* the pool a pooled query is taken from under the setting [arith_solver] *)
let pool_of_arith_solver = function
  | None -> instance_pool
  | Some n ->
      with_pool_lock (fun () ->
          Hashtbl.Poly.find_or_add arith_solver_pools n
            ~default:Hashtbl.Poly.create)

let add_arith_solver_param ctx params = function
  | None -> ()
  | Some n ->
      Z3.Params.add_int params (Z3.Symbol.mk_string ctx "smt.arith.solver") n

(* Z3 reports an exhausted resource limit as [unknown] with a reason that is
   not "timeout": "canceled", "push canceled" or "max. resource limit
   exceeded" were seen depending on the solver path.  Under an rlimit those
   mean the budget ran out, which callers here call [`Timeout]. *)
let rlimit_exhausted_reason reason =
  String.is_substring reason ~substring:"canceled"
  || String.is_substring reason ~substring:"resource limit"

(* ------------------------------------------------------------------
   Integer variables that are bit-vectors in disguise.

   An input that keeps a machine word in an [Int] and reads it through
   [(_ int_to_bv n)] makes Z3 reason about the conversion, which it does by
   arithmetic modulo 2^n; asking the same question with the word declared as a
   bit-vector lets it bit-blast instead.  On a popcount loop's step clause the
   question took 7.6-10 s as written and 0.35 s with each such word [x]
   replaced by [ubv_to_int xb] for a fresh [xb] of sort [(_ BitVec n)]: Z3
   then rewrites [int_to_bv n (ubv_to_int xb)] to [xb] itself.

   [int_to_bv_range_subst phis] applies two rewrites in turn and returns the
   rewritten [phis'] with a list of [(x, xb, n, q)]: the bounded rewrite below
   ([q = None]), then the split of [int_to_bv_split_subst] further down.
   Contract of the bounded rewrite, [int_to_bv_bounded_subst phis]: it returns
   [phis'] and a list of [(x, xb, n)].  [x] is a free [Int] variable of [phis] that occurs directly
   under [int_to_bv n] somewhere in them, and among the top-level conjuncts of
   [phis] are both a lower bound [0 <= x] and an upper bound [x < c] with
   [c <= 2^n].  A top-level conjunct is read through conjunctions and through
   a negated disjunction (a validity question about a clause arrives as
   [not (l1 \/ ... \/ lk)]), and a bound is any integer comparison, possibly
   negated, whose two sides are linear and whose difference mentions [x] alone
   with coefficient 1 or -1 (the normaliser writes [x < 2^64] as
   [not (0 <= -2^64 + x)]).  [phis'] is [phis] with every such [x]
   replaced by [ubv_to_int xb].  Since the conjuncts force [x] into
   [[0, 2^n)], which [ubv_to_int] maps [(_ BitVec n)] onto bijectively, [phis']
   is satisfiable exactly when [phis] is, and a model of [phis'] gives one of
   [phis] by [x := ubv_to_int (value of xb)] ([int_to_bv_range_model]).  A
   bound that is a conjunct of a disjunct, or under a quantifier, is not used:
   only a top-level conjunct holds in every model.  A variable bound by a
   quantifier is never replaced ([term_sort_env_of] lists free variables). *)

(* The free variables of [phis] that may be replaced as integers: free at
   [Int], and at no other sort anywhere in [phis], free or bound.  A question
   is a list of formulas whose variables are named independently (a clause
   beside the axioms or lemmas asked with it), so one name can stand for an
   [Int] in one formula and for a sequence in another; [Formula.subst] goes by
   name, and replacing such a name rewrote the sequence's occurrences into an
   integer term, which Z3 then refused as the argument of [seq.len]. *)
let int_only_free_vars phis =
  let free = Set.Poly.union_list (List.map phis ~f:Formula.term_sort_env_of) in
  let bound =
    Set.Poly.union_list (List.map phis ~f:Formula.quantified_sort_env_of)
  in
  let other =
    Set.Poly.filter_map (Set.union free bound) ~f:(fun (x, srt) ->
        if Stdlib.(srt = T_int.SInt) then None else Some x)
  in
  Set.Poly.filter_map free ~f:(fun (x, srt) ->
      if Stdlib.(srt = T_int.SInt) && not (Set.mem other x) then Some x
      else None)

let int_to_bv_bounded_subst phis =
  let free_ints = int_only_free_vars phis in
  (* the widest [int_to_bv n] each free integer variable occurs directly
     under *)
  let widths =
    List.fold phis ~init:Map.Poly.empty ~f:(fun acc phi ->
        Set.fold
          (Formula.filtered_terms_of phi ~f:(function
            | Term.FunApp (T_irb.IntToBV (Some _), [ Term.Var (x, _, _) ], _)
              ->
                Set.mem free_ints x
            | _ -> false))
          ~init:acc
          ~f:(fun acc -> function
            | Term.FunApp (T_irb.IntToBV (Some n), [ Term.Var (x, _, _) ], _)
              ->
                Map.Poly.update acc x ~f:(function
                  | None -> n
                  | Some m -> max m n)
            | _ -> acc))
  in
  if Map.Poly.is_empty widths then (phis, [])
  else
    (* the top-level conjuncts as literals: a negated disjunction is the
       conjunction of the negated disjuncts, which is how a validity question
       about a clause arrives here *)
    let rec lits pos phi =
      match phi with
      | Formula.BinaryOp (Formula.And, p1, p2, _) when pos ->
          lits pos p1 @ lits pos p2
      | Formula.BinaryOp (Formula.Or, p1, p2, _) when not pos ->
          lits pos p1 @ lits pos p2
      | Formula.UnaryOp (Formula.Not, p, _) -> lits (not pos) p
      | Formula.Atom (atm, _) -> [ (pos, atm) ]
      | _ -> []
    in
    (* an integer term as [sum a_i x_i + c], when it is linear *)
    let rec lin = function
      | Term.Var (x, T_int.SInt, _) -> Some (Map.Poly.singleton x Z.one, Z.zero)
      | Term.FunApp (T_int.Int c, [], _) -> Some (Map.Poly.empty, c)
      | Term.FunApp (T_int.Add, [ t1; t2 ], _) -> lin_comb Z.one t1 Z.one t2
      | Term.FunApp (T_int.Sub, [ t1; t2 ], _) -> lin_comb Z.one t1 Z.minus_one t2
      | Term.FunApp (T_int.Neg, [ t ], _) -> lin_comb Z.zero t Z.minus_one t
      | Term.FunApp (T_int.Mul, [ Term.FunApp (T_int.Int a, [], _); t ], _)
      | Term.FunApp (T_int.Mul, [ t; Term.FunApp (T_int.Int a, [], _) ], _) ->
          lin_comb Z.zero t a t
      | _ -> None
    and lin_comb a1 t1 a2 t2 =
      match (lin t1, lin t2) with
      | Some (m1, c1), Some (m2, c2) ->
          let scale a m = Map.Poly.map m ~f:(Z.mul a) in
          Some
            ( Map.Poly.merge (scale a1 m1) (scale a2 m2) ~f:(fun ~key:_ -> function
                | `Left a | `Right a -> Some a
                | `Both (a, b) -> Some (Z.add a b)),
              Z.(add (mul a1 c1) (mul a2 c2)) )
      | _ -> None
    in
    (* [`Lo (x, c)] says [c <= x], [`Hi (x, c)] says [x < c]; the literal is
       first written [e >= 0] *)
    let bound_of (pos, atm) =
      let ge0 =
        match atm with
        | Atom.App (Predicate.Psym psym, [ t1; t2 ], _) -> (
            let diff a b = lin_comb Z.one a Z.minus_one b in
            let dec = Option.map ~f:(fun (m, c) -> (m, Z.pred c)) in
            match psym with
            | T_int.Geq -> diff t1 t2
            | T_int.Leq -> diff t2 t1
            | T_int.Gt -> dec (diff t1 t2)
            | T_int.Lt -> dec (diff t2 t1)
            | _ -> None)
        | _ -> None
      in
      let ge0 =
        if pos then ge0
        else
          (* not (e >= 0) is -e - 1 >= 0 over the integers *)
          Option.map ge0 ~f:(fun (m, c) ->
              (Map.Poly.map m ~f:Z.neg, Z.(pred (neg c))))
      in
      match ge0 with
      | Some (m, c) -> (
          match Map.Poly.to_alist (Map.Poly.filter m ~f:(fun a -> not (Z.equal a Z.zero))) with
          | [ (x, a) ] when Z.equal a Z.one -> Some (`Lo (x, Z.neg c))
          | [ (x, a) ] when Z.equal a Z.minus_one -> Some (`Hi (x, Z.succ c))
          | _ -> None)
      | None -> None
    in
    let lits = List.concat_map phis ~f:(lits true) in
    let bounds = List.filter_map lits ~f:bound_of in
    let has_lo x =
      List.exists bounds ~f:(function
        | `Lo (y, c) -> Ident.tvar_equal x y && Z.(geq c zero)
        | `Hi _ -> false)
    in
    let has_hi x n =
      List.exists bounds ~f:(function
        | `Hi (y, c) -> Ident.tvar_equal x y && Z.(leq c (shift_left one n))
        | `Lo _ -> false)
    in
    let picked =
      Map.Poly.fold widths ~init:[] ~f:(fun ~key:x ~data:n acc ->
          if has_lo x && has_hi x n then
            (x, Ident.mk_fresh_tvar ~prefix:(Some "bvr") (), n) :: acc
          else acc)
    in
    if List.is_empty picked then (phis, [])
    else
      let sub =
        Map.Poly.of_alist_exn
        @@ List.map picked ~f:(fun (x, xb, n) ->
               ( x,
                 T_irb.mk_bv_to_int ~size:(Some n) ~signed:(Some false)
                   (Term.mk_var xb (T_bv.SBV (Some n))) ))
      in
      (List.map phis ~f:(Formula.subst sub), picked)

(* A free integer variable [x] that occurs as [int_to_bv n x] for one [n]
   needs no bounds.  Every integer is [2^n * q + ubv_to_int xb] for exactly one
   integer [q] and one [xb] of sort [(_ BitVec n)], and then
   [int_to_bv n x = xb]; so replacing each [int_to_bv n x] by a fresh [xb] and
   every other occurrence of [x] by [2^n * q + ubv_to_int xb], for a fresh [q],
   gives an equisatisfiable question, and a model of it gives one of the
   original by [x := 2^n * q + ubv_to_int xb].  Where [x] occurs only under
   [int_to_bv n], no [q] is introduced.  This is the shape of a parametric
   example's parameter standing for a word: Z3 5.1.0 did not decide in 30 s a
   one-parameter question reading a bit of [int_to_bv 64 c] beside [1 + c] in
   an equation, and decided it in 0.06 s once split.  A variable also bound by
   a quantifier somewhere in the question is left alone, so that the
   replacement cannot reach a shadowing occurrence. *)
let int_to_bv_split_subst phis =
  let free_ints = int_only_free_vars phis in
  let bound =
    Set.Poly.map ~f:fst
    @@ Set.Poly.union_list (List.map phis ~f:Formula.quantified_sort_env_of)
  in
  let widths =
    List.fold phis ~init:Map.Poly.empty ~f:(fun acc phi ->
        Set.fold
          (Formula.filtered_terms_of phi ~f:(function
            | Term.FunApp (T_irb.IntToBV (Some _), [ Term.Var (x, _, _) ], _)
              ->
                Set.mem free_ints x && not (Set.mem bound x)
            | _ -> false))
          ~init:acc
          ~f:(fun acc -> function
            | Term.FunApp (T_irb.IntToBV (Some n), [ Term.Var (x, _, _) ], _)
              ->
                Map.Poly.update acc x ~f:(function
                  | None -> Some n
                  | Some (Some m) when m = n -> Some m
                  | Some _ -> None)
            | _ -> acc))
    |> Map.Poly.filter_map ~f:Fn.id
  in
  if Map.Poly.is_empty widths then (phis, [])
  else
    let fresh =
      Map.Poly.mapi widths ~f:(fun ~key:_ ~data:n ->
          (Ident.mk_fresh_tvar ~prefix:(Some "bvs") (), n))
    in
    let f = function
      | Term.FunApp (T_irb.IntToBV (Some m), [ Term.Var (x, _, _) ], _) as t
        -> (
          match Map.Poly.find fresh x with
          | Some (xb, n) when m = n -> Term.mk_var xb (T_bv.SBV (Some n))
          | _ -> t)
      | t -> t
    in
    let phis' = List.map phis ~f:(Formula.map_term ~f) in
    let left =
      Set.Poly.map ~f:fst
      @@ Set.Poly.union_list (List.map phis' ~f:Formula.term_sort_env_of)
    in
    let picked =
      Map.Poly.fold fresh ~init:[] ~f:(fun ~key:x ~data:(xb, n) acc ->
          let q =
            if Set.mem left x then
              Some (Ident.mk_fresh_tvar ~prefix:(Some "bvq") ())
            else None
          in
          (x, xb, n, q) :: acc)
    in
    let sub =
      Map.Poly.of_alist_exn
      @@ List.filter_map picked ~f:(fun (x, xb, n, q) ->
             Option.map q ~f:(fun q ->
                 ( x,
                   T_int.mk_add
                     (T_int.mk_mul
                        (T_int.mk_int (Z.shift_left Z.one n))
                        (Term.mk_var q T_int.SInt))
                     (T_irb.mk_bv_to_int ~size:(Some n) ~signed:(Some false)
                        (Term.mk_var xb (T_bv.SBV (Some n)))) )))
    in
    let phis' =
      if Map.Poly.is_empty sub then phis'
      else List.map phis' ~f:(Formula.subst sub)
    in
    (phis', picked)

(* Bit-vector twins of a question's bounded integer arithmetic.

   WHY.  A question that reads bits of words through [int_to_bv n] and also
   states integer facts about the same words -- an index [i] below a bound, its
   word [i div 64], its bit [i mod 64], a mask [m] with [m + 1 = 2^r] -- is
   decided by neither Z3 5.1.0 nor cvc5 1.0.4 when the two halves meet only
   through [int_to_bv] and [ubv_to_int]: on the verification of a bit set's
   [clear_excess_bits_in_final_word] the ground core ran past 30 s in Z3 and
   60 s in cvc5, while its integer half alone (that the bit index lies below
   the shift) was answered in 0.07 s and its bit-vector half alone in 0.1 s.
   Stating the integer facts a second time over bit-vectors, with every
   bounded integer named by a bit-vector, let Z3 answer the same core in
   0.2-0.3 s with the integer facts left in place.

   [int_to_bv_twins_subst phis] returns [(phis', fresh)].  Let [n] be the
   widest [int_to_bv n] in [phis] (nothing is done without one) and
   [w = n + 8].  A KEY is an integer term that is a variable or an
   application whose head is not integer arithmetic ([seq.len s],
   [seq.nth s i], a selector), mentions no variable a quantifier of [phis]
   binds, and is bounded by top-level conjuncts (read as
   [int_to_bv_bounded_subst] reads them) as [0 <= key] and [key < c] with
   [c <= 2^n], directly or through two rounds of propagation along the
   top-level linear literals over several keys ([x < y] with [y < 2^64]).  Each key used below gets a fresh [kb : (_ BitVec n)] and the
   conjunct [key = ubv_to_int kb].  An integer term is TRANSLATED to a
   width-[w] term when it is built from keys, numerals, [+], [-], negation,
   products by a numeral, [div] and [mod] by a positive numeral in every
   rounding mode but the ceiling (as [bvudiv]/[bvurem] of a non-negative
   operand, otherwise as [bvsdiv]/[bvsrem] corrected to the floor where the
   mode asks for it),
   [ubv_to_int] of a word of width below [w], and [ite] on a translated
   condition; a key becomes [zext kb], and every subterm's value interval
   (each key within [[0, 2^n)]) must lie within the signed range of width
   [w], so that the translation's signed value is the integer's in every model
   of the conjuncts.  Then:
   - each top-level integer literal (a comparison or an equation between
     integers) whose both sides translate, which reads a key or a word, and
     which is not a bound [0 <= key] or [key < c] with [c >= 2^n] (implied by
     the twin's width), gets its twin over signed bit-vector comparisons as one more conjunct;
   - each [int_to_bv m t] with [m <= w] and [t] translated becomes the low [m]
     bits of the translation, since [int_to_bv m] is reduction modulo [2^m]
     and the low [m] bits of a two's complement value are that value modulo
     [2^m]; before that, [int_to_bv] is moved into an [ite], a read of a
     sequence store is split by where it reads, and a read [nth s j] beside a
     key [nth s i] is split on [j = i] (each step an identity, see [to_bv]),
     the conditions so introduced stated over the integers and, where they
     translate, over bit-vectors too;
   - an [ite] whose condition the top-level bounds decide (a single-key
     bound such as [x >= 0] beside [0 <= x]) is replaced by its branch.
   Every added conjunct holds in every model of [phis] extended by
   [kb := int_to_bv n key], and every replaced term equals its replacement
   there, so [phis'] is satisfiable exactly when [phis] is, and a model of
   [phis'] restricted to [phis]'s variables is one of [phis] ([fresh] lists
   the names to drop).  The integer literals are kept: twins are added, never
   substituted. *)
let int_to_bv_twins_subst ?(generalize = false) phis =
  let width =
    List.fold phis ~init:None ~f:(fun acc phi ->
        Set.fold
          (Formula.filtered_terms_of phi ~f:(function
            | Term.FunApp (T_irb.IntToBV (Some _), [ _ ], _) -> true
            | _ -> false))
          ~init:acc
          ~f:(fun acc -> function
            | Term.FunApp (T_irb.IntToBV (Some n), [ _ ], _) -> (
                match acc with None -> Some n | Some m -> Some (max m n))
            | _ -> acc))
  in
  match width with
  | None -> (phis, [])
  | Some n ->
      let w = n + 8 in
      let bound_names =
        Set.Poly.map ~f:fst
        @@ Set.Poly.union_list (List.map phis ~f:Formula.quantified_sort_env_of)
      in
      let closed t = Set.is_empty (Set.inter (Term.tvs_of t) bound_names) in
      let is_int t =
        try Stdlib.(Term.sort_of t = T_int.SInt)
        with exn_ when not (Common.Timer.is_async exn_) -> false
      in
      let is_arith_head = function
        | T_int.Int _ | T_int.Add | T_int.Sub | T_int.Neg | T_int.Mul
        | T_int.Div _ | T_int.Rem _ | T_bool.IfThenElse | T_irb.BVToInt _ ->
            true
        | _ -> false
      in
      let is_key = function
        | Term.Var (_, T_int.SInt, _) as t -> closed t
        | Term.FunApp (fsym, _, _) as t ->
            (not (is_arith_head fsym)) && is_int t && closed t
        | _ -> false
      in
      (* the top-level literals, as [int_to_bv_bounded_subst] reads them, and
         also through a formula embedded as a term and compared with [true]
         or [false] ([(<phi>) = (<true>)], the SMT-LIB reader's form of a
         Boolean [ite] branch or a [let]-bound formula) *)
      let rec lits pos phi =
        match phi with
        | Formula.BinaryOp (Formula.And, p1, p2, _) when pos ->
            lits pos p1 @ lits pos p2
        | Formula.BinaryOp (Formula.Or, p1, p2, _) when not pos ->
            lits pos p1 @ lits pos p2
        | Formula.UnaryOp (Formula.Not, p, _) -> lits (not pos) p
        | Formula.Atom
            ( Atom.App
                ( Predicate.Psym ((T_bool.Eq | T_bool.Neq) as psym),
                  [ a; b ],
                  _ ),
              _ ) as atom -> (
            let embedded t c =
              match t with
              | Term.FunApp (T_bool.Formula p, [], _)
                when T_bool.is_true c || T_bool.is_false c ->
                  Some (p, T_bool.is_true c)
              | _ -> None
            in
            match Option.first_some (embedded a b) (embedded b a) with
            | Some (p, with_true) ->
                let same = Stdlib.(psym = T_bool.Eq) in
                lits (Bool.equal pos (Bool.equal same with_true)) p
            | None -> (
                match atom with Formula.Atom (atm, _) -> [ (pos, atm) ] | _ -> []))
        | Formula.Atom (atm, _) -> [ (pos, atm) ]
        | _ -> []
      in
      let lits = List.concat_map phis ~f:(lits true) in
      (* an integer term as [sum a_k k + c] over keys [k], when it is linear *)
      let rec lin t =
        match t with
        | Term.FunApp (T_int.Int c, [], _) -> Some (Map.Poly.empty, c)
        | Term.FunApp (T_int.Add, [ t1; t2 ], _) -> comb Z.one t1 Z.one t2
        | Term.FunApp (T_int.Sub, [ t1; t2 ], _) -> comb Z.one t1 Z.minus_one t2
        | Term.FunApp (T_int.Neg, [ t1 ], _) ->
            Option.map (lin t1) ~f:(fun (m, c) ->
                (Map.Poly.map m ~f:Z.neg, Z.neg c))
        | Term.FunApp (T_int.Mul, [ Term.FunApp (T_int.Int a, [], _); t1 ], _)
        | Term.FunApp (T_int.Mul, [ t1; Term.FunApp (T_int.Int a, [], _) ], _)
          ->
            Option.map (lin t1) ~f:(fun (m, c) ->
                (Map.Poly.map m ~f:(Z.mul a), Z.mul a c))
        | t when is_key t -> Some (Map.Poly.singleton t Z.one, Z.zero)
        | _ -> None
      and comb a1 t1 a2 t2 =
        match (lin t1, lin t2) with
        | Some (m1, c1), Some (m2, c2) ->
            let scale a m = Map.Poly.map m ~f:(Z.mul a) in
            Some
              ( Map.Poly.merge (scale a1 m1) (scale a2 m2) ~f:(fun ~key:_ ->
                  function
                  | `Left a | `Right a -> Some a
                  | `Both (a, b) -> Some (Z.add a b)),
                Z.(add (mul a1 c1) (mul a2 c2)) )
        | _ -> None
      in
      (* a literal as a bound [lo <= k] or [k < hi] on one key *)
      let bound_of (pos, atm) =
        let ge0 =
          match atm with
          | Atom.App (Predicate.Psym psym, [ t1; t2 ], _) -> (
              let diff a b = comb Z.one a Z.minus_one b in
              let dec = Option.map ~f:(fun (m, c) -> (m, Z.pred c)) in
              match psym with
              | T_int.Geq -> diff t1 t2
              | T_int.Leq -> diff t2 t1
              | T_int.Gt -> dec (diff t1 t2)
              | T_int.Lt -> dec (diff t2 t1)
              | _ -> None)
          | _ -> None
        in
        let ge0 =
          if pos then ge0
          else
            (* not (e >= 0) is -e - 1 >= 0 over the integers *)
            Option.map ge0 ~f:(fun (m, c) ->
                (Map.Poly.map m ~f:Z.neg, Z.(pred (neg c))))
        in
        match ge0 with
        | Some (m, c) -> (
            match
              Map.Poly.to_alist
                (Map.Poly.filter m ~f:(fun a -> not (Z.equal a Z.zero)))
            with
            | [ (k, a) ] when Z.equal a Z.one -> Some (k, `Lo (Z.neg c))
            | [ (k, a) ] when Z.equal a Z.minus_one -> Some (k, `Hi (Z.succ c))
            | _ -> None)
        | None -> None
      in
      (* the bounds the literals state on one key, then those they imply
         through literals over several keys: a literal [sum a_i k_i + c >= 0]
         with [a_j = 1] gives [k_j >= -c - sum_{i <> j} a_i hi_i] (with the
         upper end of each other key, or its lower end for a negative
         coefficient), and [a_j = -1] the upper bound likewise; two rounds,
         which carry a bound along [x < y], [y < 2^64] and one step more.
         Every bound so derived holds in every model of the conjuncts. *)
      let ge0s =
        List.filter_map lits ~f:(fun (pos, atm) ->
            match atm with
            | Atom.App (Predicate.Psym psym, [ t1; t2 ], _) -> (
                let diff a b = comb Z.one a Z.minus_one b in
                let dec = Option.map ~f:(fun (m, c) -> (m, Z.pred c)) in
                let g =
                  match psym with
                  | T_int.Geq -> diff t1 t2
                  | T_int.Leq -> diff t2 t1
                  | T_int.Gt -> dec (diff t1 t2)
                  | T_int.Lt -> dec (diff t2 t1)
                  | _ -> None
                in
                if pos then g
                else
                  Option.map g ~f:(fun (m, c) ->
                      (Map.Poly.map m ~f:Z.neg, Z.(pred (neg c)))))
            | _ -> None)
        |> List.map ~f:(fun (m, c) ->
               (Map.Poly.filter m ~f:(fun a -> not (Z.equal a Z.zero)), c))
        |> List.filter ~f:(fun (m, _) -> Map.Poly.length m >= 2)
      in
      let derive bounds =
        (* inclusive ends known so far *)
        let lo_of k =
          List.fold bounds ~init:None ~f:(fun acc -> function
            | k', `Lo c when Stdlib.(k = k') ->
                Some (Option.value_map acc ~default:c ~f:(Z.max c))
            | _ -> acc)
        in
        let hi_of k =
          List.fold bounds ~init:None ~f:(fun acc -> function
            | k', `Hi c when Stdlib.(k = k') ->
                Some (Option.value_map acc ~default:(Z.pred c) ~f:(Z.min (Z.pred c)))
            | _ -> acc)
        in
        List.concat_map ge0s ~f:(fun (m, c) ->
            List.filter_map (Map.Poly.to_alist m) ~f:(fun (kj, aj) ->
                if not (Z.equal (Z.abs aj) Z.one) then None
                else
                  (* the largest value of the rest [sum_{i <> j} a_i k_i] *)
                  let rest_max =
                    Map.Poly.fold m ~init:(Some Z.zero) ~f:(fun ~key:k ~data:a acc ->
                        if Stdlib.(k = kj) then acc
                        else
                          match acc with
                          | None -> None
                          | Some acc -> (
                              let e = if Z.(gt a zero) then hi_of k else lo_of k in
                              match e with
                              | Some e -> Some (Z.add acc (Z.mul a e))
                              | None -> None))
                  in
                  match rest_max with
                  | None -> None
                  | Some r ->
                      (* a_j k_j >= -c - r *)
                      let b = Z.(neg c - r) in
                      if Z.(gt aj zero) then Some (kj, `Lo b)
                      else Some (kj, `Hi (Z.succ (Z.neg b)))))
      in
      let bounds = List.filter_map lits ~f:bound_of in
      let bounds = bounds @ derive bounds in
      let bounds = bounds @ derive bounds in
      let bounded k =
        List.exists bounds ~f:(function
          | k', `Lo c -> Stdlib.(k = k') && Z.(geq c zero)
          | _ -> false)
        && List.exists bounds ~f:(function
             | k', `Hi c -> Stdlib.(k = k') && Z.(leq c (shift_left one n))
             | _ -> false)
      in
      let names = Hashtbl.Poly.create () in
      let name_of k =
        Hashtbl.find_or_add names k ~default:(fun () ->
            Ident.mk_fresh_tvar ~prefix:(Some "bvt") ())
      in
      let smax = Z.shift_left Z.one (w - 1) in
      let fits (lo, hi) = Z.(geq lo (neg smax) && lt hi smax) in
      let size = Some w in
      let num c = T_bv.mk_bvnum ~size c in
      let zext m t = T_bv.mk_bvzext ~size:(Some m) (w - m) t in
      (* a positive power of two *)
      let is_pow2 c = Z.(gt c zero) && Z.(equal (logand c (pred c)) zero) in
      (* the truncated quotient of [a] by [2^k] ([k >= 1]): [a] plus [2^k - 1]
         where it is negative (its sign spread over the width, shifted down to
         [k] ones), shifted right arithmetically; the sum does not wrap, since
         the bias is added only to a negative value *)
      let trunc_shift a k =
        let bias =
          T_bv.mk_bvlshr ~size
            (T_bv.mk_bvashr ~size a (num (Z.of_int (w - 1))))
            (num (Z.of_int (w - k)))
        in
        T_bv.mk_bvashr ~size (T_bv.mk_bvadd ~size a bias) (num (Z.of_int k))
      in
      (* [Some (t', (lo, hi))]: [t'] of width [w] whose signed value is [t]'s
         in every model of the conjuncts, [t] within [[lo, hi]] there *)
      let rec tr t =
        let res =
          match t with
          | Term.FunApp (T_int.Int c, [], _) -> Some (num c, (c, c))
          | Term.FunApp (T_int.Add, [ t1; t2 ], _) ->
              bin t1 t2
                (fun a b -> T_bv.mk_bvadd ~size a b)
                (fun (l1, h1) (l2, h2) -> Z.(l1 + l2, h1 + h2))
          | Term.FunApp (T_int.Sub, [ t1; t2 ], _) ->
              bin t1 t2
                (fun a b -> T_bv.mk_bvsub ~size a b)
                (fun (l1, h1) (l2, h2) -> Z.(l1 - h2, h1 - l2))
          | Term.FunApp (T_int.Neg, [ t1 ], _) ->
              Option.map (tr t1) ~f:(fun (a, (l, h)) ->
                  (T_bv.mk_bvneg ~size a, Z.(neg h, neg l)))
          | Term.FunApp (T_int.Mul, [ Term.FunApp (T_int.Int c, [], _); t1 ], _)
          | Term.FunApp (T_int.Mul, [ t1; Term.FunApp (T_int.Int c, [], _) ], _)
            ->
              Option.map (tr t1) ~f:(fun (a, (l, h)) ->
                  let x = Z.mul c l and y = Z.mul c h in
                  (T_bv.mk_bvmul ~size (num c) a, (Z.min x y, Z.max x y)))
          | Term.FunApp
              ( T_int.Div ((Value.Euclidean | Value.Truncated | Value.Flooring) as md),
                [ t1; Term.FunApp (T_int.Int c, [], _) ],
                _ )
            when Atomic.get int_to_bv_pow2_shifts && is_pow2 c ->
              Option.map (tr t1) ~f:(fun (a, (l, h)) ->
                  let k = Z.log2 c in
                  if k = 0 then (a, (l, h))
                  else if Z.(geq l zero) then
                    (T_bv.mk_bvlshr ~size a (num (Z.of_int k)), (Z.fdiv l c, Z.fdiv h c))
                  else if Stdlib.(md = Value.Truncated) then
                    (trunc_shift a k, (Z.min (Z.div l c) (Z.div h c), Z.max (Z.div l c) (Z.div h c)))
                  else
                    (T_bv.mk_bvashr ~size a (num (Z.of_int k)), (Z.fdiv l c, Z.fdiv h c)))
          | Term.FunApp
              ( T_int.Rem ((Value.Euclidean | Value.Truncated | Value.Flooring) as md),
                [ t1; Term.FunApp (T_int.Int c, [], _) ],
                _ )
            when Atomic.get int_to_bv_pow2_shifts && is_pow2 c ->
              Option.map (tr t1) ~f:(fun (a, (l, h)) ->
                  let k = Z.log2 c in
                  let low = T_bv.mk_bvand ~size a (num (Z.pred c)) in
                  if Z.(geq l zero) then (low, (Z.zero, Z.min h (Z.pred c)))
                  else if Stdlib.(md = Value.Truncated) then
                    (* the truncated remainder: the value less its truncated
                       quotient times [2^k] *)
                    ( T_bv.mk_bvsub ~size a
                        (T_bv.mk_bvshl ~size (trunc_shift a k) (num (Z.of_int k))),
                      ( (if Z.(geq l zero) then Z.zero else Z.neg (Z.pred c)),
                        if Z.(leq h zero) then Z.zero else Z.pred c ) )
                  else (low, (Z.zero, Z.pred c)))
          | Term.FunApp
              ( T_int.Div ((Value.Euclidean | Value.Truncated | Value.Flooring) as md),
                [ t1; Term.FunApp (T_int.Int c, [], _) ],
                _ )
            when Z.(gt c zero) -> (
              match tr t1 with
              | Some (a, (l, h)) when Z.(geq l zero) ->
                  Some
                    ( T_bv.mk_bvdiv ~size ~signed:(Some false) a (num c),
                      (Z.fdiv l c, Z.fdiv h c) )
              | Some (a, (l, h)) ->
                  (* a signed operand: [bvsdiv] truncates, and the floor
                     (Euclidean and flooring, the divisor being positive) is
                     one less where the truncated remainder is negative *)
                  let q = T_bv.mk_bvdiv ~size ~signed:(Some true) a (num c) in
                  if Stdlib.(md = Value.Truncated) then
                    Some (q, (Z.min (Z.div l c) (Z.div h c), Z.max (Z.div l c) (Z.div h c)))
                  else
                    let neg =
                      Formula.mk_atom
                        (T_bv.mk_bvlt ~size ~signed:(Some true)
                           (T_bv.mk_bvrem ~size ~signed:(Some true) a (num c))
                           (num Z.zero))
                    in
                    Some
                      ( T_bool.mk_if_then_else (T_bool.of_formula neg)
                          (T_bv.mk_bvsub ~size q (num Z.one))
                          q,
                        (Z.fdiv l c, Z.fdiv h c) )
              | None -> None)
          | Term.FunApp
              ( T_int.Rem ((Value.Euclidean | Value.Truncated | Value.Flooring) as md),
                [ t1; Term.FunApp (T_int.Int c, [], _) ],
                _ )
            when Z.(gt c zero) -> (
              match tr t1 with
              | Some (a, (l, h)) when Z.(geq l zero) ->
                  Some
                    ( T_bv.mk_bvrem ~size ~signed:(Some false) a (num c),
                      (Z.zero, Z.min h (Z.pred c)) )
              | Some (a, (l, h)) ->
                  (* a signed operand: [bvsrem] takes the operand's sign, and
                     the Euclidean (and, for a positive divisor, flooring)
                     remainder adds the divisor where that is negative *)
                  let r = T_bv.mk_bvrem ~size ~signed:(Some true) a (num c) in
                  if Stdlib.(md = Value.Truncated) then
                    Some
                      ( r,
                        ( (if Z.(geq l zero) then Z.zero else Z.neg (Z.pred c)),
                          if Z.(leq h zero) then Z.zero else Z.pred c ) )
                  else
                    let neg =
                      Formula.mk_atom
                        (T_bv.mk_bvlt ~size ~signed:(Some true) r (num Z.zero))
                    in
                    Some
                      ( T_bool.mk_if_then_else (T_bool.of_formula neg)
                          (T_bv.mk_bvadd ~size r (num c))
                          r,
                        (Z.zero, Z.pred c) )
              | None -> None)
          | Term.FunApp (T_irb.BVToInt (_, signed), [ b ], _)
            when not (T_bv.is_signed signed) -> (
              (* the width read off the word's sort: the SMT-LIB reader
                 leaves the conversion's own size unset *)
              match Term.sort_of b with
              | T_bv.SBV (Some m) when m < w ->
                  Some (zext m b, (Z.zero, Z.pred (Z.shift_left Z.one m)))
              | _ -> None)
          | Term.FunApp (T_bool.IfThenElse, [ c; t1; t2 ], _) -> (
              let cond =
                match c with
                | Term.FunApp (T_bool.Formula phi, [], _) -> trf phi
                | _ -> None
              in
              match (cond, tr t1, tr t2) with
              | Some c', Some (a1, (l1, h1)), Some (a2, (l2, h2)) ->
                  Some
                    ( T_bool.mk_if_then_else (T_bool.of_formula c') a1 a2,
                      (Z.min l1 l2, Z.max h1 h2) )
              | _ -> None)
          | t when is_key t && bounded t ->
              Some
                ( zext n (Term.mk_var (name_of t) (T_bv.SBV (Some n))),
                  (Z.zero, Z.pred (Z.shift_left Z.one n)) )
          | _ -> None
        in
        match res with Some (_, iv) when fits iv -> res | _ -> None
      and bin t1 t2 mk iv =
        match (tr t1, tr t2) with
        | Some (a, i1), Some (b, i2) -> Some (mk a b, iv i1 i2)
        | _ -> None
      (* a formula over translated integer comparisons *)
      and trf phi =
        match phi with
        | Formula.Atom ((Atom.True _ | Atom.False _), _) -> Some phi
        | Formula.Atom (atm, _) -> Option.map (tra atm) ~f:Formula.mk_atom
        | Formula.UnaryOp (Formula.Not, p, _) ->
            Option.map (trf p) ~f:Formula.mk_neg
        | Formula.BinaryOp (op, p1, p2, _) -> (
            match (trf p1, trf p2) with
            | Some q1, Some q2 -> Some (Formula.mk_binop op q1 q2)
            | _ -> None)
        | _ -> None
      and tra atm =
        match atm with
        | Atom.App (Predicate.Psym psym, [ t1; t2 ], _) -> (
            let both mk =
              match (tr t1, tr t2) with
              | Some (a, _), Some (b, _) -> Some (mk a b)
              | _ -> None
            in
            let signed = Some true in
            match psym with
            | T_int.Leq -> both (T_bv.mk_bvleq ~size ~signed)
            | T_int.Geq -> both (T_bv.mk_bvgeq ~size ~signed)
            | T_int.Lt -> both (T_bv.mk_bvlt ~size ~signed)
            | T_int.Gt -> both (T_bv.mk_bvgt ~size ~signed)
            | T_bool.Eq when is_int t1 -> both T_bool.mk_eq
            | T_bool.Neq when is_int t1 -> both T_bool.mk_neq
            | (T_bool.Eq | T_bool.Neq) as psym -> (
                (* an equation between Boolean terms: each side read as a
                   formula, the equation as an equivalence *)
                match (trb t1, trb t2) with
                | Some f1, Some f2 ->
                    let iff = Formula.mk_iff f1 f2 in
                    Option.some
                    @@ T_bool.mk_eq (T_bool.of_formula
                         (if Stdlib.(psym = T_bool.Eq) then iff
                          else Formula.mk_neg iff))
                         (T_bool.mk_true ())
                | _ -> None)
            | _ -> None)
        | _ -> None
      (* a Boolean term as a formula over translated comparisons *)
      and trb t =
        match t with
        | Term.FunApp (T_bool.Formula phi, [], _) -> trf phi
        | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _) -> (
            match (trb c, trb a, trb b) with
            | Some c', Some a', Some b' ->
                Some
                  (Formula.or_of
                     [
                       Formula.and_of [ c'; a' ];
                       Formula.and_of [ Formula.mk_neg c'; b' ];
                     ])
            | _ -> None)
        | _ -> None
      in
      (* a literal is twinned where its twin reads a bit-vector variable (a
         key's name or a word), and is not a bound the twin's width already
         implies ([0 <= k], [k < 2^n]) *)
      let reads_word atm' =
        Set.exists (Atom.term_sort_env_of atm') ~f:(function
          | _, T_bv.SBV _ -> true
          | _ -> false)
      in
      let implied lit =
        match bound_of lit with
        | Some (_, `Lo c) -> Z.(leq c zero)
        | Some (_, `Hi c) -> Z.(geq c (shift_left one n))
        | None -> false
      in
      let twins =
        List.filter_map lits ~f:(fun ((pos, atm) as lit) ->
            if implied lit then None
            else
              match tra atm with
              | Some atm' when reads_word atm' ->
                  let a = Formula.mk_atom atm' in
                  Some (if pos then a else Formula.mk_neg a)
              | _ -> None)
      in
      let rewritten = ref false in
      (* an integer condition [phi] stated twice, over the integers and over
         bit-vectors, where it translates: the two are equivalent in every
         model of the conjuncts, so the conjunction is too *)
      let both phi =
        match trf phi with
        | Some phi' when not (Stdlib.( == ) phi phi') ->
            Formula.and_of [ phi; phi' ]
        | _ -> phi
      in
      (* the bounded reads [nth s i] that are keys, by sequence *)
      let key_reads =
        List.filter_map bounds ~f:(function
          | (Term.FunApp (T_seq.SqNth _, [ sq; i ], _) as k), `Lo _
            when bounded k ->
              Some (sq, i, k)
          | _ -> None)
        |> List.dedup_and_sort ~compare:Stdlib.compare
      in
      (* [int_to_bv m t] with [t] translated is the low [m] bits of the
         translation.  Three exact steps let more terms reach that:
         - [int_to_bv m (ite c a b)] is [ite c (int_to_bv m a)
           (int_to_bv m b)];
         - a read of a store [nth (store s i e) j] is
           [ite (0 <= j < len s) (ite (i = j) e (nth s j)) (nth (store s i
           e) j)]: inside [s] the store holds [e] at [i] and [s]'s element
           elsewhere, and outside it the read is the same term, so the two
           sides agree whatever the theory leaves open there;
         - [int_to_bv m (nth s j)] beside a key [nth s i] is
           [ite (j = i) (int_to_bv m (nth s i)) (int_to_bv m (nth s j))], by
           congruence.
         Every condition introduced is stated by [both]. *)
      let rec to_bv m t =
        match t with
        | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _) ->
            let c =
              match c with
              | Term.FunApp (T_bool.Formula phi, [], _) ->
                  T_bool.of_formula (both phi)
              | c -> c
            in
            T_bool.mk_if_then_else c (to_bv m a) (to_bv m b)
        | Term.FunApp
            ( T_seq.SqNth se,
              [ (Term.FunApp (T_seq.SqStore _, [ sq; i; e ], _) as st); j ],
              _ )
          when closed t ->
            rewritten := true;
            let inside =
              Formula.and_of
                [
                  Formula.leq (T_int.zero ()) j;
                  Formula.lt j (T_seq.mk_len se sq);
                ]
            in
            T_bool.mk_if_then_else
              (T_bool.of_formula (both inside))
              (T_bool.mk_if_then_else
                 (T_bool.of_formula (both (Formula.eq i j)))
                 (to_bv m e)
                 (to_bv m (T_seq.mk_nth se sq j)))
              (T_irb.mk_int_to_bv ~size:(Some m) (T_seq.mk_nth se st j))
        | Term.FunApp (T_seq.SqNth _, [ sq; j ], _) when closed t -> (
            let direct = word m t in
            match
              List.filter key_reads ~f:(fun (sq', i, _) ->
                  Stdlib.(sq = sq') && not Stdlib.(i = j))
            with
            | [] -> direct
            | ks ->
                rewritten := true;
                List.fold_right ks ~init:direct ~f:(fun (_, i, k) acc ->
                    T_bool.mk_if_then_else
                      (T_bool.of_formula (both (Formula.eq j i)))
                      (word m k) acc))
        | t -> word m t
      and word m t =
        match tr t with
        | Some (t', _) ->
            rewritten := true;
            T_bv.mk_bvextract ~size (m - 1) 0 t'
        | None -> T_irb.mk_int_to_bv ~size:(Some m) t
      in
      (* the tightest bounds the top-level conjuncts give each key *)
      let lo k =
        List.fold bounds ~init:None ~f:(fun acc -> function
          | k', `Lo c when Stdlib.(k = k') ->
              Some (Option.value_map acc ~default:c ~f:(Z.max c))
          | _ -> acc)
      in
      let hi k =
        List.fold bounds ~init:None ~f:(fun acc -> function
          | k', `Hi c when Stdlib.(k = k') ->
              Some (Option.value_map acc ~default:c ~f:(Z.min c))
          | _ -> acc)
      in
      (* [Some b] when a single-key bound [atm] is decided by those bounds:
         the top-level conjuncts hold in every model of the question, so the
         atom has that value in each *)
      let decided atm =
        match bound_of (true, atm) with
        | Some (k, `Lo c) -> (
            (* atm is [c <= k] *)
            match (lo k, hi k) with
            | Some l, _ when Z.geq l c -> Some true
            | _, Some h when Z.leq h c -> Some false
            | _ -> None)
        | Some (k, `Hi c) -> (
            (* atm is [k < c] *)
            match (lo k, hi k) with
            | _, Some h when Z.leq h c -> Some true
            | Some l, _ when Z.geq l c -> Some false
            | _ -> None)
        | None -> None
      in
      let closed_atom atm =
        Set.is_empty (Set.inter (Atom.tvs_of atm) bound_names)
      in
      (* the value of a condition built from such atoms, when they decide it *)
      let rec truth phi =
        match phi with
        | Formula.Atom (Atom.True _, _) -> Some true
        | Formula.Atom (Atom.False _, _) -> Some false
        | Formula.Atom (atm, _) when closed_atom atm -> decided atm
        | Formula.UnaryOp (Formula.Not, p, _) -> Option.map (truth p) ~f:not
        | Formula.BinaryOp (Formula.And, p1, p2, _) -> (
            match (truth p1, truth p2) with
            | Some false, _ | _, Some false -> Some false
            | Some true, Some true -> Some true
            | _ -> None)
        | Formula.BinaryOp (Formula.Or, p1, p2, _) -> (
            match (truth p1, truth p2) with
            | Some true, _ | _, Some true -> Some true
            | Some false, Some false -> Some false
            | _ -> None)
        | _ -> None
      in
      (* an [ite] whose condition those bounds decide is its branch: exact,
         and it takes the negative-operand branches the reader writes for a
         truncated [div] and [mod] out of a question about words *)
      let decide_ites =
        Formula.map_term ~f:(function
          | Term.FunApp
              (T_bool.IfThenElse, [ Term.FunApp (T_bool.Formula c, [], _); a; b ], _)
            as t -> (
              match truth c with
              | Some true ->
                  rewritten := true;
                  a
              | Some false ->
                  rewritten := true;
                  b
              | None -> t)
          | t -> t)
      in
      let rewrite =
        Formula.map_term ~f:(function
          | Term.FunApp (T_irb.IntToBV (Some m), [ t ], _) when m <= w ->
              to_bv m t
          | t -> t)
      in
      (* the integer terms read as words: [t] of every [int_to_bv m t], with
         its width *)
      let read_as_word =
        List.fold phis ~init:Map.Poly.empty ~f:(fun acc phi ->
            Set.fold
              (Formula.filtered_terms_of phi ~f:(function
                | Term.FunApp (T_irb.IntToBV (Some _), [ t ], _) -> closed t
                | _ -> false))
              ~init:acc
              ~f:(fun acc -> function
                | Term.FunApp (T_irb.IntToBV (Some m), [ t ], _) when m <= w ->
                    Map.Poly.set acc ~key:t ~data:m
                | _ -> acc))
      in
      (* an integer term as [sum a_r r + c] over any non-arithmetic subterms
         [r] (reads, selectors, variables) *)
      let rec linr t =
        match t with
        | Term.FunApp (T_int.Int c, [], _) -> Some (Map.Poly.empty, c)
        | Term.FunApp (T_int.Add, [ t1; t2 ], _) -> combr Z.one t1 Z.one t2
        | Term.FunApp (T_int.Sub, [ t1; t2 ], _) ->
            combr Z.one t1 Z.minus_one t2
        | Term.FunApp (T_int.Neg, [ t1 ], _) ->
            Option.map (linr t1) ~f:(fun (m, c) ->
                (Map.Poly.map m ~f:Z.neg, Z.neg c))
        | Term.FunApp (T_int.Mul, [ Term.FunApp (T_int.Int a, [], _); t1 ], _)
        | Term.FunApp (T_int.Mul, [ t1; Term.FunApp (T_int.Int a, [], _) ], _)
          ->
            Option.map (linr t1) ~f:(fun (m, c) ->
                (Map.Poly.map m ~f:(Z.mul a), Z.mul a c))
        | Term.Var _ | Term.FunApp _ -> Some (Map.Poly.singleton t Z.one, Z.zero)
        | _ -> None
      and combr a1 t1 a2 t2 =
        match (linr t1, linr t2) with
        | Some (m1, c1), Some (m2, c2) ->
            let scale a m = Map.Poly.map m ~f:(Z.mul a) in
            Some
              ( Map.Poly.merge (scale a1 m1) (scale a2 m2) ~f:(fun ~key:_ ->
                  function
                  | `Left a | `Right a -> Some a
                  | `Both (a, b) -> Some (Z.add a b)),
                Z.(add (mul a1 c1) (mul a2 c2)) )
        | _ -> None
      in
      (* An integer equation [t1 = t2] that solves for a term [r] read as a
         word ([r = e], coefficient one) is [t1 = t2 /\ int_to_bv m r =
         int_to_bv m e], by congruence, and [t1 != t2] is [t1 != t2 \/ not
         (int_to_bv m r = int_to_bv m e)], the negation of that:
         the words of equal integers are equal.  An equivalence in every
         model, applied to every closed equation outside a binder. *)
      let word_eq atm =
        match atm with
        | Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [ t1; t2 ], _)
          when is_int t1 && Set.is_empty (Set.inter (Atom.tvs_of atm) bound_names)
          -> (
            match combr Z.one t1 Z.minus_one t2 with
            | None -> None
            | Some (m, c) ->
                List.find_map (Map.Poly.to_alist m) ~f:(fun (r, a) ->
                    match Map.Poly.find read_as_word r with
                    | Some width when Z.equal (Z.abs a) Z.one ->
                        (* r = -(rest + c) / a *)
                        let rest =
                          Map.Poly.fold m ~init:(T_int.mk_int c)
                            ~f:(fun ~key:k ~data:b acc ->
                              if Stdlib.(k = r) then acc
                              else T_int.mk_add acc (T_int.mk_mul (T_int.mk_int b) k))
                        in
                        let e =
                          if Z.(gt a zero) then T_int.mk_neg rest else rest
                        in
                        if Option.is_none (tr e) then None
                        else
                          Some
                            (Formula.eq (to_bv width r) (to_bv width e))
                    | _ -> None))
        | _ -> None
      in
      let rec with_word_eqs phi =
        match phi with
        | Formula.Atom (atm, _) -> (
            match word_eq atm with
            | Some e -> (
                rewritten := true;
                match atm with
                | Atom.App (Predicate.Psym T_bool.Neq, _, _) ->
                    (* [t1 != t2] is the negation of [t1 = t2 /\ e] *)
                    Formula.or_of [ phi; Formula.mk_neg e ]
                | _ -> Formula.and_of [ phi; e ])
            | None -> (
                match atm with
                | Atom.App
                    ( Predicate.Psym ((T_bool.Eq | T_bool.Neq) as psym),
                      [ Term.FunApp (T_bool.Formula p, [], _); c ],
                      _ )
                  when T_bool.is_true c || T_bool.is_false c ->
                    let p' = with_word_eqs p in
                    if phys_equal p p' then phi
                    else
                      Formula.mk_atom
                        (Atom.mk_psym_app psym
                           [ T_bool.of_formula p'; c ])
                | _ -> phi))
        | Formula.UnaryOp (op, p, _) ->
            let p' = with_word_eqs p in
            if phys_equal p p' then phi else Formula.mk_unop op p'
        | Formula.BinaryOp (op, p1, p2, _) ->
            let p1' = with_word_eqs p1 and p2' = with_word_eqs p2 in
            if phys_equal p1 p1' && phys_equal p2 p2' then phi
            else Formula.mk_binop op p1' p2'
        | _ -> phi
      in
      let phis' =
        List.map phis ~f:(fun phi -> rewrite (with_word_eqs (decide_ites phi)))
      in
      (* a twin's words are rewritten too, so that it reads keys by their
         names *)
      let twins = List.map twins ~f:(fun phi -> rewrite (decide_ites phi)) in
      (* With [generalize], every word still read as [int_to_bv m t] of an
         integer term (one no key translates) becomes a fresh bit-vector, one
         per term: the question then forgets [w = int_to_bv m t], so it has
         more models, and its [unsat] -- the only answer a caller of this
         form may read -- is one of the question's *)
      let general = Hashtbl.Poly.create () in
      let phis' =
        if not generalize then phis'
        else
          List.map phis'
            ~f:
              (Formula.map_term ~f:(function
                | Term.FunApp (T_irb.IntToBV (Some m), [ t ], _) when closed t ->
                    Term.mk_var
                      (Hashtbl.find_or_add general (m, t) ~default:(fun () ->
                           Ident.mk_fresh_tvar ~prefix:(Some "bvw") ()))
                      (T_bv.SBV (Some m))
                | t -> t))
      in
      if List.is_empty twins && (not !rewritten) && Hashtbl.is_empty general
      then (phis, [])
      else
        let links =
          Hashtbl.fold names ~init:[] ~f:(fun ~key:k ~data:kb acc ->
              Formula.eq k
                (T_irb.mk_bv_to_int ~size:(Some n) ~signed:(Some false)
                   (Term.mk_var kb (T_bv.SBV (Some n))))
              :: acc)
        in
        (phis' @ links @ twins, Hashtbl.data names @ Hashtbl.data general)

let int_to_bv_range_subst phis =
  let phis, bounded = int_to_bv_bounded_subst phis in
  let phis, split = int_to_bv_split_subst phis in
  (* a twin's name stands for no variable of the question: its entry names it
     twice, which [int_to_bv_range_model] reads as "drop it" *)
  let phis, twins =
    if Atomic.get int_to_bv_twins then int_to_bv_twins_subst phis
    else (phis, [])
  in
  ( phis,
    List.map bounded ~f:(fun (x, xb, n) -> (x, xb, n, None))
    @ split
    @ List.map twins ~f:(fun kb -> (kb, kb, 0, None)) )

(* [int_to_bv_range_subst] with the twins and the generalisation of the
   words no key translates ([int_to_bv_twins_subst ~generalize:true]),
   whatever the switches; [None] when the twins step changes nothing.  The
   result is weaker than the question (it may have more models), so only its
   [unsat] may be read, as the question's [unsat]. *)
let int_to_bv_words_subst phis =
  let phis, bounded = int_to_bv_bounded_subst phis in
  let phis, split = int_to_bv_split_subst phis in
  match int_to_bv_twins_subst ~generalize:true phis with
  | _, [] -> None
  | phis, fresh ->
      Some
        ( phis,
          List.map bounded ~f:(fun (x, xb, n) -> (x, xb, n, None))
          @ split
          @ List.map fresh ~f:(fun kb -> (kb, kb, 0, None)) )

let int_to_bv_range_model picked model =
  if List.is_empty picked then model
  else
    let fresh =
      Set.Poly.of_list
      @@ List.concat_map picked ~f:(fun (_, xb, _, q) ->
             xb :: Option.to_list q)
    in
    let find z =
      List.find_map model ~f:(fun ((y, _), v) ->
          if Ident.tvar_equal y z then v else None)
    in
    let value_of xb n q =
      match find xb with
      | Some (Term.FunApp (T_bv.BVNum (_, z), [], _)) -> (
          let low = Z.erem z (Z.shift_left Z.one n) in
          match q with
          | None -> Some (T_int.mk_int low)
          | Some q -> (
              match find q with
              | Some (Term.FunApp (T_int.Int k, [], _)) ->
                  Some (T_int.mk_int Z.(add (mul (shift_left one n) k) low))
              | _ -> Some (T_int.mk_int low)))
      | _ -> None
    in
    List.filter model ~f:(fun ((y, _), _) -> not (Set.mem fresh y))
    @ List.filter_map picked ~f:(fun (x, xb, n, q) ->
          if Ident.tvar_equal x xb then None
          else Some ((x, T_int.SInt), value_of xb n q))

(* Called by [check_sat_base] with the context and the solver each query is
   checked in, just before the check.  Does nothing unless a test sets it: a property check
   reads through it whether two asks went to the same solver. *)
let query_solver_hook : (Z3.context -> Z3.Solver.solver -> unit) ref =
  ref (fun _ _ -> ())

(* Called by [check_sat_base] with [fresh_solver] and the formulas it is about
   to convert to Z3 (after the definitions are inlined and, for a context of
   the question's own, after negation normal form).  Does nothing unless a
   test sets it: a property check reads through it that a question asked in a
   context of its own reaches the solver in negation normal form. *)
let z3_input_hook : (bool -> Formula.t list -> unit) ref = ref (fun _ _ -> ())

(* With [COAR_Z3_ID_LOG=path] in the environment, every check of
   [check_sat_base] appends one line to [path]: the process, whether the
   question was asked in a context of its own, whether it is quantified, the
   largest Z3 identifier among the asserted expressions' subterms, the
   question's size, the process's resident memory before and after the check
   (KB), the seconds, the outcome and Z3's own memory figure after the check
   (MB, all contexts together).  A diagnostic: the identifiers a context has
   reached and the memory Z3 holds say what a context's history costs a
   question asked in it (Z3's sequence theory, for one, keeps maps indexed by
   expression identifier).  Without the variable nothing is written.  Read
   once at start-up, so that no solver domain forces it for the first time. *)
let z3_id_log_path = Sys.getenv "COAR_Z3_ID_LOG"

(* the resident memory of this process in KB (pages of 4 KB), -1 when it
   cannot be read *)
let resident_kb () =
  match In_channel.read_all "/proc/self/statm" |> String.split ~on:' ' with
  | _ :: rss :: _ -> (
      match Int.of_string_opt rss with Some pages -> pages * 4 | None -> -1)
  | _ -> -1
  | exception exn_ when not (Common.Timer.is_async exn_) -> -1

(* the largest Z3 identifier among the subterms of [es] (shared nodes and
   quantifier bodies visited once each) *)
let max_subterm_id es =
  let seen = Hash_set.create (module Int) in
  let best = ref (-1) in
  let rec walk e =
    let ast = Z3.Expr.ast_of_expr e in
    let id = Z3.AST.get_id ast in
    if not (Hash_set.mem seen id) then (
      Hash_set.add seen id;
      best := Int.max !best id;
      if Z3.AST.is_var ast then ()
      else if Z3.AST.is_quantifier ast then
        walk @@ Z3.Quantifier.get_body @@ Z3.Quantifier.quantifier_of_expr e
      else if Stdlib.(Z3.AST.get_ast_kind ast = Z3enums.APP_AST) then
        List.iter (Z3.Expr.get_args e) ~f:walk)
  in
  List.iter es ~f:walk;
  !best

(* Keep the explicit Boolean-equation API contract separate from the broader
   file-context admission and Horn export family below. *)
let supports_boolean_equations (fenv : FunEnv.t) =
  (not (Map.Poly.is_empty fenv))
  && List.for_all (Map.Poly.data fenv) ~f:(fun (params, sret, _, _, property) ->
      Term.is_bool_sort sret
      && List.for_all params ~f:(snd >> Term.is_bool_sort)
      && Formula.is_true property)

(* Refutation may use eligible entries even when a sibling is unsupported.
   All signatures are retained; this makes no full-model certificate. *)
let supports_defining_equation_instances (fenv : FunEnv.t) =
  let supported s = Term.is_bool_sort s || Term.is_int_sort s in
  List.exists (Map.Poly.data fenv) ~f:(fun (params, sret, _, _, property) ->
      supported sret
      && List.for_all params ~f:(snd >> supported)
      && Formula.is_true property)

(* Integer entries must not disable the Boolean context defense, which states
   every defining equation because Z3 constrains a native recursive definition
   only where a query applies it. Keep automatic/explicit admission bounded to
   signatures with true properties and known calls preserving integer argument
   positions: a recurrence that changes its arguments can leave a satisfiable
   equation query undecided, as a recursive probe did even in native Z3. This
   conservative guard is not a termination proof or decision procedure. *)
let supports_defining_equations (fenv : FunEnv.t) =
  let preserves_integer_arguments params body =
    let body = if Term.is_let_free body then body else Term.elim_let body in
    Set.for_all (Term.fvar_apps_of body) ~f:(function
      | FunApp (FVar (var, sorts, _), args, _) when Map.Poly.mem fenv var ->
          List.for_all (List.mapi args ~f:(fun i arg -> (i, arg)))
            ~f:(fun (i, arg) ->
              if not (Term.is_int_sort (List.nth_exn sorts i)) then true
              else
                match (List.nth params i, arg) with
                | Some (formal, sort), Var (actual, actual_sort, _) ->
                    Term.is_int_sort sort
                    && Poly.(formal = actual && sort = actual_sort)
                | _ -> false)
      | _ -> true)
  in
  let supported s = Term.is_bool_sort s || Term.is_int_sort s in
  (not (Map.Poly.is_empty fenv))
  && List.for_all (Map.Poly.data fenv) ~f:(fun (params, sret, _, _, property) ->
      supported sret
      && List.for_all params ~f:(snd >> supported)
      && Formula.is_true property)
  && List.for_all (Map.Poly.data fenv) ~f:(fun (params, _, body, _, _) ->
      preserves_integer_arguments params body)

let defining_equations_of (fenv : FunEnv.t) =
  List.map (Map.Poly.to_alist fenv) ~f:(fun (var, (params, sret, body, _, _)) ->
      let lhs =
        Term.mk_fsym_app
          (FVar (var, List.map params ~f:snd, sret))
          (Term.of_sort_env params)
      in
      let body = if Term.is_let_free body then body else Term.elim_let body in
      Formula.mk_forall_if_bounded params (Formula.eq lhs body))

(* Instantiate integer formals at zero and retain universal Boolean formals.
   Inner binders and definition-site globals retain their scopes. These are
   necessary defining equalities, not a total function-model certificate. *)
let defining_equation_instances_of (fenv : FunEnv.t) =
  if not (supports_defining_equation_instances fenv) then
    invalid_arg "Defining equation instances require at least one eligible entry";
  Map.Poly.to_alist fenv
  |> List.filter ~f:(fun (var, entry) ->
         supports_defining_equation_instances (Map.Poly.singleton var entry))
  |> List.map ~f:(fun (var, (params, sret, body, _, _)) ->
      let args =
        List.map params ~f:(fun (formal, sort) ->
            if Term.is_int_sort sort then T_int.from_int 0
            else Term.mk_var formal sort)
      in
      let sub =
        Map.Poly.of_alist_exn
          (List.filter_map params ~f:(fun (formal, sort) ->
               if Term.is_int_sort sort then Some (formal, T_int.from_int 0)
               else None))
      in
      let lhs =
        Term.mk_fsym_app (FVar (var, List.map params ~f:snd, sret)) args
      in
      let body = if Term.is_let_free body then body else Term.elim_let body in
      Formula.mk_forall_if_bounded
        (List.filter params ~f:(fun (_, sort) -> Term.is_bool_sort sort))
        (Formula.eq lhs (Term.subst sub body)))

let boolean_defining_equations = defining_equations_of

let check_sat_base =
  let cfg = [ ("model", "true") ] in
  let cfg = if validate then cfg @ validate_cfg else cfg in
  fun ?(timeout = None)
    ?(fresh_solver = false)
    ?(scoped = false)
    ?(boolean_equations = false)
    ?(defining_equations = false)
    ?(defining_equation_instances = false)
    ?fun_values_out
    ?pre
    ~id
    fenv
    phis
  ->
    if
      boolean_equations
      && ((not fresh_solver) || not (supports_boolean_equations fenv))
    then
      invalid_arg
        "Boolean equations require supported definitions and a fresh solver";
    if
      defining_equations
      && ((not fresh_solver) || not (supports_defining_equations fenv))
    then
      invalid_arg
        "Defining equations require supported definitions and a fresh solver";
    let full_equations = boolean_equations || defining_equations in
    if
      defining_equation_instances
      && (full_equations || not fresh_solver
         || not (supports_defining_equation_instances fenv))
    then
      invalid_arg
        "Defining equation instances require a fresh solver and their own mode";
    let ordinary_definitions = full_equations || defining_equation_instances in
    (* the array-literal equality this solver does not decide is rewritten
       before anything else looks at the query, so that every caller of this
       entry point is covered rather than whichever one was being debugged *)
    let phis =
      Common.PhaseTime.with_phase "expand" (fun () ->
          List.map phis ~f:expand_finite_array_eqs)
    in
    (* [pre] is the question already rewritten by [int_to_bv_range_subst]
       with what it picked ([check_sat] below) *)
    let phis, bv_ranged =
      match pre with
      | Some (phis', picked) ->
          (List.map phis' ~f:expand_finite_array_eqs, picked)
      | None -> (phis, [])
    in
    (* Defining equations constrain even symbols that no assertion calls.
       Retain the full environment before any optional reachability slicing. *)
    let fenv = if ordinary_definitions then fenv else fenv_for_query fenv phis in
    let phis =
      if defining_equation_instances then
        defining_equation_instances_of fenv @ phis
      else if full_equations then defining_equations_of fenv @ phis
      else phis
    in
    (* [fresh_solver] asks in a context made for this query alone, never
       taken from the pool nor returned to it.  Z3 (4.15.2) answers a
       quantified goal with the bare [smt] tactic -- "smt tactic failed ...
       (incomplete quantifiers)" -- and skips its default preprocessing, the
       elimination of unconstrained terms among it, in each of three
       situations:
       - the context holds a recursive function definition, whether or not the
         goal uses it;
       - some solver of the context has EVER been in a scope: a later [reset]
         of that solver does not undo it, nor does making a new solver in the
         same context;
       - the goal is written [not (exists ...)] rather than in negation normal
         form.
       Measured on a goal over arrays and a tuple datatype that is answered
       [sat] only with that preprocessing: each of the three alone was enough
       to turn the answer into [unknown].  The scope condition is Z3's
       documented design: its default solver is a combination of a
       non-incremental tactic, which preprocesses, and the incremental [smt]
       core, and it switches to the core for good once [push] is used or an
       assertion follows a [check-sat]; on [unknown] from the core it falls back
       to the tactic only for a quantifier-free goal.  Forcing that fallback
       ([combined_solver.solver2_unknown 2]) does not recover the answer: the
       tactic then also fails with "incomplete quantifiers", after a push and
       with an unused recursive definition alike, for a reason not established.
       The pooled instances are
       pushed routinely and carry every registered definition, so a pooled
       quantified query never gets the default preprocessing; a caller that
       needs it passes [~fresh_solver:true], asserts only the definitions its
       goal reaches, and puts the goal in negation normal form. *)
    let arith_solver = Stdlib.Domain.DLS.get arith_solver_key in
    (* charged as "instance": a new context is preceded by a forced full major
       collection, whose cost grows with the live heap and with the machine's
       load, and which is not part of the solver's check *)
    let instance =
      Common.PhaseTime.with_phase "instance" @@ fun () ->
      if fresh_solver then lease_clean_instance ~arith:arith_solver id cfg
      else get_instance id cfg (pool_of_arith_solver arith_solver)
    in
    print_query_sorts ~id phis;
    let ctx, solver = (instance.ctx, instance.solver) in
    Common.PhaseTime.with_phase "dtenv" (fun () ->
    instance.dtenv <-
      z3_dtenv_of_formula ~init:instance.dtenv ctx @@ Formula.and_of phis);
    Common.PhaseTime.with_phase "fenv" (fun () ->
        instance.fenv <-
          (if ordinary_definitions then
             (* Native recursive declarations plus explicit equations still return
           wrong sat on contradictory mutual recursion in Z3 5.1.0. Declare
           every signature ordinarily before converting any equation body.
           The nonempty fenv also keeps this context out of the clean pool. *)
             Map.Poly.mapi fenv
               ~f:(fun ~key:var ~data:(params, sret, _, _, _) ->
                 Z3.FuncDecl.mk_func_decl_s ctx (Ident.name_of_tvar var)
                   (List.map params ~f:(snd >> of_sort ctx instance.dtenv))
                   (of_sort ctx instance.dtenv sret))
           else z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv instance.dtenv));
    debug_print_z3_input phis;
    (* A question asked in a context of its own is put in negation normal form
       after its definitions are inlined, whatever its caller did: such a
       context runs Z3's default strategy, and a negated quantifier or an
       implication over one ([not (exists ...)]) leaves Z3 answering with the
       bare [smt] tactic, without that strategy's preprocessing (see
       [fresh_solver] above).  [defined_formula_of] already does this when the
       question reaches a defined function, but not otherwise, and
       [check_valid] negates a universal question into exactly that shape.
       Negation normal form is an equivalence, so the question is the same.
       Not reached: a formula embedded in a term ([T_bool.Formula]) and the
       two sides of an [iff] or [xor] keep their own shape. *)
    let phis =
      Common.PhaseTime.with_phase "defined" (fun () ->
          List.map phis ~f:(fun phi ->
              (* Selected instances omit other equations/properties. Keep the
                 original constraints literal instead of adding properties of
                 skipped entries through the generic query rewrite. *)
              let phi =
                if defining_equation_instances then phi
                else FunEnv.defined_formula_of fenv phi
              in
              if fresh_solver then Formula.nnf_of phi else phi))
    in
    !z3_input_hook fresh_solver phis;
    debug_print_z3_input phis;
    let phis' =
      Common.PhaseTime.with_phase "to-z3" (fun () ->
      List.map phis
        ~f:(of_formula_with_z3fenv ~id ctx [] [] instance.fenv instance.dtenv))
    in
    (* Empty parameter sets do not clear a pooled solver's previous timeout.
       The rlimit is set only when one is asked for ([with_rlimit]), and put
       back to 0 (no limit) afterwards, so a query asked without one sets
       exactly the parameters it set before the option existed. *)
    let rlimit = Stdlib.Domain.DLS.get rlimit_key in
    let set_timeout ?rlimit milliseconds =
      let params = Z3.Params.mk_params ctx in
      Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") milliseconds;
      Option.iter rlimit ~f:(fun r ->
          Z3.Params.add_int params (Z3.Symbol.mk_string ctx "rlimit") r);
      add_arith_solver_param ctx params arith_solver;
      Z3.Solver.set_parameters solver params
    in
    set_timeout ?rlimit (Option.value timeout ~default:0);
    (* One query per scope.  The pooled solver used to be [reset] after every
       query, and the reset was a quarter of the wrapper's time (2.7 s of 28 s
       over 10,561 calls; the wrapper being everything but the conversion and
       the Z3 call); a [pop] of the scope the query was pushed in is cheaper
       and leaves the solver in incremental mode.  Both clean-ups now also run
       when the query raises -- a timeout arriving as an exception in the
       middle of the Z3 call used to skip the reset, leaving the query's
       assertions in the pooled solver for the next caller of the same instance
       to conjoin with its own. *)
    (* A scope is cheap, and for a QUANTIFIED query it is also the wrong place
       to assert: [forall x. exists y. y > x] is answered sat in 0.03 s by z3 on
       a fresh solver and comes back "unknown (incomplete quantifiers)" after
       two seconds when the same assertion is made inside a push -- and through
       this wrapper it did not answer at all.  So a query carrying a quantifier
       is asserted on a solver with no open scope and the solver is reset
       afterwards, while everything else keeps the scope whose cheapness was
       measured over ten thousand calls.  What the reset does NOT do is give
       the query the strategies of a fresh solver: once any solver of a context
       has been in a scope, Z3 keeps answering quantified goals in that context
       with the bare [smt] tactic and without its default preprocessing, after
       a reset and on a newly made solver alike (see [fresh_solver] above for
       that and the two other conditions with the same effect).  The pooled
       instances have all been pushed, so the reset only keeps the query out of
       a scope.  Both paths clean up when the query raises: a timeout arriving
       as an exception in the middle of the Z3 call used to skip the clean-up,
       leaving the query's assertions in the pooled solver for the next caller
       of the same instance to conjoin with its own. *)
    (* [scoped]: a quantified query on a pooled solver is asserted inside a
       scope like a quantifier-free one, so that Z3 answers it with its
       incremental core rather than with the bare [smt] tactic the unscoped
       path gets in a context that has been pushed.  Neither strategy decides
       a superset of the other's questions: the core decided in 0.1 s
       validation questions over sequences and datatypes on which the tactic
       ran out of a 5 s budget, while the [forall x. exists y. y > x] above
       goes the other way.  The question and the reading of its answer are
       the same; only which questions are decided in time differs.  Ignored
       with [fresh_solver]. *)
    let quantified =
      List.exists phis ~f:(fun phi -> Formula.number_of_quantifiers phi > 0)
    in
    let unscoped = quantified && not scoped in
    if fresh_solver then ()
    else if unscoped then z3_solver_reset solver
    else Z3.Solver.push solver;
    let finally ~raised =
      (if fresh_solver then ()
       else if unscoped then z3_solver_reset solver
       else try Z3.Solver.pop solver 1 with _ -> z3_solver_reset solver);
      set_timeout ?rlimit:(Option.map rlimit ~f:(fun _ -> 0)) 0;
      if fresh_solver then
        (* a context of this question's own: returned to the clean pool only
           when it is on, the question did not raise and declared no
           recursive function (see [lease_clean_instance]) *)
        release_clean_instance ~arith:arith_solver ~reusable:(not raised) id
          instance
      else
        back_instance ~reset:ignore
          (pool_of_arith_solver arith_solver)
          id instance
    in
    !query_solver_hook ctx solver;
    let log_check =
      match Stdlib.Domain.DLS.get rlimit_label_key with
      | None -> fun _ -> ()
      | Some label ->
          let before = rlimit_count_of solver in
          let t0 = Core_unix.gettimeofday () in
          fun outcome ->
            let after = rlimit_count_of solver in
            rlimit_log_line
              (sprintf "CHECK\t%d\t%s\t%s\t%.3f\t%s\t%d\t%d\t%b\t%b"
                 (Core_unix.getpid () |> Pid.to_int)
                 label
                 (match (before, after) with
                 | Some b, Some a -> sprintf "%.0f" (a -. b)
                 | _ -> "na")
                 (Core_unix.gettimeofday () -. t0)
                 outcome
                 (Option.value timeout ~default:0)
                 (List.sum (module Int) phis ~f:Formula.ast_size)
                 quantified fresh_solver)
    in
    let log_ids =
      match z3_id_log_path with
      | None -> fun _ -> ()
      | Some path ->
          let max_id = max_subterm_id phis' in
          let rss0 = resident_kb () and t0 = Core_unix.gettimeofday () in
          fun outcome ->
            let z3_mb =
              match
                Z3.Statistics.get (Z3.Solver.get_statistics solver) "memory"
              with
              | Some e -> Z3.Statistics.Entry.to_string_value e
              | None -> "na"
              | exception exn_ when not (Common.Timer.is_async exn_) -> "na"
            in
            let line =
              sprintf "%d\t%b\t%b\t%d\t%d\t%d\t%d\t%.3f\t%s\t%s\n"
                (Core_unix.getpid () |> Pid.to_int)
                fresh_solver quantified max_id
                (List.sum (module Int) phis ~f:Formula.ast_size)
                rss0 (resident_kb ())
                (Core_unix.gettimeofday () -. t0)
                outcome z3_mb
            in
            Out_channel.with_file path ~append:true ~f:(fun oc ->
                Out_channel.output_string oc line)
    in
    match check_sat_z3 ?fun_values_out ctx solver instance.dtenv phis' with
    | ret -> (
        log_ids
          (match ret with
          | `Sat _ -> "sat"
          | `Unsat -> "unsat"
          | `Unknown _ -> "unknown"
          | `Timeout -> "timeout");
        log_check
          (match ret with
          | `Sat _ -> "sat"
          | `Unsat -> "unsat"
          | `Unknown reason -> "unknown:" ^ String.tr ~target:'\t' ~replacement:' ' reason
          | `Timeout -> "timeout");
        finally ~raised:false;
        match ret with
        | `Sat model ->
            `Sat
              (int_to_bv_range_model bv_ranged
                 (restrict_model_to_query phis model))
        | `Unknown reason
          when Option.is_some rlimit && rlimit_exhausted_reason reason ->
            `Timeout
        | ret -> ret)
    | exception e ->
        log_ids "raised";
        log_check ("raised:" ^ Exn.to_string e |> String.tr ~target:'\t' ~replacement:' ' |> fun s -> String.prefix s 60);
        finally ~raised:true;
        raise e

(* A bounded necessary-context check for the file-level entry points only.
   Unsat of instances together with original constraints refutes the full
   defining context and those constraints. Sat/unknown/timeout or
   a synchronous encoding refusal supply no certificate and leave the caller
   on its existing route. Never register native recursive definitions here. *)
let refutes_defining_context_by_instances ?(phis = []) ~id fenv =
  if not (supports_defining_equation_instances fenv) then false
  else
    try
      match
        check_sat_base ~timeout:(Some 1000) ~fresh_solver:true
          ~defining_equation_instances:true ~id fenv phis
      with
      | `Unsat -> true
      | `Sat _ | `Unknown _ | `Timeout -> false
    with exn when not (Common.Timer.is_async exn) -> false

(* A candidate is only a search heuristic. Its defining equalities must hold
   for all formals under the substituted constraints before their models can
   witness the original context. Failure supplies no certificate. *)
let defining_context_projection_model ~id fenv phis =
  if Map.Poly.is_empty fenv then None
  else
    try
      let entries = Map.Poly.to_alist fenv in
      if not (List.for_all entries ~f:(fun (_, (_, _, _, _, property)) ->
                  Formula.is_true property)) then None
      else
        let seeds =
          Map.Poly.of_alist_exn
            (List.map entries ~f:(fun (var, (params, sret, _, _, _)) ->
                 let seed =
                   match List.find params ~f:(fun (_, sort) -> Poly.(sort = sret)) with
                   | Some (formal, sort) -> Term.mk_var formal sort
                   | None when Term.is_int_sort sret -> T_int.from_int 0
                   | None when Term.is_bool_sort sret -> T_bool.make false
                   | None -> raise (Invalid_argument "No projection seed for result sort")
                 in
                 (var, (params, seed))))
        in
        let candidates =
          Map.Poly.of_alist_exn
            (List.map entries ~f:(fun (var, (params, _, body, _, _)) ->
                 let body = if Term.is_let_free body then body else Term.elim_let body in
                 (var, (params, Term.subst_funcs seeds body))))
        in
        let contains_known body =
          Set.exists (Term.fvar_apps_of body) ~f:(function
            | FunApp (FVar (var, _, _), _, _) -> Map.Poly.mem fenv var
            | _ -> false)
        in
        let globals = Set.Poly.union_list
            (List.map (Map.Poly.data candidates) ~f:(fun (params, body) ->
                 Set.diff (Term.fvs_of body) (Set.Poly.of_list (List.map params ~f:fst)))) in
        let has_lambda body =
          not (Set.is_empty (Term.filtered_terms_of body ~f:T_array.is_lambda)) in
        let unsafe_scope =
          List.exists entries ~f:(fun (_, (_, _, body, _, _)) -> has_lambda body)
          || List.exists phis ~f:(fun phi ->
                 not (Set.is_empty (Formula.filtered_terms_of phi ~f:T_array.is_lambda)))
          || (not (Set.is_empty globals)
              && (List.exists entries ~f:(fun (_, (params, _, body, _, _)) ->
                      not (Term.is_quantifier_free body)
                      || List.exists params ~f:(fun (var, _) -> Set.mem globals var))
                  || List.exists phis ~f:(fun phi ->
                         not (Formula.is_quantifier_free phi)
                         || not (Formula.is_let_free phi))))
        in
        if unsafe_scope
           || List.exists (Map.Poly.data candidates) ~f:(fun (_, body) -> contains_known body)
        then None
        else
          let equations =
            List.map entries ~f:(fun (var, (params, _, body, _, _)) ->
                let candidate = snd (Map.Poly.find_exn candidates var) in
                let body = if Term.is_let_free body then body else Term.elim_let body in
                Formula.mk_forall_if_bounded params
                  (Formula.eq candidate (Term.subst_funcs candidates body)))
          in
          let phis = List.map phis ~f:(Formula.subst_funcs candidates) in
          let valid =
            List.for_all equations ~f:(fun equation ->
                match check_sat_base ~timeout:(Some 1000) ~fresh_solver:true
                        ~id (FunEnv.mk_empty ()) (Formula.mk_neg equation :: phis) with
                | `Unsat -> true
                | _ -> false)
          in
          if not valid then None
          else
            match check_sat_base ~timeout:(Some 1000) ~fresh_solver:true
                    ~id (FunEnv.mk_empty ()) phis with
            | `Sat model -> Some model
            | _ -> None
    with exn when not (Common.Timer.is_async exn) -> None

(* Total definitions supply a background model for validity-based pCSP solving.
   Recognise generated sizes by their complete factory entries and finite
   datatype dependencies, never by names. Other definitions must be acyclic
   or have every call decrease a natural-valued integer rank under its guards.
   Array lambdas are excluded: an arbitrary array-theory carrier need not
   contain the function they denote. *)
let has_total_defining_context ~id fenv =
  try
    let generated =
      Map.Poly.data (get_dtenv ())
      |> List.filter ~f:(fun dt ->
             Datatype.is_dt dt && not (Datatype.is_poly dt)
             && Set.for_all (fst (Datatype.used_dt_and_sorts_of dt))
                  ~f:Datatype.is_dt)
      |> List.map ~f:Datatype.size_fun_of
      |> Map.Poly.of_alist_exn
    in
    let recognised = Map.Poly.filteri fenv ~f:(fun ~key ~data ->
        match Map.Poly.find generated key with
        | Some expected -> Poly.equal expected data
        | None -> false) in
    let rec closed_sizes visiting var =
      if Set.mem visiting var then true
      else match Map.Poly.find recognised var with
        | None -> false
        | Some (_, _, body, _, _) ->
            Set.for_all (Term.fvar_apps_of body) ~f:(function
              | FunApp (FVar (callee, _, _), _, _) ->
                  closed_sizes (Set.add visiting var) callee
              | _ -> true)
    in
    let trusted = Map.Poly.filter_keys recognised ~f:(closed_sizes Set.Poly.empty) in
    let user = Map.Poly.filter_keys fenv ~f:(fun key -> not (Map.Poly.mem trusted key)) in
    if not (List.for_all (Map.Poly.data user) ~f:(fun (_, _, body, _, prop) ->
                  Formula.is_true prop
                  && Set.is_empty (Term.filtered_terms_of body ~f:T_array.is_lambda)))
    then false
    else
      let dependencies body =
        Set.union
          (Set.filter (Term.fvs_of body) ~f:(Map.Poly.mem user))
          (Set.Poly.filter_map (Term.fvar_apps_of body) ~f:(function
            | FunApp (FVar (var, _, _), _, _) when Map.Poly.mem user var -> Some var
            | _ -> None))
      in
      let finished = ref Set.Poly.empty in
      let rec acyclic visiting var =
        if Set.mem !finished var then true
        else if Set.mem visiting var then false
        else
          let (_, _, body, _, _) = Map.Poly.find_exn user var in
          let valid = Set.for_all (dependencies body)
              ~f:(acyclic (Set.add visiting var)) in
          if valid then finished := Set.add !finished var;
          valid
      in
      if List.for_all (Map.Poly.keys user) ~f:(acyclic Set.Poly.empty) then true
      else
        let ranks = Map.Poly.map user ~f:(fun (params, _, _, _, _) ->
            match List.last (List.filter (List.mapi params ~f:(fun i p -> (i,p)))
                    ~f:(fun (_, (_, sort)) -> Term.is_int_sort sort)) with
            | Some (i, (var, sort)) -> (i, Term.mk_var var sort)
            | None -> invalid_arg "No integer rank for recursive definition") in
        let zero = T_int.from_int 0 in
        let natural t = T_bool.mk_if_then_else
            (T_bool.of_formula (Formula.mk_atom (T_int.mk_leq zero t))) t zero in
        let obligations = ref [] in
        Map.Poly.iteri user ~f:(fun ~key ~data:(_, _, body, _, _) ->
            let caller_rank = natural (snd (Map.Poly.find_exn ranks key)) in
            let rec walk guards (term : Term.t) = match term with
              | Var (var, _, _) when Map.Poly.mem user var ->
                  invalid_arg "Known function used as a value in rank proof"
              | Var _ -> ()
              | FunApp (T_array.ALambda _, _, _) ->
                  invalid_arg "Array lambda is outside integer rank proof"
              | FunApp (T_bool.IfThenElse, [condition; yes; no], _) ->
                  walk guards condition;
                  let guard = Formula.eq condition (T_bool.make true) in
                  walk (guard :: guards) yes;
                  walk (Formula.mk_neg guard :: guards) no
              | FunApp (T_bool.Formula _, _, _) as term ->
                  if not (Set.is_empty (dependencies term)) then
                    invalid_arg "Recursive call under formula binder or operator"
              | FunApp (sym, args, _) ->
                  List.iter args ~f:(walk guards);
                  (match sym with
                   | FVar (var, _, _) when Map.Poly.mem user var ->
                       let arg = List.nth_exn args (fst (Map.Poly.find_exn ranks var)) in
                       obligations := Formula.mk_imply (Formula.and_of guards)
                           (Formula.mk_atom (T_int.mk_lt (natural arg) caller_rank))
                           :: !obligations
                   | _ -> ())
              | LetTerm _ -> invalid_arg "Unexpected remaining let in rank proof"
            in
            walk [] (if Term.is_let_free body then body else Term.elim_let body));
        List.for_all !obligations ~f:(fun phi ->
            match check_sat_base ~timeout:(Some 1000) ~fresh_solver:true
                    ~id (FunEnv.mk_empty ()) [Formula.mk_neg phi] with
            | `Unsat -> true
            | _ -> false)
  with exn when not (Common.Timer.is_async exn) -> false

(* [check_sat_base] after the rewrite of words in disguise, when it is on.
   A split word whose [x] also occurs outside [int_to_bv n] carries an integer
   quotient [q], and with it a coefficient [2^n] in linear arithmetic beside
   [ubv_to_int] of bit-vector terms; Z3 5.1.0 did not decide a one-parameter
   question of that shape in 30 s, and decided it in 0.16 s with [q] fixed to
   0.  So such a question is first asked with every quotient fixed to 0: a
   model of that strengthening is a model of the question, so its [sat] is
   returned as it is; anything else is not a verdict about the question,
   which is then asked as rewritten.  (Z3 5.1.0's integer-blasting bit-vector
   solver, [smt.bv.solver] 2, answered such questions fast too, and also
   answered [unsat] to a satisfiable one, so it is not used.) *)
let check_sat_unguarded =
  fun ?(timeout = None) ?(fresh_solver = false) ?(scoped = false)
      ?(defining_equations = false) ?fun_values_out ~id fenv phis ->
    let fresh_solver = fresh_solver || defining_equations in
    (* The query-only range rewrite cannot split a global also used in a
       defining body: the equality added afterwards would still read the
       original variable. Keep complete equations and the query correlated. *)
    if defining_equations || not (Atomic.get int_to_bv_range) then
      check_sat_base ~timeout ~fresh_solver ~scoped ~defining_equations
        ?fun_values_out ~id fenv phis
    else
      let ((phis', picked) as pre) = int_to_bv_range_subst phis in
      (* a rewritten question is asked in a context of its own: the pooled
         ones have been pushed, so Z3 answers in them with its incremental
         core and without its preprocessing, and a rewritten validation
         question that a fresh Z3 answered [sat] in 0.5 s did not return in
         120 s on a pooled solver *)
      let fresh_solver = fresh_solver || not (List.is_empty picked) in
      let quotients =
        List.filter_map picked ~f:(fun (_, _, _, q) ->
            Option.map q ~f:(fun q ->
                Formula.eq (Term.mk_var q T_int.SInt) (T_int.mk_int Z.zero)))
      in
      let full () =
        check_sat_base ~timeout ~fresh_solver ~scoped ~defining_equations
          ?fun_values_out ~pre ~id fenv phis
      in
      if List.is_empty quotients then full ()
      else
        match
          check_sat_base ~timeout ~fresh_solver ~scoped ~defining_equations
            ?fun_values_out ~pre:(phis' @ quotients, picked) ~id fenv phis
        with
        | `Sat model -> `Sat model
        | _ -> full ()

(* Supported defining environments are queried through fresh ordinary
   declarations and complete equations. For other environments,
   [check_sat_unguarded] is used for refutations. Its positive result requires
   a complete-context totality certificate and a query independent of known
   functions; totality alone does not certify their answering interpretation.
   In particular, a [`Sat] about formulas that apply a
   recursive function under a quantifier ([recursive_function_under_binder])
   is returned as [`Unknown]: Z3 5.1.0 answers such an unsatisfiable question
   [sat], with a model that falsifies it, so the answer is not a model and no
   caller may read it as one -- every caller that reads [`Sat] (or
   [check_valid]'s [`Invalid]) as a countermodel refuting a problem (the
   unfolding refuter, the zero-unknown verdict, the unknown-free sweeps) would
   otherwise report a satisfiable problem [unsat].  [`Unsat] is kept.  The
   shape is tested only after a [`Sat], so a question without it costs
   nothing more.

   Rejected: confirming the [`Sat] by substituting the model's values into the
   question and asking whether the negation of the result is unsatisfiable.
   The model's array values arrive as [lambda] terms, and Z3 5.1.0 answers
   [unsat] to [cnt 0 3 (lambda i. ite (i = 2) 15922 0) >= 2] for the count of
   [x] among the first [t] cells -- a true ground formula -- so the
   confirmation accepted the very model it was to reject. *)
(* A total extension of a background does not certify the native solver's
   interpretation of a known function called by its query. Check the original
   vocabulary, including nullary values, before any declaration slicing.
   The filtered traversal deliberately hides array-lambda bodies. Treat the
   lambda itself as a possible known-function dependence rather than certify
   independence from a traversal that cannot see its contents. *)
let query_uses_known_functions fenv phis =
  List.exists phis ~f:(fun phi ->
      not
        (Set.is_empty
           (Formula.filtered_terms_of phi ~f:(function
             | Var (var, _, _) | FunApp (FVar (var, _, _), _, _) ->
                 Map.Poly.mem fenv var
             | FunApp (T_array.ALambda _, _, _) -> not (Map.Poly.is_empty fenv)
             | _ -> false))))

let without_known_interpretations fenv values =
  List.filter values ~f:(fun ((var, _), _) -> not (Map.Poly.mem fenv var))

let value_uses_known_functions fenv term =
  not (Set.is_empty (Term.filtered_terms_of term ~f:(function
    | Var (var, _, _) | FunApp (FVar (var, _, _), _, _) -> Map.Poly.mem fenv var
    | FunApp (T_array.ALambda _, _, _) -> not (Map.Poly.is_empty fenv)
    | _ -> false)))

let shared_native_function_values_are_independent fenv values =
  List.for_all (without_known_interpretations fenv values)
    ~f:(fun (_, value) ->
      let terms = value.FunValue.default ::
        List.concat_map value.FunValue.entries ~f:(fun (args, result) -> result :: args)
      in
      not (List.exists terms ~f:(value_uses_known_functions fenv)))

(* The extension theorem used here is first-order. An arrow carrier encoded
   as an uninterpreted sort need not contain a known function's interpretation.
   Keep this restriction local to native positive admission. *)
let shared_native_context_is_first_order fenv =
  let first_order sort =
    Set.for_all (Term.sorts_of_sort sort) ~f:(fun sort ->
      not (Sort.is_arrow sort))
  in
  Map.Poly.for_all fenv ~f:(fun (params, result, body, _, _) ->
    List.for_all params ~f:(snd >> first_order)
    && first_order result
    && Set.for_all (Term.filtered_terms_of body ~f:(fun _ -> true))
         ~f:(Term.sort_of >> first_order)
    && Set.is_empty (Term.filtered_terms_of body ~f:(function
      | Var (var, _, _) ->
          (match Map.Poly.find fenv var with
           | Some (params, _, _, _, _) -> not (List.is_empty params)
           | None -> false)
      | _ -> false)))

let certify_shared_native_result ~id fenv phis ret =
  match ret with
  | `Sat _ when recursive_function_under_binder fenv (Formula.and_of phis) ->
      `Unknown "a recursive function under a quantifier: sat is not a model"
  | `Sat model when not (Map.Poly.is_empty fenv) ->
      if (not (query_uses_known_functions fenv phis))
         && shared_native_context_is_first_order fenv
         && has_total_defining_context ~id fenv
      (* Only the background assignment is certified extendable. Native
         interpretations of the unused known functions are not certificates. *)
      then
        let background = without_known_interpretations fenv model in
        if List.exists background ~f:(fun (_, value) ->
             Option.exists value ~f:(value_uses_known_functions fenv))
        then `Unknown "shared background model retains an uncertified known-function value"
        else `Sat background
      else `Unknown "known-function context has no verified shared model certificate"
  | _ -> ret


(* Serialized array lambdas are allowed, but every formula and term body is
   checked for original known symbols. Predicate fixpoints are conservatively
   refused rather than relying on term visitors that omit their bodies. *)
let finite_model_value_is_independent fenv term =
  let rec term_ok (term : Term.t) = match term with
    | Var (var, _, _) -> not (Map.Poly.mem fenv var)
    | LetTerm (_, _, def, body, _) -> term_ok def && term_ok body
    | FunApp (FVar (var, _, _), args, _) ->
        not (Map.Poly.mem fenv var) && List.for_all args ~f:term_ok
    | FunApp (T_bool.Formula phi, args, _) ->
        formula_ok phi && List.for_all args ~f:term_ok
    | FunApp (_, args, _) -> List.for_all args ~f:term_ok
  and formula_ok = function
    | Formula.Atom (atom, _) -> (match atom with
        | Atom.App (Predicate.Fixpoint _, _, _) -> false
        | Atom.App (_, args, _) -> List.for_all args ~f:term_ok
        | Atom.True _ | Atom.False _ -> true)
    | Formula.UnaryOp (_, phi, _) | Formula.Bind (_, _, phi, _) -> formula_ok phi
    | Formula.BinaryOp (_, left, right, _) -> formula_ok left && formula_ok right
    | Formula.LetFormula (_, _, def, body, _) -> term_ok def && formula_ok body
    | Formula.LetRec _ -> false
  in
  term_ok term


(* Introducing a definition-site global beneath a caller binder would capture
   it. Scopes containing known calls are refused; independent scopes need no
   replacement and can be kept unchanged. Definition bodies refuse every scope
   rather than alpha-renaming only
   some of the mutually embedded formula, term and predicate representations. *)
let rec finite_expansion_formula_has_scope ?(independent = fun _ -> false) = function
  | (Formula.Bind _ | Formula.LetFormula _) as phi ->
      not (independent (T_bool.of_formula phi))
  | Formula.LetRec _ -> true
  | Formula.UnaryOp (_, phi, _) -> finite_expansion_formula_has_scope ~independent phi
  | Formula.BinaryOp (_, left, right, _) ->
      finite_expansion_formula_has_scope ~independent left
      || finite_expansion_formula_has_scope ~independent right
  | Formula.Atom (atom, _) -> (match atom with
      | Atom.App (Predicate.Fixpoint _, _, _) -> true
      | Atom.App (_, args, _) -> List.exists args ~f:(finite_expansion_term_has_scope ~independent)
      | Atom.True _ | Atom.False _ -> false)
and finite_expansion_term_has_scope ?(independent = fun _ -> false) (term : Term.t) =
  match term with
  | Var _ -> false
  | LetTerm _ as term -> not (independent term)
  | FunApp (T_array.ALambda _, _, _) -> true
  | FunApp (T_bool.Formula phi, args, _) ->
      finite_expansion_formula_has_scope ~independent phi
      || List.exists args ~f:(finite_expansion_term_has_scope ~independent)
  | FunApp (_, args, _) -> List.exists args ~f:(finite_expansion_term_has_scope ~independent)

(* A finite equational expansion can certify a positive background witness.
   Pins strengthen the original query: failure at a pin is never a refutation.
   Full-context totality is required even for definitions absent from the query.
   The fixed fuel and size bounds limit work, not the semantics admitted. *)
let finite_defining_expansion fenv phis =
  let rec expand fuel phis =
    if List.fold phis ~init:0 ~f:(fun n phi -> n + Formula.ast_size phi) > 4096
    then None
    else if not (query_uses_known_functions fenv phis) then Some phis
    else if fuel = 0 then None
    else
      let replace (term : Term.t) = match term with
        | FunApp (FVar (var, _, _), args, _) as term ->
            (match Map.Poly.find fenv var with
             | Some (params, _, body, _, _) ->
                 Term.subst (Map.Poly.of_alist_exn
                   (List.zip_exn (List.map params ~f:fst) args)) body
             | None -> term)
        | Var (var, _, _) as term ->
            (match Map.Poly.find fenv var with
             | Some ([], _, body, _, _) -> body
             | _ -> term)
        | term -> term
      in
      let next = List.map phis ~f:(fun phi ->
        Formula.map_term ~f:replace phi |> Evaluator.simplify) in
      expand (fuel - 1) next
  in
  try
    if List.exists phis ~f:(finite_expansion_formula_has_scope
        ~independent:(finite_model_value_is_independent fenv))
       || Map.Poly.exists fenv ~f:(fun (_, _, body, _, _) -> finite_expansion_term_has_scope body)
    then None else expand 12 phis
  with exn when not (Common.Timer.is_async exn) -> None


let check_sat_by_finite_defining_expansion ~timeout ?fun_values_out ~id fenv phis =
  let calls = List.concat_map phis ~f:(fun phi ->
    Set.to_list (Formula.filtered_terms_of phi ~f:(function
      | FunApp (FVar (var, _, _), _, _) -> Map.Poly.mem fenv var
      | _ -> false))) in
  let ranked_calls = List.filter_map calls ~f:(function
    | FunApp (FVar (var, _, result), args, _) when Term.is_int_sort result ->
        let params, _, _, _, _ = Map.Poly.find_exn fenv var in
        List.last (List.filter_map (List.zip_exn params args)
          ~f:(fun ((_, sort), arg) -> if Term.is_int_sort sort then Some arg else None))
    | _ -> None) in
  if List.exists phis ~f:(finite_expansion_formula_has_scope
        ~independent:(finite_model_value_is_independent fenv))
     || Map.Poly.exists fenv ~f:(fun (_, _, body, _, _) -> finite_expansion_term_has_scope body)
     || List.is_empty calls || List.length calls <> List.length ranked_calls
     || recursive_function_under_binder fenv (Formula.and_of phis)
     || not (shared_native_context_is_first_order fenv)
     || not (has_total_defining_context ~id fenv)
  then None
  else
    let candidates =
      match finite_defining_expansion fenv phis with
      | Some expanded -> [expanded]
      | None ->
          let ranks = List.filter_map ranked_calls ~f:(function
            | Var (var, sort, _) when not (Map.Poly.mem fenv var) -> Some (var, sort)
            | _ -> None) |> Set.Poly.of_list |> Set.to_list in
          (match ranks with
           | [var, sort] ->
               List.filter_map [0; 1; 2; 3] ~f:(fun rank ->
                 let value = T_int.from_int rank in
                 let pinned = List.map phis ~f:(Formula.subst (Map.Poly.singleton var value)) in
                 Option.map (finite_defining_expansion fenv pinned) ~f:(fun expanded ->
                   Formula.eq (Term.mk_var var sort) value :: expanded))
           | _ -> [])
    in
    List.find_map candidates ~f:(fun expanded ->
      if query_uses_known_functions fenv expanded then None else
      let staged = Option.map fun_values_out ~f:(fun _ -> ref []) in
      match check_sat_base ~timeout ~fresh_solver:true
          ?fun_values_out:staged ~id (FunEnv.mk_empty ()) expanded with
      | `Sat model ->
          let model = without_known_interpretations fenv model in
          let values = Option.value_map staged ~default:[] ~f:(fun out ->
            without_known_interpretations fenv !out) in
          let independent term = finite_model_value_is_independent fenv term in
          if List.for_all model ~f:(fun (_, value) ->
               Option.for_all value ~f:independent)
             && List.for_all values ~f:(fun (_, value) ->
               List.for_all (value.FunValue.default ::
                 List.concat_map value.FunValue.entries
                   ~f:(fun (args, result) -> result :: args)) ~f:independent)
          then (
            Option.iter fun_values_out ~f:(fun out -> out := values);
            Some (`Sat model))
          else None
      | _ -> None)

let check_sat =
  fun ?(timeout = None) ?(fresh_solver = false) ?(scoped = false)
      ?fun_values_out ~id fenv phis ->
    (* Ordinary declarations plus every defining equality constrain even unused
       definitions; their answering model is the model returned to the caller. *)
    let defining_equations = supports_defining_equations fenv in
    (* Native model values must not escape a declined positive answer. Clear
       the caller's previous values even if the query raises, and publish only
       the values belonging to an accepted Sat. *)
    Option.iter fun_values_out ~f:(fun out -> out := []);
    let staged_values = Option.map fun_values_out ~f:(fun _ -> ref []) in
    let finite =
      if defining_equations then None
      else check_sat_by_finite_defining_expansion ~timeout
          ?fun_values_out:staged_values ~id fenv phis
    in
    let ret = match finite with
      | Some ret -> ret
      | None -> check_sat_unguarded ~timeout ~fresh_solver ~scoped ~defining_equations
          ?fun_values_out:staged_values ~id fenv phis
    in
    let ret =
      if defining_equations || Option.is_some finite then ret
      else certify_shared_native_result ~id fenv phis ret
    in
    let ret =
      match ret, staged_values with
      | `Sat _, Some staged
        when (not defining_equations) && Option.is_none finite
             && not (shared_native_function_values_are_independent fenv !staged) ->
          `Unknown "shared function model retains an uncertified known-function value"
      | _ -> ret
    in
    (match ret, fun_values_out, staged_values with
     | `Sat _, Some out, Some staged ->
         out := if defining_equations || Option.is_some finite then !staged
                else without_known_interpretations fenv !staged
     | _ -> ());
    ret

(* ------------------------------------------------------------------
   A base asserted once, asked against many extensions.

   Several questions that share most of their conjuncts -- a clause body
   [base] and one candidate head after another -- are asked in one solver of
   a context of the caller's own: [base_session_set] resets the solver and
   asserts the converted base at its root, and [base_session_check] converts
   only the extension, asserts it in a scope, checks and pops.  So the base is
   converted to Z3 and asserted once per base instead of once per question.

   Contract.  [base_session_check s ~timeout fenv phi] is [`Unsat] only when
   Z3 answers [unsat] to the conjunction of the last base set and [phi], and
   [`Sat m] only with a model [m] Z3 gives for that conjunction; any other
   answer, a raised exception other than an asynchronous one, a base or an
   extension the session refuses, all give [`Unknown], which says nothing.
   Refused: every nonempty defining environment. Supported environments require
   fresh ordinary declarations and complete defining equations; unsupported
   native definitions have no complete-context model certificate here. Also
   refused is a formula that
   [int_to_bv_range_subst] would rewrite (the
   rewrite picks its variables from the whole question, which the session
   never sees at once).  The context is pushed, so Z3 answers in its
   incremental core, as it does in every pooled context; a weaker core costs
   decisions, never soundness.  Not for
   concurrent use: one session belongs to one domain. *)
type base_session = { bs : instance; mutable bs_ok : bool }

let base_session_create ~id () =
  {
    bs = get_instance id [ ("model", "true") ] (Hashtbl.Poly.create ());
    bs_ok = false;
  }

(* [phis] converted in [s]'s context; [None] when a known-function context
   or the bit-vector range rewrite requires the caller's normal fallback. *)
let base_session_convert ~id s fenv phis =
  let phis = List.map phis ~f:expand_finite_array_eqs in
  let unchanged =
    (not (Atomic.get int_to_bv_range))
    ||
    let phis', picked = int_to_bv_range_subst phis in
    List.is_empty picked && List.for_all2_exn phis phis' ~f:phys_equal
  in
  if not (Map.Poly.is_empty fenv) || not unchanged then None
  else
    let inst = s.bs and fenv = fenv_for_query fenv phis in
    let ctx = inst.ctx in
    Common.PhaseTime.with_phase "dtenv" (fun () ->
        inst.dtenv <-
          z3_dtenv_of_formula ~init:inst.dtenv ctx (Formula.and_of phis));
    Common.PhaseTime.with_phase "fenv" (fun () ->
        inst.fenv <- z3_fenv_of ~id ~init:inst.fenv ctx [] [] fenv inst.dtenv);
    let phis = List.map phis ~f:(FunEnv.defined_formula_of fenv) in
    Some
      (Common.PhaseTime.with_phase "to-z3" (fun () ->
           List.map phis
             ~f:(of_formula_with_z3fenv ~id ctx [] [] inst.fenv inst.dtenv)))

let base_session_set ~id s fenv base =
  s.bs_ok <- false;
  try
    z3_solver_reset s.bs.solver;
    match base_session_convert ~id s fenv base with
    | None -> false
    | Some exprs ->
        Common.PhaseTime.with_phase "assert" (fun () ->
            z3_solver_add s.bs.solver exprs);
        s.bs_ok <- true;
        true
  with exn when not (Common.Timer.is_async exn) -> false

let base_session_check ~id s ~timeout fenv phi =
  if not s.bs_ok then `Unknown
  else
    try
      match base_session_convert ~id s fenv [ phi ] with
      | None -> `Unknown
      | Some exprs ->
          let ctx = s.bs.ctx and solver = s.bs.solver in
          let set_timeout ms =
            let params = Z3.Params.mk_params ctx in
            Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") ms;
            Z3.Solver.set_parameters solver params
          in
          Z3.Solver.push solver;
          Exn.protect
            ~f:(fun () ->
              set_timeout (Option.value timeout ~default:0);
              Common.PhaseTime.with_phase "assert" (fun () ->
                  z3_solver_add solver exprs);
              match z3_check solver [] with
              | UNSATISFIABLE -> `Unsat
              | SATISFIABLE -> (
                  match z3_solver_get_model solver with
                  | Some model ->
                      `Sat
                        (Common.PhaseTime.with_phase "model" (fun () ->
                             model_of ctx s.bs.dtenv model))
                  | None -> `Unknown)
              | UNKNOWN -> `Unknown)
            ~finally:(fun () ->
              set_timeout 0;
              try Z3.Solver.pop solver 1
              with _ ->
                (* a solver whose scope cannot be closed holds the extension:
                   the base is no longer the only thing asserted *)
                s.bs_ok <- false)
    with exn when not (Common.Timer.is_async exn) -> `Unknown

(* ------------------------------------------------------------------
   Asking a quantified query again in a context made for it alone.

   WHY.  A Z3 solver that has been pushed, or that has had assertions added
   after a check, answers from then on in incremental mode: the [smt] core
   alone, without the tactic preprocessing (the elimination of unconstrained
   terms among it) that a fresh solver runs first.  With Z3's default
   [combined_solver.solver2_unknown=1], a quantified goal the core leaves
   "unknown (incomplete quantifiers)" is not handed to the tactic either.
   Measured on Z3 4.15.2, one goal over arrays and a tuple datatype: [sat] in
   a fresh context; unknown in the same context after a [(push 1)(pop 1)];
   unknown in a fresh context that merely declares a recursive function the
   goal never uses.  The pooled instances below are pushed routinely, so every
   quantified query on the pooled path is asked in incremental mode.  Every
   defined function is also registered in a pooled context, as a recursive
   definition, whether or not the query uses it.

   WHAT IT DOES NOT BUY.  On that same goal a FRESH context decides only about
   half the time: declaring a few unrelated constants first, which changes
   nothing but the internal identifiers of the terms, flips the answer between
   [sat] and "incomplete quantifiers" (8 of 16 such draws decided), while a
   pushed context and one holding an unused recursive definition decided 0 of
   16.  So a fresh attempt is a second chance at a decision the pooled context
   cannot make at all, not a guarantee of one.

   WHAT.  [fresh_retry_policy] selects one of three behaviours:
     [Off]            -- the pooled answer is final (the default);
     [RetryOnUnknown] -- a quantified query the pooled context answers
                         [`Unknown] is asked once more in a fresh context;
     [AlwaysFresh]    -- every quantified query is asked in a fresh context
                         first; for measuring what the pooled path loses, not
                         for ordinary runs.
   The fresh question is told only the defined functions the formula reaches
   (directly or through other definitions), is put in negation normal form,
   carries the caller's own timeout, and is not asked when [may_not_return]
   says the solver may never return on its shape.  Leaving out a definition
   the formula does not reach does not change what it means, and negation
   normal form is an equivalence, so the fresh query is the same question.

   CONTRACT.  Under [RetryOnUnknown] an answer the pooled query DECIDED
   ([`Sat], [`Unsat]) is returned unchanged, and so is a [`Timeout]: the
   caller's budget has been spent, and a second attempt would double it.  Only
   an [`Unknown] from a quantified query is replaced, and only by a decision
   of the fresh context; when that is undecided too, the pooled answer stands.

   SETTING IT.  The policy is process-global and is written once, before any
   solving domain exists (a solver configuration sets it when it is loaded);
   the counters are atomic because queries are asked from several domains.

   ADAPTING.  Whether the retry still earns anything depends on the Z3 version.
   [fresh_retry_report] says how often the pooled path was undecided and how
   often the fresh context decided it; a canary test checks, per Z3 version,
   that a pushed context still loses the decision.  If Z3 stops losing it, the
   policy can be set to [Off] and this block becomes dead weight to be removed.

   The process-wide default is [RetryOnUnknown]: it changes an answer only where the pooled
   path returned [Unknown] on a quantified query, and replaces it only by a decision of the
   fresh attempt, so an answer the pooled path gave is never touched. *)
type fresh_retry_policy = Off | RetryOnUnknown | AlwaysFresh
[@@deriving yojson]

let fresh_retry_policy = Atomic.make RetryOnUnknown
let set_fresh_retry_policy p = Atomic.set fresh_retry_policy p
let get_fresh_retry_policy () = Atomic.get fresh_retry_policy

let str_of_fresh_retry_policy = function
  | Off -> "Off"
  | RetryOnUnknown -> "RetryOnUnknown"
  | AlwaysFresh -> "AlwaysFresh"

let fresh_retry_pooled_unknown = Atomic.make 0
let fresh_retry_pooled_timeout = Atomic.make 0
let fresh_retry_attempted = Atomic.make 0
let fresh_retry_refused = Atomic.make 0
let fresh_retry_sat = Atomic.make 0
let fresh_retry_unsat = Atomic.make 0
let fresh_retry_undecided = Atomic.make 0

let fresh_retry_report () =
  sprintf
    "(z3-fresh-retry (policy %s) (pooled-quantified-unknown %d) \
     (pooled-quantified-timeout %d) (fresh-asked %d) (refused-shape %d) \
     (fresh-sat %d) (fresh-unsat %d) (fresh-undecided %d))"
    (str_of_fresh_retry_policy (get_fresh_retry_policy ()))
    (Atomic.get fresh_retry_pooled_unknown)
    (Atomic.get fresh_retry_pooled_timeout)
    (Atomic.get fresh_retry_attempted)
    (Atomic.get fresh_retry_refused)
    (Atomic.get fresh_retry_sat)
    (Atomic.get fresh_retry_unsat)
    (Atomic.get fresh_retry_undecided)

(* The entry point without the policy: what every caller got before it
   existed, and what the fresh attempt itself goes through. *)
let check_sat_without_retry = check_sat

(* Ask [phis] in a fresh context, or say why not.  [None] when the shape is
   one the solver may not return on. *)
let check_sat_fresh ?fun_values_out ~timeout ~id fenv phis =
  Option.iter fun_values_out ~f:(fun out -> out := []);
  if List.exists phis ~f:may_not_return then (
    Atomic.incr fresh_retry_refused;
    None)
  else (
    Atomic.incr fresh_retry_attempted;
    let ret =
      check_sat_without_retry ~timeout ~fresh_solver:true ?fun_values_out ~id
        fenv
        (List.map phis ~f:Formula.nnf_of)
    in
    (match ret with
    | `Sat _ -> Atomic.incr fresh_retry_sat
    | `Unsat -> Atomic.incr fresh_retry_unsat
    | _ -> Atomic.incr fresh_retry_undecided);
    Some ret)

let check_sat_policy ?(timeout = None) ?(fresh_solver = false) ?fun_values_out
    ~id fenv phis =
  let policy = get_fresh_retry_policy () in
  let quantified () =
    List.exists phis ~f:(fun phi ->
        Formula.number_of_quantifiers (FunEnv.defined_formula_of fenv phi) > 0)
  in
  match policy with
  | Off -> check_sat_without_retry ?fun_values_out ~timeout ~fresh_solver ~id fenv phis
  | _ when fresh_solver ->
      check_sat_without_retry ?fun_values_out ~timeout ~fresh_solver ~id fenv phis
  | AlwaysFresh when quantified () -> (
      match check_sat_fresh ?fun_values_out ~timeout ~id fenv phis with
      | Some ret -> ret
      | None -> check_sat_without_retry ?fun_values_out ~timeout ~id fenv phis)
  | AlwaysFresh -> check_sat_without_retry ?fun_values_out ~timeout ~id fenv phis
  | RetryOnUnknown -> (
      match check_sat_without_retry ?fun_values_out ~timeout ~id fenv phis with
      | `Unknown _ as ret when quantified () -> (
          Atomic.incr fresh_retry_pooled_unknown;
          match check_sat_fresh ?fun_values_out ~timeout ~id fenv phis with
          | Some ((`Sat _ | `Unsat) as decided) -> decided
          | Some _ | None -> ret)
      | `Timeout as ret when quantified () ->
          Atomic.incr fresh_retry_pooled_timeout;
          ret
      | ret -> ret)

(* ------------------------------------------------------------------
   A proving-only second attempt at a validity question over SMT-LIB
   sequences, with the sequences axiomatised.

   WHY.  Z3's native sequence theory (4.15.2) leaves undecided -- a timeout
   whatever the budget, or "unknown" -- an entailment of the shape
     len s1 = len s /\ (forall k. 0 <= k < len s => post (s1[k]) (s[k]))
       => forall k. 0 <= k < len s => post ((s1 ++ [v])[k]) ((s ++ [b])[k])
   which is what a pointwise relation between two sequences extended by one
   element each amounts to, and which every Rust iterator adapter over a
   visited sequence produces.  The same entailment with the sequences replaced
   by an uninterpreted sort and a few axioms about length, reads and
   concatenation -- the encoding Dafny, Boogie and Why3 hand to an SMT solver --
   is decided at once, by E-matching on the axioms.

   WHAT.  [prove_valid_by_seq_axioms] translates the question
   ([SeqAxiomEncoding.encode]), asks the negation of the translation together
   with the axioms below in a context made for it, with model production off,
   and answers [SeqAxProved] only on [unsat].

   SOUNDNESS, AND ITS BOUNDARY.  Each axiom is a theorem of the sequence
   theory (checked against z3's native theory, each one's negation [unsat]),
   so reading the new sort as real sequences turns any model of the original
   negation into a model of the translated negation and the axioms; an
   [unsat] of the latter therefore proves the original valid.  A [sat] proves
   nothing: the axioms do not pin the new sort down to sequences (they say
   nothing about an index out of range, and nothing makes two elements with
   the same length and reads equal), so its models are not sequences.  That is
   why the outcome type below has no constructor carrying a model, why the
   solver is created with model production off and no model is ever read, and
   why [with_seq_axiom_fallback] can only turn an undecided answer into
   [`Valid] and otherwise returns the answer it was given, unchanged.

   THE AXIOMS, per element sort [E] with [S] standing for [(Seq E)]; each
   quantified one carries exactly one trigger, on the composite term it
   describes (never on a bare constructor, which fires once per syntactic
   occurrence and is how sequence axiomatisations loop), and every read is
   range-guarded, because a native read out of range is left open per
   sequence and index and an unguarded read axiom is false there:
     len s >= 0                                         {len s}
     len empty = 0
     len s = 0 => s = empty                             {len s}
     len (unit x) = 1                                   {len (unit x)}
     i = 0 => nth (unit x) i = x                        {nth (unit x) i}
     len (a ++ b) = len a + len b                       {len (a ++ b)}
     0 <= i < len a => nth (a ++ b) i = nth a i, and
     len a <= i < len a + len b
       => nth (a ++ b) i = nth b (i - len a)            {nth (a ++ b) i}
     0 <= o, 0 <= n, o + n <= len s
       => len (extract s o n) = n                       {len (extract s o n)}
     0 <= o, 0 <= n, o + n <= len s, 0 <= k < n
       => nth (extract s o n) k = nth s (o + k)         {nth (extract s o n) k}
     len (store s i v) = len s                          {len (store s i v)}
     0 <= n < len s => (i = n => nth (store s i v) n = v)
                    /\ (i <> n => nth (store s i v) n = nth s n)
                                                        {nth (store s i v) n}
   These follow Dafny's prelude (one function per operation, one trigger per
   axiom on the composite term), with Why3's range guards on the reads of a
   concatenation.  There is no associativity axiom (none of those preludes
   states one as a quantified fact); the translation instead writes every
   concatenation as one left-nested chain without empty operands, which is
   exact.  Nor is there extensionality.  [store] is this tree's sequence
   write, whose meaning is the guarded three-piece concatenation
   [T_seq.store_expansion_of]; the two store axioms were checked against that
   expansion. *)
type seq_axiom_outcome =
  | SeqAxProved
  | SeqAxNotProved of string  (** [sat], [unknown] or [timeout]: nothing *)
  | SeqAxDeclined of string  (** not asked: the translation is not faithful *)

let seq_axioms_of_family ctx dtenv (fam : SeqAxiomEncoding.family) =
  let int = Z3.Arithmetic.Integer.mk_sort ctx in
  let s = of_sort ctx dtenv fam.seq_sort in
  let e = of_sort ctx dtenv fam.elem in
  let decl v dom rng = Z3.FuncDecl.mk_func_decl ctx (of_var ctx v) dom rng in
  let len = decl fam.len [ s ] int in
  let nth = decl fam.nth [ s; int ] e in
  let concat = decl fam.concat [ s; s ] s in
  let unit_ = decl fam.unit_ [ e ] s in
  let empty = decl fam.empty [] s in
  let extract = decl fam.extract [ s; int; int ] s in
  let store = decl fam.store [ s; int; e ] s in
  let ( @. ) d args = Z3.FuncDecl.apply d args in
  let var name sort = Z3.Expr.mk_const_s ctx ("seqax!" ^ name) sort in
  let num n = Z3.Arithmetic.Integer.mk_numeral_i ctx n in
  let ( <=. ) a b = Z3.Arithmetic.mk_le ctx a b in
  let ( <. ) a b = Z3.Arithmetic.mk_lt ctx a b in
  let ( +. ) a b = Z3.Arithmetic.mk_add ctx [ a; b ] in
  let ( -. ) a b = Z3.Arithmetic.mk_sub ctx [ a; b ] in
  let ( =. ) a b = Z3.Boolean.mk_eq ctx a b in
  let ( ==> ) a b = Z3.Boolean.mk_implies ctx a b in
  let conj l = Z3.Boolean.mk_and ctx l in
  let forall vars trigger body =
    Z3.Quantifier.expr_of_quantifier
    @@ Z3.Quantifier.mk_forall_const ctx vars body None
         [ Z3.Quantifier.mk_pattern ctx [ trigger ] ]
         [] None None
  in
  let sa = var "s" s and a = var "a" s and b = var "b" s in
  let x = var "x" e and v = var "v" e in
  let i = var "i" int and k = var "k" int and o = var "o" int in
  let n = var "n" int in
  let emp = empty @. [] in
  let in_extract = conj [ num 0 <=. o; num 0 <=. n; (o +. n) <=. (len @. [ sa ]) ] in
  [
    forall [ sa ] (len @. [ sa ]) (num 0 <=. (len @. [ sa ]));
    (len @. [ emp ]) =. num 0;
    forall [ sa ] (len @. [ sa ]) ((len @. [ sa ]) =. num 0 ==> (sa =. emp));
    forall [ x ] (len @. [ unit_ @. [ x ] ]) ((len @. [ unit_ @. [ x ] ]) =. num 1);
    forall [ x; i ]
      (nth @. [ unit_ @. [ x ]; i ])
      (i =. num 0 ==> ((nth @. [ unit_ @. [ x ]; i ]) =. x));
    forall [ a; b ]
      (len @. [ concat @. [ a; b ] ])
      ((len @. [ concat @. [ a; b ] ]) =. ((len @. [ a ]) +. (len @. [ b ])));
    (let ab = concat @. [ a; b ] in
     forall [ a; b; i ] (nth @. [ ab; i ])
       (conj
          [
            conj [ num 0 <=. i; i <. (len @. [ a ]) ]
            ==> ((nth @. [ ab; i ]) =. (nth @. [ a; i ]));
            conj [ (len @. [ a ]) <=. i; i <. ((len @. [ a ]) +. (len @. [ b ])) ]
            ==> ((nth @. [ ab; i ]) =. (nth @. [ b; i -. (len @. [ a ]) ]));
          ]));
    (let ex = extract @. [ sa; o; n ] in
     forall [ sa; o; n ] (len @. [ ex ]) (in_extract ==> ((len @. [ ex ]) =. n)));
    (let ex = extract @. [ sa; o; n ] in
     forall [ sa; o; n; k ] (nth @. [ ex; k ])
       (conj [ in_extract; num 0 <=. k; k <. n ]
       ==> ((nth @. [ ex; k ]) =. (nth @. [ sa; o +. k ]))));
    (let st = store @. [ sa; i; v ] in
     forall [ sa; i; v ] (len @. [ st ]) ((len @. [ st ]) =. (len @. [ sa ])));
    (let st = store @. [ sa; i; v ] in
     forall [ sa; i; v; n ] (nth @. [ st; n ])
       (conj [ num 0 <=. n; n <. (len @. [ sa ]) ]
       ==> conj
             [
               i =. n ==> ((nth @. [ st; n ]) =. v);
               Z3.Boolean.mk_not ctx (i =. n)
               ==> ((nth @. [ st; n ]) =. (nth @. [ sa; n ]));
             ]));
  ]

(* Whether the time spent BUILDING the axiomatised question counts against
   its budget, per domain ([with_seq_axiom_charge_build]; default [false]: the
   budget is the solver's [timeout] alone, as it always was).  Why: the
   translation, the expansion of finite array equalities, the negation normal
   form and the conversion of a goal of hundreds of disjuncts were measured to
   take about 2 s per question on a large Rust-derived input, against a 500 ms
   budget for the solver call, so that budget bounded the cheap part.  When
   charged, the build is checked against the budget after each of its steps,
   a question whose budget is spent before the solver is asked is not asked
   ([SeqAxNotProved]), and the solver gets what is left.  Not asking can only
   lose a proof: nothing but [SeqAxProved] is ever read from this question. *)
let seq_axiom_charge_build_key : bool Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> false)

let with_seq_axiom_charge_build charge f =
  if not charge then f ()
  else
    let saved = Stdlib.Domain.DLS.get seq_axiom_charge_build_key in
    Stdlib.Domain.DLS.set seq_axiom_charge_build_key true;
    Exn.protect ~f ~finally:(fun () ->
        Stdlib.Domain.DLS.set seq_axiom_charge_build_key saved)

(* Wall-clock time spent building fallback questions (everything before the
   solver call), per domain, in seconds; for tracing only. *)
let seq_axiom_build_secs_key : float ref Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> ref 0.)

let seq_axiom_fallback_build_secs_here () =
  !(Stdlib.Domain.DLS.get seq_axiom_build_secs_key)

(* How many fallback questions were not asked because building them spent
   their budget (with the build charged); process-wide, for the report. *)
let seq_axiom_build_spent = Atomic.make 0

(* The forced collection before the fresh context of each fallback question
   ([new_context_full_major_every]), made before every n-th of those contexts
   only; [1], the default, before each, as for every other new context.  Why:
   the collection's cost grows with the live heap, and over a heap of 1-2 GB it
   took about a second per question, against well under a second for the
   question itself, so on a large Rust-derived input it was most of the
   fallback's time (14 questions, 11 s of the first 120 s).  The question asked
   is the same either way: its context is its own and is dropped after the
   answer, model production is off and nothing but [SeqAxProved] is read from
   it.  What changes is when the dropped contexts are released: at most n of
   them wait for the collector.  Process-wide, written once when a solver
   configuration that asks for it is loaded. *)
let seq_axiom_full_major_every = Atomic.make 1
let seq_axiom_contexts = Atomic.make 0

let set_seq_axiom_full_major_every n =
  Atomic.set seq_axiom_full_major_every (Int.max 1 n)

(* a fresh, model-free instance for one fallback question: as [get_instance]
   gives it, with the forced collection skipped except before every n-th
   ([seq_axiom_full_major_every]) *)
let seq_axiom_instance id =
  (* a clean pooled context when [clean_reset_pool] is on (no collection when
     one is waiting), a fresh one otherwise *)
  let mk () = lease_clean_instance ~arith:None id [ ("model", "false") ] in
  let every = Atomic.get seq_axiom_full_major_every in
  (* under the byte rule ([new_context_full_major_bytes]) the context's
     collection is decided by heap growth, so no thinning by count here *)
  if every <= 1 || Option.is_some (Atomic.get new_context_full_major_bytes)
  then mk ()
  else
    let k = Atomic.fetch_and_add seq_axiom_contexts 1 in
    if k % every = 0 then mk ()
    else
      (* [Int.max_value]: no collection for this context (unless it is the
         first context of the process, which is collected for at any setting) *)
      with_new_context_full_major_every Int.max_value mk

(* A Z3 resource limit ([rlimit], see [rlimit_key]) for the sequence-axiom
   fallback's questions asked while [with_seq_axiom_rlimit] runs, beside their
   wall-clock budget, which stays as the bound on a check Z3 does not
   interrupt.  Kept apart from [rlimit_key] because the fallback asks in a
   context of its own, whose work on the axiomatised form is counted from a
   fresh counter and is a different quantity from the native question's: the
   two limits are chosen separately.  An exhausted limit is an undecided
   fallback, which keeps the caller's answer as it was (the fallback can only
   turn an undecided answer into [`Valid]).  Per domain; [None] (the default)
   sets no limit, the parameter not even set. *)
let seq_axiom_rlimit_key : int option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_seq_axiom_rlimit rlimit f =
  match rlimit with
  | None -> f ()
  | Some _ ->
      let saved = Stdlib.Domain.DLS.get seq_axiom_rlimit_key in
      Stdlib.Domain.DLS.set seq_axiom_rlimit_key rlimit;
      Exn.protect ~f ~finally:(fun () ->
          Stdlib.Domain.DLS.set seq_axiom_rlimit_key saved)

(* Asking the fallback's question in a forked copy of this process.

   Why: each fallback question is asked in a Z3 context of its own, and a
   context's memory is released only when the collector finalises the OCaml
   value that holds it, so a full major collection is forced before each new
   context ([new_context_full_major_every]).  Over a heap of 1-2 GB that
   collection costs about a second, against a question that takes well under
   one.  In a forked copy the context is made, used and dropped in the copy,
   whose exit releases it with everything else, so this process makes no
   context and forces no collection for the question.

   Contract of [ask_seq_axiom_question ~timeout ask]: with no runner set (the
   default) it is [ask ()].  With a runner set, [ask] runs in a forked copy
   killed after [seq_axiom_fork_kill_ms timeout] milliseconds, and the outcome
   is the copy's [ask ()] -- the same question with the same parameters (its Z3
   [timeout] and resource limit included) as in this process -- or
   [SeqAxNotProved] when the copy was killed, died or raised.  When no copy
   can be made (OCaml refuses to fork while other domains run) [ask] runs
   here, as with no runner.  So the outcome is [SeqAxProved] only when [ask ()]
   proved the question in some process, and a caller that reads nothing but
   [SeqAxProved] (every caller: [with_seq_axiom_fallback]) can only lose a
   proof to the kill, never gain a different answer.  The outcome type carries
   strings only, so it survives the trip back through [Marshal].

   In the copy no collection is forced before its context (the collection would
   only copy the parent's heap pages it marks), and the collector's pacing is
   relaxed for the same reason; the copy lives for one question.  A Z3 timer
   armed in the copy fires there: Z3 joins and deletes its timer threads in a
   [pthread_atfork] prepare handler, so the copy starts with none and makes its
   own (Z3's [scoped_timer]).  The kill is a backstop for the build of the
   context and the conversion, which the Z3 timeout does not cover. *)
type seq_axiom_fork_runner =
  ms:int ->
  (unit -> seq_axiom_outcome) ->
  [ `Value of seq_axiom_outcome | `Lost | `Not_forked ]

let seq_axiom_fork_runner : seq_axiom_fork_runner option Atomic.t =
  Atomic.make None

(* process-wide, written once when a solver configuration that asks for it is
   loaded (the forking itself lives above this library) *)
let set_seq_axiom_fork_runner r = Atomic.set seq_axiom_fork_runner r

(* the wall-clock kill for a copy asking a question whose Z3 budget is
   [timeout] ms: three times that budget, and never under one second, so the
   copy's own timeout is what normally ends an undecided question *)
let seq_axiom_fork_kill_ms timeout = Int.max 1000 (3 * timeout)

(* process-wide counts, for the report and for tests: questions answered by a
   copy, copies killed or dead, and questions asked here because no copy could
   be made *)
let seq_axiom_forked = Atomic.make 0
let seq_axiom_fork_lost = Atomic.make 0
let seq_axiom_fork_unavailable = Atomic.make 0

let in_seq_axiom_fork_copy ask =
  (* the first context of a process is collected for at any setting; this
     copy's counter is its own, so marking one context made skips that too *)
  if Atomic.get new_contexts = 0 then Atomic.incr new_contexts;
  Gc.set { (Gc.get ()) with space_overhead = 100_000 };
  with_new_context_full_major_every Int.max_value ask

let ask_seq_axiom_question ~timeout ask =
  match Atomic.get seq_axiom_fork_runner with
  | None -> ask ()
  | Some runner -> (
      match
        runner ~ms:(seq_axiom_fork_kill_ms timeout) (fun () ->
            in_seq_axiom_fork_copy ask)
      with
      | `Value outcome ->
          Atomic.incr seq_axiom_forked;
          outcome
      | `Lost ->
          Atomic.incr seq_axiom_fork_lost;
          SeqAxNotProved "the forked copy was killed or died"
      | `Not_forked ->
          Atomic.incr seq_axiom_fork_unavailable;
          ask ())

let prove_valid_by_seq_axioms ~timeout ~id (fenv : FunEnv.t) phi =
  Common.PhaseTime.with_phase "seq-axiom" @@ fun () ->
  let stage, _ = Common.PhaseTime.stages () in
  stage "reach";
  let started = Common.Clock.now_float () in
  let charge = Stdlib.Domain.DLS.get seq_axiom_charge_build_key in
  let elapsed_ms () =
    Float.iround_towards_zero_exn
      (Time_float.Span.to_ms (Time_float.diff (Common.Clock.now_float ()) started))
  in
  let noted = ref false in
  let note_build () =
    if not !noted then (
      noted := true;
      let here = Stdlib.Domain.DLS.get seq_axiom_build_secs_key in
      here := !here +. (Float.of_int (elapsed_ms ()) /. 1000.))
  in
  (* [Some outcome] when the build has spent the budget *)
  let spent () =
    if charge && elapsed_ms () >= timeout then (
      Atomic.incr seq_axiom_build_spent;
      Some (SeqAxNotProved "budget spent building the axiomatised question"))
    else None
  in
  let finish r =
    note_build ();
    r
  in
  let reached = fenv_reached_by fenv phi in
  stage "encode";
  if
    Map.Poly.exists reached ~f:(fun (params, sret, def, _, property) ->
        List.exists params ~f:(snd >> SeqAxiomEncoding.mentions_seq_sort)
        || SeqAxiomEncoding.mentions_seq_sort sret
        || SeqAxiomEncoding.mentions_seq (Formula.eq def def)
        || SeqAxiomEncoding.mentions_seq property)
  then finish (SeqAxDeclined "a defined function over sequences")
  else
    match SeqAxiomEncoding.encode phi with
    | Error reason -> finish (SeqAxDeclined reason)
    | Ok (phi', families, copies) -> (
        match spent () with
        | Some r -> finish r
        | None ->
        stage "negate";
        let neg =
          Formula.nnf_of
          @@ FunEnv.defined_formula_of reached
          @@ expand_finite_array_eqs (Formula.negate phi')
        in
        stage "shape";
        if may_not_return neg then finish (SeqAxDeclined "the translation's shape")
        else
          match spent () with
          | Some r -> finish r
          | None ->
          (* the part that makes a Z3 context: run here, or in a forked copy
             when [seq_axiom_fork_runner] is set ([ask_seq_axiom_question]) *)
          ask_seq_axiom_question ~timeout @@ fun () ->
          (* model production off: nothing a [sat] would produce may be read.
             A context of its own per question, whose creation (with the full
             major collection before it, [new_context_full_major_every]) is
             timed apart from the shape test *)
          stage "context";
          let instance = seq_axiom_instance id in
          let ctx, solver = (instance.ctx, instance.solver) in
          (* the context goes back to the clean pool (when that is on) only
             if this question declared no recursive function in it and no
             datatype copy of the encoding: a copy's fields name families
             numbered per question, so one copy name can stand for two
             different datatypes in two questions, and a context reuses a
             declared datatype by its name *)
          let reusable =
            ref (Map.Poly.is_empty reached && List.is_empty copies)
          in
          let release () =
            release_clean_instance ~arith:None ~reusable:!reusable id instance
          in
          stage "to-z3";
          (fun outcome -> release (); outcome) @@
          match
            let local =
              List.fold copies ~init:(DTEnv.of_formula neg) ~f:(fun env c ->
                  Map.Poly.set env ~key:(Datatype.full_name_of c) ~data:c)
            in
            let plain =
              Map.Poly.filter (get_dtenv ()) ~f:(fun dt ->
                  not (SeqAxiomEncoding.mentions_seq_sort (T_dt.SDT dt)))
            in
            let dtenv =
              z3_dtenv_of_dtenv ~init:instance.dtenv ctx
                (Map.Poly.merge_skewed plain local ~combine:(fun ~key:_ _ c ->
                     c))
            in
            if !reusable then instance.dtenv <- dtenv;
            let z3fenv = z3_fenv_of ~id ctx [] [] reached dtenv in
            let goal = of_formula_with_z3fenv ~id ctx [] [] z3fenv dtenv neg in
            let axioms =
              List.concat_map families ~f:(seq_axioms_of_family ctx dtenv)
            in
            note_build ();
            let left = timeout - elapsed_ms () in
            if charge && left <= 0 then (
              Atomic.incr seq_axiom_build_spent;
              `Spent)
            else
            let budget_ms = if charge then left else timeout in
            let params = Z3.Params.mk_params ctx in
            Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout")
              budget_ms;
            Option.iter (Stdlib.Domain.DLS.get seq_axiom_rlimit_key)
              ~f:(fun r ->
                Z3.Params.add_int params (Z3.Symbol.mk_string ctx "rlimit") r);
            Z3.Solver.set_parameters solver params;
            Z3.Solver.add solver (axioms @ [ goal ]);
            stage "ask";
            if dump_z3_queries then
              prerr_endline
                ("=== Z3 query (sequence axioms) ===\n"
               ^ Z3.Solver.to_string solver);
            (* under [COAR_Z3_RLIMIT_LOG] with a label set, one [CHECK] line
               for this check, labelled [<label>:seqax], in the format of
               [check_sat_base]'s (the fresh column is always true here: the
               fallback asks in a context of its own).  Without the variable
               or a label nothing is read *)
            let log_check =
              match
                ( Stdlib.Domain.DLS.get rlimit_label_key,
                  Lazy.force rlimit_log_file )
              with
              | Some label, Some _ ->
                  let before = rlimit_count_of solver in
                  let t0 = Core_unix.gettimeofday () in
                  fun outcome ->
                    let after = rlimit_count_of solver in
                    rlimit_log_line
                      (sprintf "CHECK\t%d\t%s:seqax\t%s\t%.3f\t%s\t%d\t%d\t%b\ttrue"
                         (Core_unix.getpid () |> Pid.to_int)
                         label
                         (match (before, after) with
                         | Some b, Some a -> sprintf "%.0f" (a -. b)
                         | _ -> "na")
                         (Core_unix.gettimeofday () -. t0)
                         outcome budget_ms (Formula.ast_size neg)
                         (Formula.number_of_quantifiers neg > 0))
              | _ -> fun _ -> ()
            in
            match z3_check solver [] with
            | res ->
                log_check
                  (match res with
                  | Z3.Solver.UNSATISFIABLE -> "unsat"
                  | Z3.Solver.SATISFIABLE -> "sat"
                  | Z3.Solver.UNKNOWN ->
                      "unknown:"
                      ^ String.tr ~target:'\t' ~replacement:' '
                          (Z3.Solver.get_reason_unknown solver));
                `Asked res
            | exception e ->
                log_check
                  ("raised:" ^ Exn.to_string e
                  |> String.tr ~target:'\t' ~replacement:' '
                  |> fun s -> String.prefix s 60);
                raise e
          with
          | `Spent ->
              SeqAxNotProved "budget spent building the axiomatised question"
          | `Asked Z3.Solver.UNSATISFIABLE -> SeqAxProved
          | `Asked Z3.Solver.SATISFIABLE -> SeqAxNotProved "sat"
          | `Asked Z3.Solver.UNKNOWN ->
              SeqAxNotProved (Z3.Solver.get_reason_unknown solver)
          | exception exn_ when not (Common.Timer.is_async exn_) ->
              reusable := false;
              finish (SeqAxDeclined ("the encoding raised " ^ Exn.to_string exn_)))

(* The policy: [None] leaves the fallback off; [Some ms] asks it wherever a
   validity question over sequences comes back undecided, with a budget of at
   most [ms] milliseconds (and at most the caller's own budget).  Process-wide,
   written once when a solver configuration that asks for it is loaded. *)
let seq_axiom_fallback_budget : int option Atomic.t = Atomic.make None
let set_seq_axiom_fallback ms = Atomic.set seq_axiom_fallback_budget (Some ms)
let seq_axiom_asked = Atomic.make 0
let seq_axiom_declined = Atomic.make 0
let seq_axiom_proved = Atomic.make 0
let seq_axiom_not_proved = Atomic.make 0

(* Wall-clock time spent in fallback questions, for tracing only: the
   process-wide total in microseconds (the end-of-run report) and a per-domain
   running total in seconds, which a caller reads before and after one of its
   own questions to say how much of that question was the fallback.  Reading
   or writing either changes no answer. *)
let seq_axiom_micros = Atomic.make 0
let seq_axiom_secs_key : float ref Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> ref 0.)

let seq_axiom_fallback_secs_here () = !(Stdlib.Domain.DLS.get seq_axiom_secs_key)

(* A per-domain cap on that budget, for one caller's questions: [None] (the
   default) leaves the process-wide budget as it is; [Some ms] with [ms <= 0]
   asks no fallback; [Some ms] otherwise asks it with at most [ms].  It can
   only lower the budget or switch the fallback off, never switch it on, so a
   caller that sets it can only lose proofs the fallback would have given:
   the fallback turns nothing but an undecided answer into [`Valid]. *)
let seq_axiom_fallback_cap_key : int option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_seq_axiom_fallback_cap cap f =
  match cap with
  | None -> f ()
  | Some _ ->
      let saved = Stdlib.Domain.DLS.get seq_axiom_fallback_cap_key in
      Stdlib.Domain.DLS.set seq_axiom_fallback_cap_key cap;
      Exn.protect ~f ~finally:(fun () ->
          Stdlib.Domain.DLS.set seq_axiom_fallback_cap_key saved)

(* A per-domain replacement for the process-wide budget, for one caller's
   questions: [None] (the default) keeps the process-wide budget; [Some ms]
   asks the fallback with [ms] instead (raised or lowered), the cap above and
   each question's own budget still applying.  It never switches the fallback
   on: with the process-wide budget off, nothing is asked.  The fallback turns
   nothing but an undecided answer into [`Valid], so a caller that sets it
   changes only what it pays for an undecided question and which of those it
   proves. *)
let seq_axiom_fallback_base_key : int option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_seq_axiom_fallback_base base f =
  match base with
  | None -> f ()
  | Some _ ->
      let saved = Stdlib.Domain.DLS.get seq_axiom_fallback_base_key in
      Stdlib.Domain.DLS.set seq_axiom_fallback_base_key base;
      Exn.protect ~f ~finally:(fun () ->
          Stdlib.Domain.DLS.set seq_axiom_fallback_base_key saved)

(* the budget this domain's fallback has before its cap: the process-wide one,
   replaced by [with_seq_axiom_fallback_base]'s where that is set; [None] when
   the fallback is off *)
let seq_axiom_fallback_base_budget () =
  match Atomic.get seq_axiom_fallback_budget with
  | None -> None
  | Some global -> (
      match Stdlib.Domain.DLS.get seq_axiom_fallback_base_key with
      | Some base -> Some base
      | None -> Some global)

(* the budget a fallback asked now would get: the process-wide one (or this
   domain's replacement for it) under this domain's cap *)
let effective_seq_axiom_fallback_budget () =
  match
    ( seq_axiom_fallback_base_budget (),
      Stdlib.Domain.DLS.get seq_axiom_fallback_cap_key )
  with
  | None, _ -> None
  | budget, None -> budget
  | Some _, Some cap when cap <= 0 -> None
  | Some budget, Some cap -> Some (Int.min budget cap)

let seq_axiom_fallback_report () =
  sprintf
    "(z3-seq-axiom-fallback (budget %s) (asked %d) (declined %d) (proved %d) \
     (not-proved %d) (secs %.1f) (build-spent %d) (forked %d) (fork-lost %d) \
     (fork-unavailable %d))"
    (match Atomic.get seq_axiom_fallback_budget with
    | None -> "off"
    | Some ms -> sprintf "%d ms" ms)
    (Atomic.get seq_axiom_asked)
    (Atomic.get seq_axiom_declined)
    (Atomic.get seq_axiom_proved)
    (Atomic.get seq_axiom_not_proved)
    (Float.of_int (Atomic.get seq_axiom_micros) /. 1e6)
    (Atomic.get seq_axiom_build_spent)
    (Atomic.get seq_axiom_forked)
    (Atomic.get seq_axiom_fork_lost)
    (Atomic.get seq_axiom_fork_unavailable)

(* [answer] is the answer a validity question over [phi] got, asked with the
   budget [caller_timeout] (milliseconds, if any).  A decided one
   is returned as it is; an undecided one is returned as it is unless the
   fallback is on, [phi] mentions a sequence, and the axiomatised question is
   [unsat], in which case it becomes [`Valid].  Nothing else can come out of
   the fallback: it has no answer that carries a model. *)
(* With [COAR_SEQAX_TRACE] in the environment, each fallback question prints
   its outcome, its wall time and its budget on stderr, so that a proof lost
   to the budget can be told from one the axioms do not give. *)
let trace_seq_axiom_fallback =
  Stdlib.(Sys.getenv_opt "COAR_SEQAX_TRACE" <> None)

(* Whether the validity questions asked in this domain are first rewritten by
   [IntBinderSplit.rewrite] ([with_split_int_binders]; default [false]): every
   integer binder whose body holds an [ite] on [x < c] split at [c] and its
   upper part shifted to start at zero.  The rewrite is an equivalence in every
   model and adds no free variable, so a [`Valid] answer, an [`Invalid] model
   and the fallback's proof each mean what they meant for the question as
   given.  Applied by [check_valid], [check_valid_seq_as_array] and
   [with_seq_axiom_fallback], once per question.  Why: a read at [x - c] is not
   matched by a ground read at [k], so the instance [x := k + c] a proof needs
   is found, if at all, by model-based instantiation, and on one recorded
   question that happened or not with the spelling of a generated sort name and
   with the random seed. *)
let split_int_binders_key : bool Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> false)

let with_split_int_binders on f =
  if not on then f ()
  else
    let saved = Stdlib.Domain.DLS.get split_int_binders_key in
    Stdlib.Domain.DLS.set split_int_binders_key true;
    Exn.protect ~f ~finally:(fun () ->
        Stdlib.Domain.DLS.set split_int_binders_key saved)

let split_int_binders_here phi =
  if Stdlib.Domain.DLS.get split_int_binders_key then
    Common.PhaseTime.with_phase "int-binder-split" (fun () ->
        IntBinderSplit.rewrite_at IntBinderSplit.ladder_tally phi)
  else phi

let rec with_seq_axiom_fallback ~caller_timeout ~id fenv phi answer =
  with_seq_axiom_fallback_split ~caller_timeout ~id fenv
    (split_int_binders_here phi) answer

(* [with_seq_axiom_fallback] on a question already rewritten *)
and with_seq_axiom_fallback_split ~caller_timeout ~id fenv phi answer =
  match answer with
  | `Valid | `Invalid _ -> answer
  | _ -> (
      match effective_seq_axiom_fallback_budget () with
      | None -> answer
      | Some budget when SeqAxiomEncoding.mentions_seq phi -> (
          Atomic.incr seq_axiom_asked;
          let timeout =
            match caller_timeout with
            | Some ms -> Int.min ms budget
            | None -> budget
          in
          let started = Common.Clock.now_float () in
          let r = prove_valid_by_seq_axioms ~timeout ~id fenv phi in
          (let secs =
             Time_float.Span.to_sec
               (Time_float.diff (Common.Clock.now_float ()) started)
           in
           let here = Stdlib.Domain.DLS.get seq_axiom_secs_key in
           here := !here +. secs;
           ignore
             (Atomic.fetch_and_add seq_axiom_micros
                (Float.iround_towards_zero_exn (secs *. 1e6)));
           if trace_seq_axiom_fallback then
             prerr_endline
               (sprintf "[seq-axiom-fallback] %s after %.3f s (budget %d ms)"
                  (match r with
                  | SeqAxProved -> "proved"
                  | SeqAxNotProved reason -> "not proved: " ^ reason
                  | SeqAxDeclined reason -> "declined: " ^ reason)
                  secs timeout));
          match r with
          | SeqAxProved ->
              Atomic.incr seq_axiom_proved;
              `Valid
          | SeqAxNotProved reason ->
              Atomic.incr seq_axiom_not_proved;
              Debug.print
              @@ lazy (sprintf "[seq-axiom-fallback] not proved (%s)" reason);
              answer
          | SeqAxDeclined reason ->
              Atomic.incr seq_axiom_declined;
              Debug.print
              @@ lazy (sprintf "[seq-axiom-fallback] declined (%s)" reason);
              answer)
      | Some _ -> answer)
(* The public entry keeps its signature, which callers pass around as a
   first-class value; [check_sat_policy] is the same function with the
   function-value side channel exposed. *)
let check_sat ?(timeout = None) ?(fresh_solver = false) ~id fenv phis =
  check_sat_policy ~timeout ~fresh_solver ~id fenv phis

(* A quantified question asked first inside a scope of a pooled solver, under
   a short budget, and only when that leaves it undecided, as [ask] asks it.

   Contract.  With [enabled] false, with [phis] quantifier-free, or with a
   shape [may_not_return] refuses (Z3's own budget does not hold over it), the
   answer is [ask ()], asked once, and nothing else is asked.  Otherwise
   [check_sat ~scoped:true] is asked first with the smaller of [scoped_ms]
   and [timeout]: its [`Unsat] is the answer (no model of [phis] exists, as
   from any other ask), its [`Sat m] is the answer (a model Z3 gave for
   [phis], read as every [`Sat] of [check_sat] is read), and its [`Timeout]
   or [`Unknown] says nothing, after which the answer is [ask ()].  So only
   the order of the asks changes, and every answer is read as the single ask
   reads its own.  The second component says which path gave the answer;
   [on_scoped] is given the scoped ask's answer as soon as it is known.

   Why: on a pooled solver a quantified question is asserted outside any
   scope ([check_sat_base]), and in a context that has been pushed Z3 then
   answers with its bare [smt] tactic; the same question inside a scope goes
   to Z3's incremental core, which decided validation questions over
   sequences and datatypes in 0.1 s that the tactic did not decide in 5 s.
   The core is not better everywhere -- [forall x. exists y. y > x] is
   decided outside a scope and not inside one -- so the scoped ask comes
   first and short, and the unscoped one keeps its whole budget. *)
(* how many scoped asks [check_sat_scoped_first] made; read by the tests *)
let scoped_first_asked = Atomic.make 0

let check_sat_scoped_first ?(on_scoped = fun _ -> ()) ~enabled ~scoped_ms
    ~timeout ~id fenv phis ~ask =
  if
    (not enabled)
    || List.for_all phis ~f:Formula.is_quantifier_free
    || List.exists phis ~f:may_not_return
  then (ask (), `Not_asked)
  else
    let ms =
      match timeout with Some t -> Int.min t scoped_ms | None -> scoped_ms
    in
    Atomic.incr scoped_first_asked;
    let scoped =
      check_sat_without_retry ~scoped:true ~timeout:(Some (Int.max 1 ms)) ~id
        fenv phis
    in
    on_scoped scoped;
    match scoped with
    | `Unsat -> (`Unsat, `Scoped)
    | `Sat m -> (`Sat m, `Scoped)
    | `Timeout | `Unknown _ -> (ask (), `Fell_through)

(* ------------------------------------------------------------------
   Equalities between the factors of products, implied by a question's
   linear facts.

   [implied_factor_equalities ~timeout ~id fenv phi] returns
   [phi \/ t1 != u1 \/ ... \/ tk != uk], where each [ti = ui] is an equation
   between two integer terms that occur as the two non-numeral factors of
   products [x * y] in [phi], mention no variable bound in [phi], and is
   implied by the LINEAR FACTS of [phi]'s negation; [phi] itself, unchanged
   (physically), when there is none.

   The linear facts are the negations of the disjuncts of
   [Evaluator.elim_onepoint_and_split_binders phi] (an equivalent formula) that
   bind no variable, read no product of two non-numerals, convert no integer
   to a word and mention no bit-vector; each is implied by [not phi].  An
   equation is taken only when the solver answers [unsat] to the facts with
   [ti != ui], under [timeout] ms each, so every taken equation holds wherever
   [phi] is false.  Hence [phi] and the result are true at the same
   assignments in every model: where [phi] is false every [ti = ui] holds, so
   the added disjuncts are false too.  So any answer about the result -- a
   proof, a countermodel -- is an answer about [phi].  At most
   [max_factor_pairs] pairs are asked, in the order the factors first occur.

   Why: Z3's nonlinear integer arithmetic reasons about each product as a
   monomial over its variables, and two monomials [n * t] and [w * i] are not
   compared once the linear part forces [n = w] unless the equation is stated:
   on a bit-set obligation that fixes both [n] and [w] through
   [64 n - 64 < b <= 64 n] and [64 w - 64 < b <= 64 w], the question ran past
   30 s under two of three seeds, quantified or instantiated, and with
   [n = w] conjoined to its negation it was answered [unsat] in under 0.12 s
   under every seed. *)
let max_factor_pairs = 28

let implied_factor_equalities ~timeout ~id fenv phi =
  let is_numeral = function Term.FunApp (T_int.Int _, [], _) -> true | _ -> false in
  let nonlinear = function
    | Term.FunApp (T_int.Mul, [ t1; t2 ], _) ->
        (not (is_numeral t1)) && not (is_numeral t2)
    | _ -> false
  in
  let fvs = Formula.fvs_of phi in
  let factors =
    Formula.filtered_terms_of phi ~f:nonlinear
    |> Set.to_list
    |> List.concat_map ~f:(function
      | Term.FunApp (T_int.Mul, [ t1; t2 ], _) -> [ t1; t2 ]
      | _ -> [])
    |> List.filter ~f:(fun t ->
        let tvs = Term.fvs_of t in
        (not (Set.is_empty tvs))
        && Set.is_subset tvs ~of_:fvs
        && (try Stdlib.(Term.sort_of t = T_int.SInt) with _ -> false))
    |> List.stable_dedup ~compare:Stdlib.compare
  in
  let pairs =
    List.concat_mapi factors ~f:(fun i t ->
        List.filter_mapi factors ~f:(fun j u ->
            if j > i then Some (t, u) else None))
    |> fun l -> List.take l max_factor_pairs
  in
  if List.is_empty pairs then phi
  else
    let linear_fact d =
      Set.is_empty (Formula.quantified_sort_env_of d)
      && Set.is_empty (Formula.filtered_terms_of d ~f:nonlinear)
      && Set.is_empty
           (Formula.filtered_terms_of d ~f:(function
             | Term.FunApp (T_irb.IntToBV _, _, _) -> true
             | _ -> false))
      && not
           (Set.exists (Formula.term_sort_env_of d) ~f:(fun (_, s) ->
                match s with T_bv.SBV _ -> true | _ -> false))
    in
    let facts =
      Evaluator.elim_onepoint_and_split_binders phi
      |> Formula.disjuncts_of |> Set.to_list
      |> List.filter ~f:linear_fact
      |> List.map ~f:Formula.negate
    in
    if List.is_empty facts then phi
    else
      let eqs =
        List.filter pairs ~f:(fun (t, u) ->
            match
              check_sat ~timeout:(Some timeout) ~id fenv
                (Formula.mk_atom (T_bool.mk_neq t u) :: facts)
            with
            | `Unsat -> true
            | _ -> false)
      in
      if List.is_empty eqs then phi
      else
        Formula.or_of
          (phi
          :: List.map eqs ~f:(fun (t, u) ->
              Formula.mk_atom (T_bool.mk_neq t u)))

(* [is_sat] and [is_valid] answer [false] on Z3's unknown/timeout as well; use
   [check_sat]/[check_valid] (or [is_valid_exn]) wherever [false] would become
   a definite verdict.

   All four take [?timeout] and forward it, so a caller that needs a bound
   need not reach past the function it wants.  Nothing passes one here and
   nothing should be given one without measuring -- a budget on a query that
   terminates can turn an answer of 0.1 s into `unknown` and a hang -- but a
   caller that must not hang can ask, and a budget is in any case not a bound
   on every query: on a formula quantified over a sequence the
   call does not return whatever is passed, which is why the shape is checked
   before asking ([may_not_return]). *)
let is_sat ?timeout ~id fenv phi =
  match check_sat ?timeout ~id fenv [ phi ] with `Sat _ -> true | _ -> false

let check_valid ?timeout ?fresh_solver ~id fenv phi =
  let phi = split_int_binders_here phi in
  with_seq_axiom_fallback_split ~caller_timeout:(Option.join timeout) ~id fenv
    phi
  @@
  match check_sat ?timeout ?fresh_solver ~id fenv [ Formula.negate phi ] with
  | `Unsat -> `Valid
  | `Sat model -> `Invalid model
  | res -> res

(* whether [phi] converts an integer term other than a numeral to a word: the
   shape [check_valid_by_words] can act on *)
let reads_int_as_word phi =
  not
    (Set.is_empty
       (Formula.filtered_terms_of phi ~f:(function
         | Term.FunApp (T_irb.IntToBV _, [ Term.FunApp (T_int.Int _, [], _) ], _)
           ->
             false
         | Term.FunApp (T_irb.IntToBV _, [ _ ], _) -> true
         | _ -> false)))

(* [phi] asked for validity through its words ([int_to_bv_words_subst]): the
   negation with every bounded integer named by a bit-vector, its integer
   literals twinned over bit-vectors, and every remaining [int_to_bv m t]
   forgotten into a fresh word.  The negation so rewritten is weaker, so only
   [`Valid] (its [unsat]) is an answer about [phi]; everything else, and a
   question the rewrite leaves as it is, is [`Unknown].  Why: a validity
   question that mixes integer facts with bits read through [int_to_bv]
   (a bit set's index, its word [i div 64] and its bit [i mod 64]) is
   decided by neither Z3 5.1.0 nor cvc5 1.0.4 when the two halves meet only
   through the conversion, and its rewritten form, all of whose bit-level
   reasoning is over bit-vectors, was answered in 0.08 s where the original
   ran past 30 s. *)
(* [COAR_DUMP_WORDS=dir]: each words question's solver check is kept as
   [dir/wN_k.smt2] ([with_query_dump]), for replaying it outside the process.
   A diagnostic; nothing is written without the variable. *)
let words_dump_count = Atomic.make 0

(* [words_seq_as_arrays]: a words question is asked with its sequences read
   as arrays ([seq_reads_as_arrays]); process-wide once on. *)
let words_seq_as_arrays = Atomic.make false
let set_words_seq_as_arrays b = Atomic.set words_seq_as_arrays b

(* [seq_reads_as_arrays phis]: the conjuncts of [phis] (in negation normal
   form) with every read
   [seq.nth s i] and every length [seq.len s] of a sequence term [s] built
   from variables and selectors alone (no sequence operator) replaced by
   [select a_s i] and [l_s], one fresh array [a_s : Int -> E] and one fresh
   integer [l_s] per distinct such [s], with [0 <= l_s] added, a read of a
   store [seq.nth (store s k v) i] by [ite (0 <= i < l_s) (ite (i = k) v
   (select a_s i)) (select b i)] with one more fresh array [b] per distinct
   store and its length by [l_s]; every conjunct
   in which a sequence-sorted term is still left after that (a
   concatenation, an equation between sequences), or which binds a variable
   (embedded formulas are entered: a term-level [ite] condition is one), is
   dropped.

   Contract: the result is a weakening -- every model of [phis] gives one of
   the result by [a_s := fun i -> nth s i] (the value a model gives a read out
   of range included, since SMT-LIB leaves that read open and each model
   fixes it), [l_s := len s] and [b := fun i -> nth (store s k v) i] (a store
   keeps the length, and inside it reads [v] at [k] and [s] elsewhere), and
   dropping conjuncts only adds models -- so
   [unsat] of the result proves [phis] unsatisfiable, and nothing else may be
   read from it.  The fresh names avoid every free variable of [phis].

   Why: a words question reads its sequences only through ground reads and
   lengths, and its bit-level reasoning needs none of the sequence theory; Z3
   5.1.0's sequence solver gave up on two such questions of a bit-set
   obligation ("reached max unfolding") under some seeds and took 2-8 s under
   the others, while the same questions so weakened were [unsat] in 0.5-1 s
   under every seed. *)
let seq_reads_as_arrays phis =
  let fvs = Set.Poly.union_list (List.map phis ~f:Formula.fvs_of) in
  let fresh =
    let k = ref 0 in
    fun prefix ->
      let rec draw () =
        incr k;
        let v = Ident.Tvar (sprintf "%s!%d" prefix !k) in
        if Set.mem fvs v then draw () else v
      in
      draw ()
  in
  let rec plain = function
    | Term.Var _ -> true
    | Term.FunApp (T_dt.DTSel _, [ t ], _) -> plain t
    | _ -> false
  in
  let tbl = Hashtbl.Poly.create () in
  let key s elem =
    Hashtbl.find_or_add tbl s ~default:(fun () ->
        ( Term.mk_var (fresh "seqarr") (T_array.SArray (T_int.SInt, elem)),
          Term.mk_var (fresh "seqlen") T_int.SInt ))
  in
  let store_tbl = Hashtbl.Poly.create () in
  let store_key st elem =
    Hashtbl.find_or_add store_tbl st ~default:(fun () ->
        Term.mk_var (fresh "seqarr") (T_array.SArray (T_int.SInt, elem)))
  in
  let abstract t =
    match t with
    | Term.FunApp (T_seq.SqNth elem, [ s; i ], _) when plain s ->
        T_array.mk_select T_int.SInt elem (fst (key s elem)) i
    | Term.FunApp (T_seq.SqLen elem, [ s ], _) when plain s ->
        snd (key s elem)
    | Term.FunApp
        ( T_seq.SqNth elem,
          [ (Term.FunApp (T_seq.SqStore _, [ s; k; v ], _) as st); i ],
          _ )
      when plain s ->
        let a, l = key s elem in
        T_bool.mk_if_then_else
          (T_bool.of_formula
             (Formula.and_of
                [ Formula.leq (T_int.zero ()) i; Formula.lt i l ]))
          (T_bool.mk_if_then_else
             (T_bool.of_formula (Formula.eq i k))
             v
             (T_array.mk_select T_int.SInt elem a i))
          (T_array.mk_select T_int.SInt elem (store_key st elem) i)
    | Term.FunApp
        (T_seq.SqLen elem, [ Term.FunApp (T_seq.SqStore _, [ s; _; _ ], _) ], _)
      when plain s ->
        snd (key s elem)
    | t -> t
  in
  (* [exists_term p c]: some term of [c], inside embedded formulas too,
     satisfies [p] *)
  let exists_term p c =
    let found = ref false in
    ignore
      (Formula.map_term c ~f:(fun t ->
           if (not !found) && p t then found := true;
           t));
    !found
  in
  let seq_left =
    exists_term (fun t ->
        match Term.sort_of t with
        | T_seq.SSeq _ -> true
        | _ -> false
        | exception _ -> false)
  in
  let binds c =
    (not (Set.is_empty (Formula.quantified_sort_env_of c)))
    || exists_term
         (function
           | Term.LetTerm _ | Term.FunApp (T_array.ALambda _, _, _) -> true
           | Term.FunApp (T_bool.Formula phi, [], _) ->
               not (Set.is_empty (Formula.quantified_sort_env_of phi))
           | _ -> false)
         c
  in
  let kept =
    List.concat_map phis ~f:(fun phi ->
        Formula.conjuncts_list_of (Formula.nnf_of phi))
    |> List.filter_map ~f:(fun c ->
        if binds c then None
        else
          let c' = Formula.map_term c ~f:abstract in
          if seq_left c' then None else Some c')
  in
  kept
  @ List.map (Hashtbl.data tbl) ~f:(fun (_, l) ->
      Formula.mk_atom (T_int.mk_leq (T_int.zero ()) l))

let check_valid_by_words ?(timeout = None) ~id fenv phi =
  match int_to_bv_words_subst [ Formula.negate phi ] with
  | None -> `Unknown "no words to rewrite"
  | Some pre -> (
      let pre =
        if Atomic.get words_seq_as_arrays then
          let phis, picked = pre in
          (seq_reads_as_arrays phis, picked)
        else pre
      in
      let ask () =
        check_sat_base ~timeout ~fresh_solver:true ~pre ~id fenv
          [ Formula.negate phi ]
      in
      match
        match Sys.getenv "COAR_DUMP_WORDS" with
        | None -> ask ()
        | Some dir ->
            with_query_dump
              (sprintf "%s/w%d-%d" dir
                 (Atomic.fetch_and_add words_dump_count 1)
                 (Common.ForkGuard.self_pid ()))
              ask
      with
      | `Unsat -> `Valid
      | `Sat _ -> `Unknown "a model of the rewritten negation says nothing"
      | `Unknown r -> `Unknown r
      | `Timeout -> `Timeout)

let is_valid ?timeout ~id fenv phi =
  Debug.print @@ lazy "[Z3interface.is_valid]";
  match check_valid ?timeout ~id fenv phi with `Valid -> true | _ -> false

(* ------------------------------------------------------------------
   A refutation-only retry under a stronger strategy.

   [check_sat_by_elimination ~timeout ~id fenv phis] asks [phis] in a context
   made for this query alone (only the definitions the query reaches, the
   query in negation normal form, finite array-literal equalities expanded),
   with a solver built from the
   tactic [(then simplify der qe-light simplify smt)] in place of Z3's default
   strategy.  [der] eliminates a universally bound variable fixed by an
   equation ([forall x. x != t \/ P x] becomes [P t]), and [qe-light] does the
   same for cheap existential projections; a constraint whose premise names a
   quantified variable's value is decided so where the default strategy leaves
   it "incomplete quantifiers". These tactic rewrites preserve their input,
   but restricting the function environment is a separate relaxation unless
   the omitted equations admit the required model extension. Reachability
   does not establish that condition. Only refutation is used: an unsatisfiable
   retained context refutes the full one; Sat is not a full-context certificate.
   The native recursive-equation enforcement limitation remains separate.

   [timeout] (milliseconds) is Z3's own [timeout] parameter together with a
   [try_for] on the tactic: a Z3 call is not interruptible by the process's
   alarm, so the budget has to be the solver's.  A query [may_not_return] says
   the solver may never return on is not asked ([`Refused]).

   [smtlib2_out], when given, receives the query as SMT-LIB2 text in Z3's own
   printing of the assertions (declarations, datatypes and reached definitions
   included, headed by [(set-logic ALL)], with no [check-sat] command), so that
   a caller can put the same question to another solver or to a Z3 process,
   whose wall clock does bound it; it is filled whether or not Z3 is asked
   ([elimination_query_text] gives the text alone, asking nothing).  Only
   an [`Unsat] is conclusive for the caller; [`Sat] carries no model. *)
(* The solver [check_sat_by_elimination] (below) asks, with the query's
   assertions added, and the query's formulas after its rewriting. *)
let elimination_solver ~timeout ~id fenv phis =
  (* the rewrite whatever the linked library, because this query's text is
     also handed to a [z3] process, whose version need not be the library's *)
  let phis =
    List.map phis ~f:(fun phi ->
        Formula.nnf_of @@ expand_finite_array_eqs_always phi)
  in
  let fenv = fenv_reached_by fenv (Formula.and_of phis) in
  let cfg = [ ("model", "true") ] in
  let instance = get_instance id cfg (Hashtbl.Poly.create ()) in
  let ctx = instance.ctx in
  let dtenv =
    z3_dtenv_of_formula ~init:instance.dtenv ctx @@ Formula.and_of phis
  in
  let z3fenv = z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv dtenv in
  let exprs =
    List.map phis ~f:(fun phi ->
        of_formula_with_z3fenv ~id ctx [] [] z3fenv dtenv
        @@ FunEnv.defined_formula_of fenv phi)
  in
  let tactic =
    let t = Z3.Tactic.mk_tactic ctx in
    Z3.Tactic.try_for ctx
      (Z3.Tactic.and_then ctx (t "simplify") (t "der")
         [ t "qe-light"; t "simplify"; t "smt" ])
      timeout
  in
  let solver = Z3.Solver.mk_solver_t ctx tactic in
  let params = Z3.Params.mk_params ctx in
  Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout;
  Z3.Solver.set_parameters solver params;
  z3_solver_add solver exprs;
  (solver, phis)

let elimination_text solver =
  "(set-logic ALL)\n" ^ Z3.Solver.to_string solver ^ "\n"

let check_sat_by_elimination ~timeout ?smtlib2_out ~id fenv phis =
  let solver, phis = elimination_solver ~timeout ~id fenv phis in
  Option.iter smtlib2_out ~f:(fun out -> out := elimination_text solver);
  if List.exists phis ~f:may_not_return then `Refused
  else
    match z3_check solver [] with
    | UNSATISFIABLE -> `Unsat
    | SATISFIABLE -> `Sat
    | UNKNOWN -> (
        match Z3.Solver.get_reason_unknown solver with
        | "timeout" | "canceled" -> `Timeout
        | reason -> `Unknown reason)

(* The SMT-LIB2 text [check_sat_by_elimination ~smtlib2_out] would receive for
   [phis], without asking Z3 anything.  A caller that only wants the text must
   not get it by calling [check_sat_by_elimination] with a tiny budget: with
   [~timeout:1] the solver is still asked, and on a query over sequences
   (4.15.2, the negation of "every element of [s ++ [n + 1]] exceeds [n] when
   every element of [s] does") that call did not return within 90 to 900 s in
   most runs (four of five here), while the same query under a 5000 ms budget
   returned both times it was tried; why the 1 ms budget does not hold is not known.  The budget
   given to the solver here is never used, since nothing is asked. *)
let elimination_query_text ~id fenv phis =
  elimination_text @@ fst @@ elimination_solver ~timeout:1 ~id fenv phis

(* [dump_native_question ~id fenv phi], inside [with_query_dump prefix]: writes
   the negation of [phi] -- the satisfiability question whose [unsat] proves
   [phi] valid -- to [prefix_native<suffix>.smt2] in Z3's printing (in negation normal
   form, with finite array-literal equalities expanded, both equivalences),
   followed by [(check-sat)], asking nothing.  It is written whether or not
   [phi] is then asked natively, so a question [may_not_return] refuses (and
   that is therefore asked, if at all, only in the sequence-axiom form) can
   still be replayed as it stands.  A diagnostic: a no-op outside
   [with_query_dump], and a failure to print is written into the file rather
   than raised. *)
let dump_variant_rewrites =
  [
    ("onepoint", Evaluator.elim_onepoint_and_split_binders);
    ("onepoint_ctx", Evaluator.elim_onepoint_and_split_binders_contextual);
    ("seq_len_exists", Evaluator.elim_seq_existentials);
    ("read_concat", Evaluator.rewrite_seq_read_over_concat);
    ("prefix_concat", Evaluator.rewrite_seq_prefix_over_concat);
    ("simplify", fun phi -> Evaluator.simplify phi);
  ]

let rec dump_native_question ?(suffix = "") ~id fenv phi =
  match Stdlib.Domain.DLS.get query_dump with
  | None -> ()
  | Some (prefix, _) ->
      let data =
        try
          elimination_query_text ~id fenv [ Formula.negate phi ]
          ^ "(check-sat)\n"
        with exn when not (Common.Timer.is_async exn) ->
          "; not printed: " ^ Exn.to_string exn ^ "\n"
      in
      Out_channel.write_all (prefix ^ "_native" ^ suffix ^ ".smt2") ~data;
      (* [COAR_DUMP_VARIANTS=r1+r2,r3]: also the question rewritten by each
         composition of exact rewrites listed ([dump_variant_rewrites], each
         an equivalence in every model), as [prefix_native__r1+r2.smt2] *)
      if String.is_empty suffix then
        Option.iter (Sys.getenv "COAR_DUMP_VARIANTS") ~f:(fun vs ->
            List.iter (String.split ~on:',' vs) ~f:(fun v ->
                try
                  let phi' =
                    List.fold (String.split ~on:'+' v) ~init:phi
                      ~f:(fun phi n ->
                        (List.Assoc.find_exn ~equal:String.equal
                           dump_variant_rewrites n)
                          phi)
                  in
                  dump_native_question ~suffix:("__" ^ v) ~id fenv phi'
                with exn when not (Common.Timer.is_async exn) ->
                  Out_channel.write_all
                    (prefix ^ "_native__" ^ v ^ ".smt2")
                    ~data:("; not rewritten: " ^ Exn.to_string exn ^ "\n")))

(* [with_validity_dump ~var ~counter ~id fenv phi f]: with the environment
   variable [var] naming a directory, the validity question [phi] that [f ()]
   answers is kept as files there -- its native form ([dump_native_question])
   when the outcome is ["undecided"] and [native] (default; a caller that
   rewrites [phi] before asking passes [false] and dumps the asked form
   itself), and every check [f] makes ([with_query_dump]) under the prefix [qN], N
   drawn from [counter] -- and one line [qN outcome secs budget_ms text_len]
   is appended to [index.tsv], [outcome f's answer] naming the outcome.
   Without the variable it is [f ()].  A diagnostic for replaying a question
   outside the process that asked it. *)
let with_validity_dump ?(native = true) ~var ~counter ~id ~timeout ~outcome fenv phi f =
  match Sys.getenv var with
  | None -> f ()
  | Some dir ->
      let n = Atomic.fetch_and_add counter 1 in
      let name = sprintf "q%d-%d" n (Common.ForkGuard.self_pid ()) in
      let started = Common.Clock.now_float () in
      let r, secs =
        with_query_dump (sprintf "%s/%s" dir name) @@ fun () ->
        let r = f () in
        let secs =
          Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) started)
        in
        (* after the clock: printing builds a context of its own *)
        if native && String.equal (outcome r) "undecided" then
          dump_native_question ~id fenv phi;
        (r, secs)
      in
      Out_channel.with_file (dir ^ "/index.tsv") ~append:true ~f:(fun oc ->
          Out_channel.output_string oc
            (sprintf "%s\t%s\t%.3f\t%d\t%d\n" name (outcome r) secs timeout
               (String.length (Formula.str_of phi))));
      r

(* ------------------------------------------------------------------
   A concat-free sequence query asked as arrays plus a length.

   [seq.store] is expanded at this boundary into extraction and concatenation
   (the [SqStore] arm of [of_term]), because SMT-LIB sequences have no write,
   and Z3 (4.15.2) decides nothing about [seq.nth] over that expansion: the
   frame fact of a write times out at 20 s where cvc5 answers in 0.2 s.
   [Ast.SeqAsArray.translate] rewrites a formula whose sequence terms are
   variables, reads, lengths, writes, [seq.empty], [seq.unit] and [ite], and
   whose every read is range-guarded, into an EQUISATISFIABLE formula over an
   array and a length per sequence; its header states the fragment and the
   argument.  These entry points ask that translation first.

   CONTRACT.  The answer is the one the untranslated query would have if Z3
   decided it:
   - [`Unsat] of the translation is [`Unsat] of the input (equisatisfiable);
   - [`Sat] of the translation is returned with its model read back onto the
     input's sequence variables (each the word a_s[0..n_s-1]) and the
     translation's own names removed; if the model cannot be read back, the
     untranslated query is asked instead;
   - anything undecided, and any formula outside the fragment, is asked
     untranslated, with the caller's budget: an undecided translation can
     therefore cost the budget twice.
   The range entailment the translation needs is asked of Z3 with a 1 s
   budget and trusted only on [`Valid].  The caller decides whether to use
   these at all; nothing reaches them by default. *)
let seq_as_array_translated = Atomic.make 0
let seq_as_array_outside = Atomic.make 0
let seq_as_array_decided = Atomic.make 0

let seq_as_array_report () =
  sprintf "(z3-seq-as-array (translated %d) (outside %d) (decided %d))"
    (Atomic.get seq_as_array_translated)
    (Atomic.get seq_as_array_outside)
    (Atomic.get seq_as_array_decided)

let check_sat_seq_as_array ?(timeout = None) ?(fresh_solver = false) ~id fenv
    phis =
  let untranslated () = check_sat ~timeout ~fresh_solver ~id fenv phis in
  let entails hyps goal =
    match
      check_sat ~timeout:(Some 1000) ~id fenv
        [ Formula.and_of (Formula.mk_neg goal :: hyps) ]
    with
    | `Unsat -> true
    | _ -> false
  in
  match Ast.SeqAsArray.translate ~entails (Formula.and_of phis) with
  | Error reason ->
      if not (String.equal reason "no sequence") then (
        Atomic.incr seq_as_array_outside;
        Debug.print
        @@ lazy (sprintf "[z3:seq-as-array] asked untranslated: %s" reason));
      untranslated ()
  | Ok tr -> (
      Atomic.incr seq_as_array_translated;
      let asked =
        if fresh_solver then Formula.nnf_of tr.formula else tr.formula
      in
      match check_sat ~timeout ~fresh_solver ~id fenv [ asked ] with
      | `Unsat ->
          Atomic.incr seq_as_array_decided;
          `Unsat
      | `Sat model -> (
          match Ast.SeqAsArray.read_back tr model with
          | Some model ->
              Atomic.incr seq_as_array_decided;
              `Sat model
          | None -> untranslated ())
      | _ -> untranslated ())

let check_valid_seq_as_array ?timeout ?fresh_solver ~id fenv phi =
  let phi = split_int_binders_here phi in
  match
    check_sat_seq_as_array ?timeout ?fresh_solver ~id fenv
      [ Formula.negate phi ]
  with
  | `Unsat -> `Valid
  | `Sat model -> `Invalid model
  | res -> res

(* ------------------------------------------------------------------
   A select-only array query asked with each array an uninterpreted function.

   [Ast.ArrayAsFun.translate] rewrites a formula that reads its array
   variables only through full [select] chains (after read over write) into
   an EQUISATISFIABLE formula over one fresh function symbol per array; its
   header states the fragment and the argument.  Measured on the
   counterexample queries of a candidate that states a universal over the
   cells of two arrays: 8 of 8 reached a 10 s budget as arrays and were
   answered [sat] in at most 0.1 s as functions, and the 16 queries both
   encodings decided got the same answer in both.

   CONTRACT.  The answer is the one the untranslated query would have if Z3
   decided it:
   - [`Unsat] of the translation is [`Unsat] of the input;
   - [`Sat] of the translation is returned with each array variable given the
     array term its function's interpretation denotes (writes over a constant
     array, or nested [lambda]s when the interpretation's default depends on
     its argument) and the function names removed; when an interpretation
     cannot be read back, the untranslated query is asked instead;
   - anything undecided, and any formula outside the fragment, is asked
     untranslated with the caller's budget, so an undecided translation can
     cost the budget twice.
   The second component says which of those happened, for the caller's
   trace. *)
let arrays_as_functions_translated = Atomic.make 0
let arrays_as_functions_outside = Atomic.make 0
let arrays_as_functions_decided = Atomic.make 0
let arrays_as_functions_fallback = Atomic.make 0

let arrays_as_functions_report () =
  sprintf
    "(z3-arrays-as-functions (translated %d) (outside %d) (decided %d) \
     (fallback %d))"
    (Atomic.get arrays_as_functions_translated)
    (Atomic.get arrays_as_functions_outside)
    (Atomic.get arrays_as_functions_decided)
    (Atomic.get arrays_as_functions_fallback)

let check_sat_arrays_as_functions ?(timeout = None) ?(fresh_solver = false)
    ~id fenv phis =
  let untranslated () = check_sat ~timeout ~fresh_solver ~id fenv phis in
  match Ast.ArrayAsFun.translate (Formula.and_of phis) with
  | Error reason ->
      if not (String.equal reason "no array") then
        Atomic.incr arrays_as_functions_outside;
      (untranslated (), `Outside reason)
  | Ok tr -> (
      Atomic.incr arrays_as_functions_translated;
      let asked =
        if fresh_solver then Formula.nnf_of tr.formula else tr.formula
      in
      let fun_values = ref [] in
      match
        check_sat_policy ~timeout ~fresh_solver ~fun_values_out:fun_values ~id
          fenv [ asked ]
      with
      | `Unsat ->
          Atomic.incr arrays_as_functions_decided;
          (`Unsat, `Decided)
      | `Sat model -> (
          match Ast.ArrayAsFun.read_back tr model !fun_values with
          | Some model ->
              Atomic.incr arrays_as_functions_decided;
              (`Sat model, `Decided)
          | None ->
              Atomic.incr arrays_as_functions_fallback;
              (untranslated (), `Fallback "a function value was not read back"))
      | `Timeout ->
          Atomic.incr arrays_as_functions_fallback;
          (untranslated (), `Fallback "timeout")
      | `Unknown reason ->
          Atomic.incr arrays_as_functions_fallback;
          (untranslated (), `Fallback reason))

(* ------------------------------------------------------------------
   A query whose arrays are constrained cell by cell, asked with them
   eliminated.

   [Ast.ArrayPointwise.rewrite] splits the query into at most a few cases,
   whose disjunction is EQUISATISFIABLE with it, and in each eliminates an
   [Array Int Int] variable read only at ground indices and at the variable
   of a top-level universal; its header states the fragment and the argument.

   CONTRACT.  [`Unsat] when every case is [unsat]; [`Sat] with a case's model
   read back onto the query's own variables (an eliminated array as a
   [lambda]); [None] when the query is outside the fragment, when a case is
   undecided and none is [sat], or when a model is not read back -- the
   caller then asks the query as before, so an undecided rewrite can cost the
   budget twice.  Each case is asked under the caller's budget. *)
let array_pointwise_rewritten = Atomic.make 0
let array_pointwise_decided = Atomic.make 0

let check_sat_array_pointwise ?(timeout = None) ~id fenv phis =
  match Ast.ArrayPointwise.rewrite (Formula.and_of phis) with
  | Error reason -> (None, reason)
  | Ok r ->
      Atomic.incr array_pointwise_rewritten;
      let rec go undecided = function
        | [] -> if undecided then (None, "a case undecided") else (Some `Unsat, "unsat")
        | (c : Ast.ArrayPointwise.case) :: rest -> (
            match check_sat ~timeout ~id fenv [ c.formula ] with
            | `Unsat -> go undecided rest
            | `Sat model -> (
                match Ast.ArrayPointwise.read_back r c model with
                | Some m -> (Some (`Sat m), "sat")
                | None -> go true rest)
            | _ -> go true rest)
      in
      let res, why = go false r.cases in
      if Option.is_some res then Atomic.incr array_pointwise_decided;
      (res, why)

exception Unknown

let is_valid_exn ?timeout ~id fenv phi =
  match check_valid ?timeout ~id fenv phi with
  | `Valid -> true
  | `Invalid _ -> false
  | _ -> raise Unknown

(** [non_tracked] will be popped from solver when solving finished *)
(* ------------------------------------------------------------------
   Synthesising the quantifier prefix instead of fixing it.

   A template of the form [\ params. forall i_1..i_n. body] commits to the
   prefix before the solver sees it.  This asks the solver to choose it: the
   preamble below declares one boolean [Q_i] per index -- true for universal,
   false for existential -- and a function [perm] asserted to be a bijection
   of [1..n], and defines [QSAT Term] to be the prefix those bits select,
   applied to the indices in the order [perm] gives.  The marker a clause
   constraint carries, a vacuous [forall ((QSAT_HOLE Bool))], is rewritten
   into an application of [QSAT], and the remaining [forall]s become the
   [lambda]s that make the body an array [Term] can be read from.

   The choice comes back in the model, as the [Q_i] and as [perm] evaluated
   at each index, and the caller rebuilds the template's binders from it.

   Ported from an abandoned branch.  It goes through *text*: the constraint
   is printed, rewritten, concatenated with the preamble and re-parsed.  That
   is how it was written and it is kept, but it is a printer being used as a
   serialiser, and moving it to the AST API is the obvious next step for
   anyone reviving it. *)

(* DEFERRED RATHER THAN ABANDONED: this route exists to let a solver choose
   each quantifier's direction, and the near-term goal is the case where every
   index is universal.  See the note where the marker is produced for the
   question this must answer first.

   [n] index variables: the SMT-LIB preamble defining [QSAT] over them. *)
let qsat_preamble n =
  let args = String.concat ~sep:" " (List.init n ~f:(fun _ -> "Int")) in
  let qs =
    String.concat ~sep:"\n"
    @@ List.init n ~f:(fun i -> sprintf "(declare-const Q%d Bool)" (i + 1))
  in
  let perm =
    String.concat ~sep:"\n"
    @@ ("(declare-fun perm (Int) Int)"
        :: List.init n ~f:(fun i ->
               let i = i + 1 in
               sprintf "(assert (and (<= 1 (perm %d)) (<= (perm %d) %d)))" i i n)
       @ List.concat
         @@ List.init n ~f:(fun i ->
                List.init (n - i - 1) ~f:(fun j ->
                    sprintf "(assert (not (= (perm %d) (perm %d))))" (i + 1)
                      (i + j + 2))))
  in
  let selects =
    String.concat ~sep:" "
    @@ List.init n ~f:(fun i -> sprintf "(select X (perm %d))" (i + 1))
  in
  (* [Qgen_i] binds index [i] with the quantifier [Q_i] names and stores its
     value into [X]; [Qgen_{n+1}] reads [Term] at the permuted indices. *)
  let qgen_defs =
    (* [Qgen_i] mentions [Qgen_{i+1}], so the base case is written first and
       the steps after it in descending order; SMT-LIB has no forward
       reference. *)
    let base =
      sprintf
        "(define-fun Qgen%d ((Term FuncT) (X IntArray)) Bool\n  (select Term \
         %s))\n"
        (n + 1) selects
    in
    let step i =
      sprintf
        "(define-fun Qgen%d ((Term FuncT) (X IntArray)) Bool\n\
        \  (ite (= Q%d true)\n\
        \    (forall ((x Int)) (Qgen%d Term (store X %d x)))\n\
        \    (exists ((x Int)) (Qgen%d Term (store X %d x)))))\n"
        i i (i + 1) i (i + 1) i
    in
    String.concat ~sep:"\n"
    @@ (base :: List.rev (List.init n ~f:(fun i -> step (i + 1))))
  in
  String.concat ~sep:"\n"
    [
      (* the decoder reads the count back from here rather than being told *)
      sprintf "(define-const |#number-of-quantifiers| Int %d)" n;
      "";
      "(define-sort IntArray () (Array Int Int))";
      sprintf "(define-sort FuncT () (Array %s Bool))" args;
      "";
      qs;
      "";
      perm;
      "";
      qgen_defs;
      "";
      "(define-fun QSAT ((Term FuncT)) Bool\n  (Qgen1 Term ((as const \
       IntArray) 0)))";
    ]

(* The marker the constraint generator leaves, turned into an application of
   [QSAT], and every other binder into the lambda it has to be for [Term] to
   be an array. *)
(* DUBIOUS: a blind textual rewrite of the PRINTED query. It turns any
   [(forall ] into a [(lambda ], not only the ones this route put there, so
   it is safe only because nothing else prints a query through it. This
   belongs on the AST. *)
let replace_qsat_hole str =
  Str.global_replace (Str.regexp_string "(forall ") "(lambda "
  @@ Str.global_replace
       (Str.regexp_string "forall ((QSAT_HOLE Bool))")
       "QSAT" str

let incr_check_sat_unsat_core ~id ?(enable = true) ?(z3str3 = false)
    ?(timeout = None) ?(non_tracked = Set.Poly.empty)
    (* Per-unknown count of index variables whose quantifier the solver is to
       choose.  Empty -- which is every caller that does not ask for it --
       leaves the constraints asserted directly, as before.  Non-empty takes
       the textual route through [qsat_preamble]: the preamble can define only
       one [QSAT], so the count used is the largest, where the branch this
       comes from read it at one hardcoded unknown name. *)
      ?(qvars = Map.Poly.empty)
    (* A budget in milliseconds for asking the same question first of a fresh
       solver that sees it once, with every tracked label asserted rather than
       assumed.  0 -- every caller that does not ask -- asks only the
       incremental solver, as before.

       Why: a solver that has been pushed or given assumptions is in Z3's
       incremental mode, which skips the preprocessing tactics a one-shot check
       runs (solving the equations that pin a coefficient, propagating values).
       On template-coefficient queries over many witness templates the
       incremental check is heavy-tailed -- the same query answered [sat] in
       under a second one-shot took 16-23 s, or did not return within 20 s,
       under three seeds incrementally -- so the one-shot attempt is tried
       first under this budget.

       Only a [sat] from it is used, and that is sound: the fresh solver holds
       every assertion of the incremental one and, besides the labels the
       incremental check assumes, may only force further Boolean constants
       true (any top-level [b => e] with [b] a Boolean constant is read as a
       tracked assertion), so its model satisfies the incremental question.
       Anything else -- [unsat], which needs the incremental solver's core,
       [unknown], a timeout or a Z3 error -- falls through to the incremental
       check unchanged.  Not used on the [QSAT] route. *)
    ?(oneshot_first_ms = 0)
    (* Z3's [smt.arith.solver] for this query and the one-shot attempt (see
       [arith_solver_key]); [None] leaves the parameter unset.  A caller that
       sets it sets it on every call to one solver, from the first, since the
       theory is fixed when the solver's core is first set up. *)
    ?(arith_solver = None)
    (* [true] when [labeled_constr_map] is already in [solver]: a re-ask of
       a query that timed out, whose tracked constraints the first ask
       asserted and left there.  Nothing is asserted again, so the question
       is the one asked before; the map is still read to restrict a model to
       the query.  The untracked constraints are pushed and popped around
       each check, so they are given again as before. *)
    ?(asserted = false)
    (* [Some labels]: ask the question of a fresh solver instead of [solver].
       [labels] holds every label tracked in [solver] so far, and each label
       this call tracks is added to it, so the caller keeps one list per solver
       and empties it when it replaces the solver.  The fresh solver gets every
       assertion of [solver] -- each tracked constraint as the implication
       [label => e] Z3 keeps, the untracked ones of this call as they are -- and
       is checked under the labels as assumptions: the same question, with the
       same models and the same unsat cores over the same labels, asked of a
       solver that carries nothing from the earlier checks.

       Why: the synthesis query is asked again and again of one solver as
       examples are added, and on quantified constraints (a parametric example
       read under its universal) Z3's state from the earlier checks can make a
       later check of a few more constraints fail: on one input a question a
       fresh solver answers [sat] in 1-2 s (five seeds) came back
       [unknown (incomplete (theory array))] after 7.6 s, and the next one
       [canceled] at its 16 s budget, in the solver that had answered the
       questions before it.  The fresh solver internalises the whole query on
       every check, which is the price.  [None] -- every caller that does not
       ask -- checks [solver] itself, as before.  Not used on the [QSAT]
       route. *)
    ?(fresh_labels : Z3.Expr.expr list ref option)
    (* with [fresh_labels]: [true] asks [solver] first and the fresh solver
       only when [solver] leaves the question undecided ([unknown], a timeout,
       a Z3 error); [false] asks only the fresh one *)
    ?(fresh_after_undecided = false) solver ctx fenv dtenv
    labeled_constr_map =
  let oneshot_sat () =
    let fresh = Z3.Solver.mk_solver ctx None in
    let params = Z3.Params.mk_params ctx in
    Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "model") true;
    add_arith_solver_param ctx params arith_solver;
    let budget =
      match timeout with
      | None -> oneshot_first_ms
      | Some t -> Int.min t oneshot_first_ms
    in
    Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") budget;
    Z3.Solver.set_parameters fresh params;
    let earlier = Z3.Solver.get_assertions solver in
    Z3.Solver.add fresh earlier;
    List.iter earlier ~f:(fun e ->
        if Z3.Boolean.is_implies e then
          match Z3.Expr.get_args e with
          | label :: _ when Z3.Expr.is_const label && Z3.Boolean.is_bool label
            ->
              Z3.Solver.add fresh [ label ]
          | _ -> ());
    match try Ok (z3_check fresh []) with Z3.Error msg -> Error msg with
    | Ok Z3.Solver.SATISFIABLE -> z3_solver_get_model fresh
    | _ -> None
  in
  let f () =
    let params = Z3.Params.mk_params ctx in
    Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "model") true;
    if enable then
      Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "unsat_core") true;
    Z3.Params.add_symbol params
      (Z3.Symbol.mk_string ctx "smt.string_solver")
      (Z3.Symbol.mk_string ctx (if z3str3 then "z3str3" else "seq"));
    add_arith_solver_param ctx params arith_solver;
    (match timeout with
    | None -> ()
    | Some timeout ->
        Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout);
    Z3.Solver.set_parameters solver params;
    (* REACHABLE ON THE DEFAULT PATH, and 0 there: [qvars] is empty unless a
       caller asks for the QSAT route, so the [else] arms below are the two
       this function had before, unchanged. *)
    let qsat_arity =
      (* The preamble defines one [QSAT], over [Array Int^n Bool] for a single
         [n], and the marker every constraint carries is the same word, so a
         query holding two unknowns that want *different* counts has no way to
         give each its own.  Taking the largest, which is what this did, builds
         the smaller one's body as an array of the wrong arity and reads it at
         indices it does not have -- silently, since the query still parses.
         Refuse instead: it is a query nobody can have asked for on purpose,
         and a wrong answer here is indistinguishable from a right one. *)
      match
        List.dedup_and_sort ~compare:Int.compare
        @@ List.filter ~f:(fun n -> n > 0)
        @@ Map.Poly.data qvars
      with
      | [] -> 0
      | [ n ] -> n
      | ns ->
          failwith
          @@ sprintf
               "cannot synthesise quantifier prefixes of %d different lengths                 (%s) in one query: the preamble defines a single QSAT"
               (List.length ns)
               (String.concat_map_list ~sep:", " ns ~f:Int.to_string)
    in
    if asserted then ()
    else if qsat_arity > 0 then begin
      (* Each constraint becomes a definition of a boolean [Formula-<label>]
         whose body went through the marker rewrite, and the label tracks that
         constant rather than the constraint, so an unsat core still names the
         labels the caller gave. *)
      let formula_const label =
        Z3.Expr.mk_const_s ctx ("Formula-" ^ label) (Z3.Boolean.mk_sort ctx)
      in
      let defs = ref [] and consts = ref [] and tracked = ref [] in
      let free = ref Set.Poly.empty in
      Map.Poly.iteri labeled_constr_map ~f:(fun ~key:label ~data:phi ->
          if Formula.is_true phi then ()
          else begin
            let z3_expr = of_formula_with_z3fenv ~id ctx [] [] fenv dtenv phi in
            free := Set.union !free (Formula.tvs_of phi);
            let decl = formula_const label in
            defs :=
              sprintf "(assert (= %s %s))" (Z3.Expr.to_string decl)
                (replace_qsat_hole (Z3.Expr.to_string z3_expr))
              :: !defs;
            consts := Z3.Expr.to_string decl :: !consts;
            tracked := (decl, Z3.Boolean.mk_const_s ctx label) :: !tracked
          end);
      let query =
        String.concat ~sep:"\n"
          [
            String.concat_map_list ~sep:"\n" !consts ~f:(fun c ->
                sprintf "(declare-const %s Bool)" c);
            String.concat_map_list ~sep:"\n" (Set.to_list !free) ~f:(fun x ->
                sprintf "(declare-const |%s| Int)" (Ident.name_of_tvar x));
            "";
            qsat_preamble qsat_arity;
            "";
            String.concat ~sep:"\n" !defs;
          ]
      in
      Debug.print @@ lazy (sprintf "[qsat] query:\n%s" query);
      Z3.Solver.add solver @@ Z3.AST.ASTVector.to_expr_list
      @@ Z3.SMT.parse_smtlib2_string ctx query [] [] [] [];
      if enable then
        List.iter !tracked ~f:(fun (decl, label) ->
            z3_solver_assert_and_track solver decl label)
    end
    else if enable then
      Map.Poly.iteri labeled_constr_map ~f:(fun ~key:label ~data:phi ->
          if Formula.is_true phi then ()
          else
            if Lazy.force ConvertCensus.on then ConvertCensus.run phi;
            let z3_expr =
              Common.PhaseTime.with_phase "convert" (fun () ->
                  of_formula_with_z3fenv ~id ctx [] [] fenv dtenv phi)
            in
            Debug.print
            @@ lazy
                 (sprintf "assert and track: [%s] %s" label (Formula.str_of phi));
            let label = Z3.Boolean.mk_const_s ctx label in
            Option.iter fresh_labels ~f:(fun r -> r := label :: !r);
            Common.PhaseTime.with_phase "track" (fun () ->
                z3_solver_assert_and_track solver z3_expr label))
    else
      z3_solver_add solver
      @@ List.filter_map (Map.Poly.data labeled_constr_map) ~f:(fun phi ->
          if Formula.is_true phi then None
          else
            let z3_expr = of_formula_with_z3fenv ~id ctx [] [] fenv dtenv phi in
            Debug.print @@ lazy (sprintf "assert: %s" (Formula.str_of phi));
            Some z3_expr);
    if not @@ Set.is_empty non_tracked then (
      Z3.Solver.push solver;
      if false then print_endline @@ Z3.Solver.to_string solver;
      Z3.Solver.add solver @@ Set.to_list
      @@ Set.Poly.map non_tracked
           ~f:(of_formula_with_z3fenv ~id ctx [] [] fenv dtenv));
    (* the solver the question is asked of, and read from afterwards *)
    let fresh () =
      match fresh_labels with
      | Some labels when qsat_arity = 0 && enable ->
          let fresh = Z3.Solver.mk_solver ctx None in
          Z3.Solver.set_parameters fresh params;
          Z3.Solver.add fresh (Z3.Solver.get_assertions solver);
          `Fresh (fresh, !labels)
      | _ -> `Same
    in
    let asked = ref (if fresh_after_undecided then `Same else fresh ()) in
    let asked_solver () =
      match !asked with `Fresh (s, _) -> s | `Same -> solver
    in
    let check_asked () =
      match !asked with
      | `Fresh (fresh, labels) -> z3_check fresh labels
      | `Same -> z3_check solver []
    in
    (* the fallback: a question [solver] left undecided asked once more of a
       fresh solver; a decided answer is kept as it is *)
    let check_asked () =
      let undecided_then_fresh () =
        match fresh () with
        | `Same -> None
        | f ->
            Common.PhaseTime.event "synthesis/fresh-after-undecided";
            asked := f;
            Some (check_asked ())
      in
      if not fresh_after_undecided then check_asked ()
      else
        match check_asked () with
        | Z3.Solver.UNKNOWN -> (
            match undecided_then_fresh () with Some r -> r | None -> UNKNOWN)
        | r -> r
        | exception Z3.Error msg -> (
            match undecided_then_fresh () with
            | Some r -> r
            | None -> raise (Z3.Error msg))
    in
    let ret =
      (* Z3 can give up on a query by raising rather than by answering
         [unknown]: a synthesis query whose constraints reach Z3's own size
         limits raises [Z3.Error "Overflow encountered when expanding
         vector"] from [check].  That is a failure to decide this one query,
         not an internal error of the caller, so it is reported as [unknown]
         with Z3's message (and a cancellation as a timeout); the scope pushed
         above is still popped below.  Only [Z3.Error] is caught, so the
         timer's asynchronous exceptions pass through. *)
      match
        match
          if oneshot_first_ms > 0 && qsat_arity = 0 then oneshot_sat ()
          else None
        with
        | Some model -> Ok (`Oneshot model)
        | None -> (
            try
              Ok
                (`Checked (check_asked ()))
            with Z3.Error msg -> Error msg)
      with
      | Error ("canceled" | "timeout") -> `Timeout
      | Error msg -> `Unknown ("Z3 error: " ^ msg)
      | Ok (`Oneshot model) ->
          `Sat
            (restrict_model_to_query
               (Map.Poly.data labeled_constr_map @ Set.to_list non_tracked)
            @@ model_of ctx dtenv model)
      | Ok (`Checked Z3.Solver.SATISFIABLE) -> (
          match z3_solver_get_model (asked_solver ()) with
          | Some model ->
              (* as in [check_sat]: a pooled solver's model can carry a name
                 this query never asked about, and a consumer that turns the
                 model into a substitution is keyed by name *)
              `Sat
                (restrict_model_to_query
                   (Map.Poly.data labeled_constr_map @ Set.to_list non_tracked)
                @@ model_of ctx dtenv model)
          | None -> `Unknown "model generation is not enabled?")
      | Ok (`Checked UNSATISFIABLE) ->
          if enable then (
            let unsat_keys =
              List.map ~f:Z3.Expr.to_string
              @@ z3_solver_get_unsat_core (asked_solver ())
            in
            Debug.print @@ lazy "unsat cores:";
            List.iter unsat_keys ~f:(fun unsat_key ->
                Debug.print @@ lazy unsat_key);
            `Unsat unsat_keys)
          else `Unsat [] (* ToDo: Dummy *)
      | Ok (`Checked UNKNOWN) -> (
          match Z3.Solver.get_reason_unknown (asked_solver ()) with
          | "timeout" | "canceled" -> `Timeout
          | reason ->
              if false then print_endline reason;
              `Unknown reason)
    in
    if not @@ Set.is_empty non_tracked then Z3.Solver.pop solver 1;
    ret
  in
  if true then f ()
  else
    match timeout with
    | None -> f ()
    | Some tm ->
        if tm = 0 then `Timeout (* times out immediately *)
        else
          Timer.enable_timeout (tm / 1000) Fn.id ignore f
            (fun _ res -> res)
            (fun _ -> function Timer.Timeout -> `Timeout | e -> raise e)

let check_sat_unsat_core ~id ?(z3str3 = false) ?(timeout = None) fenv
    pvar_clause_map =
  let ctx =
    let cfg = [ ("model", "true"); ("unsat_core", "true") ] in
    let cfg = if validate then cfg @ validate_cfg else cfg in
    let cfg =
      match timeout with
      | None -> cfg
      | Some timeout -> cfg @ [ ("timeout", string_of_int timeout) ]
    in
    Z3.mk_context cfg
  in
  let dtenv =
    z3_dtenv_of_formula ctx @@ Formula.and_of @@ List.map ~f:snd
    @@ Map.Poly.to_alist pvar_clause_map
  in
  let solver = Z3.Solver.mk_solver ctx None in
  let fenv =
    z3_fenv_of ~id ctx [] []
      (fenv_for_query fenv (Map.Poly.data pvar_clause_map))
      dtenv
  in
  (match timeout with
  | None -> ()
  | Some timeout ->
      let params = Z3.Params.mk_params ctx in
      Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout;
      Z3.Solver.set_parameters solver params);
  incr_check_sat_unsat_core ~id ~z3str3 ~timeout solver ctx fenv dtenv
    pvar_clause_map

let max_smt_z3 ctx dtenv hard soft =
  let optimizer = Z3.Optimize.mk_opt ctx in
  Z3.Optimize.add optimizer hard;
  Map.Poly.iteri soft ~f:(fun ~key ~data ->
      List.iter data ~f:(fun (expr, weight) ->
          ignore
          @@ Z3.Optimize.add_soft optimizer expr (string_of_int weight)
               (Z3.Symbol.mk_string ctx key)));
  match z3_opt_check optimizer with
  | SATISFIABLE ->
      let open Option.Monad_infix in
      Z3.Optimize.get_model optimizer >>= fun model ->
      let num_sat =
        Map.Poly.fold soft ~init:0 ~f:(fun ~key:_ ~data sum ->
            List.fold data ~init:sum ~f:(fun sum (expr, weight) ->
                sum
                +
                match Z3.Model.eval model expr true with
                | None -> 0
                | Some e -> if Z3.Boolean.is_true e then weight else 0))
      in
      Some (num_sat, model_of ctx dtenv model)
  | _ -> None

let max_smt ~id fenv hard soft =
  let cfg = [ ("MODEL", "true") (* ("well_sorted_check", "true"); *) ] in
  let ctx = Z3.mk_context cfg in
  let soft_phi =
    Map.Poly.to_alist soft |> List.map ~f:snd |> List.join |> List.map ~f:fst
    |> Formula.and_of
  in
  let dtenv = z3_dtenv_of_formula ctx @@ Formula.and_of (soft_phi :: hard) in
  let hard =
    List.map hard ~f:(of_formula_with_z3fenv ~id ctx [] [] fenv dtenv)
  in
  let soft =
    Map.Poly.map soft
      ~f:
        (List.map ~f:(fun (phi, weight) ->
             (of_formula_with_z3fenv ~id ctx [] [] fenv dtenv phi, weight)))
  in
  max_smt_z3 ctx dtenv hard soft

(** ToDo: use MaxSMT instead *)
let max_smt_of ~id fenv num_ex phis =
  let fenv = fenv_for_query fenv phis in
  let cfg = [ ("unsat_core", "true") ] in
  let instance = get_instance id cfg instance_pool in
  let ctx = instance.ctx in
  instance.dtenv <-
    z3_dtenv_of_formula ~init:instance.dtenv ctx @@ Formula.and_of phis;
  instance.fenv <-
    z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv instance.dtenv;
  let dtenv = instance.dtenv in
  let fenv = instance.fenv in
  let solver = instance.solver in
  let name_map0 =
    List.map phis ~f:(of_formula_with_z3fenv ~id ctx [] [] fenv dtenv)
    |> List.foldi ~init:Map.Poly.empty ~f:(fun i map phi ->
        let name = "#S_" ^ string_of_int i in
        (* Tracking literals must not alias variables in the input formula. *)
        let label = Z3.Expr.mk_fresh_const ctx name (Z3.Boolean.mk_sort ctx) in
        Map.Poly.update map label ~f:(function None -> phi | Some x -> x))
  in
  (* greedy MaxSMT: assert all remaining soft constraints; on unsat drop one
     from the core and retry; on sat record the model and continue with the
     constraints that were dropped, until [num_ex] models or nothing is left.
     The solver must be reset *before* asserting (it used to be reset after,
     so every check ran on an empty solver and produced an empty model). *)
  let rec inner num_ex models ignored name_map =
    if num_ex <= 0 || Map.Poly.is_empty name_map then models
    else (
      z3_solver_reset solver;
      Map.Poly.iteri name_map ~f:(fun ~key ~data ->
          z3_solver_assert_and_track solver data key);
      match z3_check solver [] with
      | Z3.Solver.SATISFIABLE -> (
          match z3_solver_get_model solver with
          | None -> models
          | Some model ->
              let models' =
                Set.add models
                  (restrict_model_to_query phis @@ model_of ctx dtenv model)
              in
              let name_map' =
                Map.Poly.filter_keys ~f:(Set.mem ignored) name_map0
              in
              inner (num_ex - 1) models' Set.Poly.empty name_map')
      | UNSATISFIABLE -> (
          match z3_solver_get_unsat_core solver with
          | [] -> models
          | ucore :: _ ->
              inner num_ex models (Set.add ignored ucore)
                (Map.Poly.remove name_map ucore))
      | UNKNOWN -> models)
  in
  (* The instance may already be registered in the pool. An exception during
     checking or model decoding must not leave its tracked assertions behind. *)
  let finally () =
    z3_solver_reset solver;
    back_instance ~reset:ignore instance_pool id instance
  in
  match inner num_ex Set.Poly.empty Set.Poly.empty name_map0 with
  | ret ->
      finally ();
      ret
  | exception e ->
      finally ();
      raise e

let check_opt_z3 ~max ctx dtenv phis obj =
  let optimizer = Z3.Optimize.mk_opt ctx in
  Z3.Optimize.add optimizer phis;
  let handle = Z3.Optimize.(if max then maximize else minimize) optimizer obj in
  match z3_opt_check optimizer with
  | SATISFIABLE ->
      let open Option.Monad_infix in
      Z3.Optimize.get_model optimizer >>= fun model ->
      let lower =
        try Some (Z3.Optimize.get_lower handle |> term_of ctx [] [] dtenv)
        with exn_ when not (Common.Timer.is_async exn_) -> None
      in
      let upper =
        try Some (Z3.Optimize.get_upper handle |> term_of ctx [] [] dtenv)
        with exn_ when not (Common.Timer.is_async exn_) -> None
      in
      Some (lower, upper, model_of ctx dtenv model)
  | _ -> None

let check_opt ~id fenv phis ~max obj =
  let ctx =
    let cfg =
      let cfg = [ ("model", "true") ] in
      if validate then cfg @ validate_cfg else cfg
    in
    Z3.mk_context cfg
  in
  let dtenv = z3_dtenv_of_formula ctx @@ Formula.and_of phis in
  let fenv =
    fenv_for_query fenv (Formula.eq obj obj :: phis)
  in
  let z3fenv = z3_fenv_of ~id ctx [] [] fenv dtenv in
  debug_print_z3_input phis;
  let phis =
    List.map phis ~f:(of_formula_with_z3fenv ~id ctx [] [] z3fenv dtenv)
  in
  let obj =
    of_term ~id ctx [] [] (z3_fenv_of ~id ctx [] [] fenv dtenv) dtenv obj
  in
  check_opt_z3 ~max ctx dtenv phis obj

let penv_of phi ctx dtenv =
  Formula.pred_sort_env_of phi
  |> Set.to_list
  |> List.map ~f:(pred_decl_of ctx dtenv)

(* satisfiability of [phis] with their predicate variables as uninterpreted
   functions (declared from [pred_sort_env_of]); used by the witness checker's
   consequence checks "original clauses /\ definitions => preprocessed
   clause" *)
let check_sat_with_preds ?(timeout = None) ~id fenv phis =
  let fenv = fenv_for_query fenv phis in
  let cfg = [ ("model", "true") ] in
  let instance = get_instance id cfg instance_pool in
  let ctx = instance.ctx in
  let phi = Formula.and_of phis in
  instance.dtenv <- z3_dtenv_of_formula ~init:instance.dtenv ctx phi;
  instance.fenv <-
    z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv instance.dtenv;
  let penv = penv_of phi ctx instance.dtenv in
  let solver = Z3.Solver.mk_simple_solver ctx in
  (match timeout with
  | Some ms ->
      let params = Z3.Params.mk_params ctx in
      Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") ms;
      Z3.Solver.set_parameters solver params
  | None -> ());
  let exprs =
    List.map phis
      ~f:(of_formula_with_z3fenv ~id ctx [] penv instance.fenv instance.dtenv)
  in
  match z3_check solver exprs with
  | Z3.Solver.UNSATISFIABLE -> `Unsat
  | Z3.Solver.SATISFIABLE -> `Sat
  | Z3.Solver.UNKNOWN -> `Unknown

(** assume that [phi] is alpha-renamed *)
let z3_simplify ~id fenv phi =
  let fenv = fenv_for_query fenv [ phi ] in
  let cfg = [ ("model", "true") ] in
  let instance = get_instance id cfg instance_pool in
  let ctx = instance.ctx in
  instance.dtenv <- z3_dtenv_of_formula ~init:instance.dtenv ctx phi;
  instance.fenv <-
    z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv instance.dtenv;
  let dtenv = instance.dtenv in
  let fenv = instance.fenv in
  let penv = penv_of phi ctx dtenv in
  let tenv =
    let lenv = Map.Poly.to_alist @@ Formula.let_sort_env_of phi in
    lenv @ Set.to_list @@ Formula.term_sort_env_of phi
  in

  let symplify_params = Z3.Params.mk_params ctx in
  Z3.Params.add_bool symplify_params (Z3.Symbol.mk_string ctx "elim_ite") true;
  Z3.Params.add_bool symplify_params
    (Z3.Symbol.mk_string ctx "push_ite_arith")
    true;

  let rec inner = function
    | Formula.LetFormula (v, sort, def, body, info) ->
        let def' =
          if Stdlib.(sort = T_bool.SBool) then
            T_bool.of_formula @@ inner @@ Formula.of_bool_term def
          else def
        in
        Formula.mk_let_formula ~info v sort def' (inner body)
    | phi ->
        phi
        |> (fun phi ->
        if false then print_endline @@ "before: " ^ Formula.str_of phi ^ "\n";
        phi)
        |> of_formula_with_z3fenv ~id ctx tenv penv fenv dtenv
        |> Fn.flip Z3.Expr.simplify @@ Some symplify_params
        |> formula_of ctx (List.rev tenv) penv dtenv
        |> Evaluator.simplify
        |> fun phi ->
        if false then print_endline @@ "after: " ^ Formula.str_of phi ^ "\n";
        phi
  in
  let ret = inner phi in
  back_instance ~reset:ignore instance_pool id instance;
  ret

let qelim ?(timeout = None) ~id ~fenv phi =
  let fenv = fenv_for_query fenv [ phi ] in
  Debug.print @@ lazy "[Z3interface.qelim]";
  if
    (not (Formula.is_quantifier_free phi))
    && Formula.is_fun_quantifier_free phi
    && Set.for_all (Formula.funsyms_of phi) ~f:(function
      | T_int.Power | T_real.RPower -> false
      | fsym -> not (T_bv.is_bv_fsym fsym))
    && Set.for_all (Formula.predsyms_of phi) ~f:(T_bv.is_bv_psym >> not)
  then (
    Debug.print @@ lazy (sprintf "[z3:qelim] %s" (Formula.str_of phi));
    let cfg = [ ("model", "true") ] in
    let instance = get_instance id cfg instance_pool in
    let ctx = instance.ctx in
    let goal =
      Z3.Goal.mk_goal ctx false false false
      (*instance.goal*)
    in
    instance.dtenv <- z3_dtenv_of_formula ~init:instance.dtenv ctx phi;
    instance.fenv <-
      z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv instance.dtenv;
    let symplify_params = Z3.Params.mk_params ctx in
    let penv = penv_of phi ctx instance.dtenv in
    Z3.Params.add_bool symplify_params (Z3.Symbol.mk_string ctx "elim_ite") true;
    let qe_params = Z3.Params.mk_params ctx in
    Z3.Params.add_bool qe_params
      (Z3.Symbol.mk_string ctx "eliminate_variables_as_block")
      true;
    let expr =
      of_formula_with_z3fenv ~id ctx [] penv instance.fenv instance.dtenv phi
    in
    Debug.print @@ lazy ("[qelim] input: " ^ Z3.Expr.to_string expr);
    try
      z3_goal_add goal [ expr ];
      let g =
        let tactic =
          let tactic = Z3.Tactic.mk_tactic ctx "qe" in
          match timeout with
          | None -> tactic
          | Some timeout -> Z3.Tactic.try_for ctx tactic timeout
        in
        Z3.Goal.as_expr
        @@ Z3.Tactic.ApplyResult.get_subgoal
             (Z3.Tactic.apply tactic goal (Some qe_params))
             0
      in
      let expr = Z3.Expr.simplify g (Some symplify_params) in
      Debug.print @@ lazy ("[qelim] output: " ^ Z3.Expr.to_string expr);
      let phi =
        Evaluator.simplify @@ Formula.nnf_of
        @@ formula_of ctx [] penv instance.dtenv expr
      in
      back_instance
        ~reset:(fun ins -> Z3.Goal.reset ins.goal)
        instance_pool id instance;
      if false then print_endline @@ "qelim ret: " ^ Formula.str_of phi;
      phi
    with Z3.Error "canceled" ->
      Common.PhaseTime.event_here "qelim-canceled";
      (* a cancelled elimination declines (the input is returned) and gives
         its solver instance back to the pool, as the answered path does, so
         that a cancelled call on a fresh instance does not leave the pool
         without it *)
      back_instance
        ~reset:(fun ins -> Z3.Goal.reset ins.goal)
        instance_pool id instance;
      phi)
  else phi

let smtlib2_str_of_formula ~id ctx fenv dtenv phi =
  Z3.Expr.to_string
  @@ of_formula_with_z3fenv ~id ctx
       (Set.to_list @@ Formula.term_sort_env_of phi)
       (penv_of phi ctx dtenv) fenv dtenv phi

let expr_of_default_true ~id ctx fenv dtenv phi =
  try of_formula_with_z3fenv ~id ctx [] [] fenv dtenv @@ Evaluator.simplify phi
  with exn_ when not (Common.Timer.is_async exn_) ->
    of_formula_with_z3fenv ~id ctx [] [] fenv dtenv @@ Formula.mk_true ()

let str_of_asserts_of_solver solver =
  "Asserts of solver:\n\t"
  ^ String.concat_map_list ~sep:"\n\t" ~f:Z3.Expr.to_string
  @@ Z3.Solver.get_assertions solver

let inc_check_valid solver exprs =
  if false then
    Debug.print
    @@ lazy
         (sprintf "checking validity of %s\n%s\n"
            (String.concat_map_list ~sep:" / " ~f:Z3.Expr.to_string exprs)
            (str_of_asserts_of_solver solver));
  match z3_check solver exprs with
  | SATISFIABLE ->
      if false then Debug.print @@ lazy (sprintf "check valid -> (sat)invalid");
      false
  | UNSATISFIABLE ->
      if false then
        Debug.print @@ lazy (sprintf "checksat valid -> (unsat)valid");
      true
  | _ -> failwith "inc_check_valid"

let star and_flag = function
  | Formula.Atom (a, _) when Atom.is_pvar_app a -> None
  | Formula.UnaryOp (Formula.Not, Formula.Atom (a, _), _)
    when Atom.is_pvar_app a ->
      None
  | phi ->
      Some (Evaluator.simplify @@ if and_flag then phi else Formula.negate phi)

let rec simplify_term ~id solver ctx fenv dtenv = function
  | Term.FunApp (T_bool.Formula phi, [], info) ->
      let phi, has_changed = simplify_formula ~id solver ctx fenv dtenv phi in
      (T_bool.of_formula ~info phi, has_changed)
  | Term.FunApp (T_bool.IfThenElse, [ t1; t2; t3 ], info) ->
      let t1, has_changed1 = simplify_term ~id solver ctx fenv dtenv t1 in
      let t2, has_changed2 =
        (*ToDo: add t1 to the context*)
        simplify_term ~id solver ctx fenv dtenv t2
      in
      let t3, has_changed3 =
        (*ToDo: add not t1 to the context*)
        simplify_term ~id solver ctx fenv dtenv t3
      in
      ( T_bool.mk_if_then_else ~info t1 t2 t3,
        has_changed1 || has_changed2 || has_changed3 )
  | t (*ToDo*) -> (t, false)

and simplify_atom ~id solver ctx fenv (dtenv : dtenv) atom =
  if Atom.is_pvar_app atom then
    let pvar, sorts, args, info = Atom.let_pvar_app atom in
    let args', _has_changed_list =
      List.unzip @@ List.map ~f:(simplify_term ~id solver ctx fenv dtenv) args
    in
    ( Atom.mk_pvar_app pvar sorts args' ~info,
      false (*List.exists ~f:ident has_changed_list*) )
  else
    let phi = Formula.mk_atom atom in
    if false then
      Debug.print @@ lazy (sprintf "simplify atom: %s" (Formula.str_of phi));
    if
      inc_check_valid solver
        [ expr_of_default_true ~id ctx fenv dtenv @@ Formula.negate phi ]
    then (Atom.mk_true (), true)
    else if
      inc_check_valid solver [ expr_of_default_true ~id ctx fenv dtenv phi ]
    then (Atom.mk_false (), true)
    else (atom, false)

and check_sub_formulas ~id level solver ctx fenv (dtenv : dtenv) and_flag phi =
  let cs =
    List.map ~f:snd
    @@ List.sort ~compare:(fun (n1, _) (n2, _) -> n1 - n2)
    @@ List.map ~f:(fun x -> (Formula.ast_size x, x))
    @@ Set.to_list
    @@ if and_flag then Formula.conjuncts_of phi else Formula.disjuncts_of phi
  in
  if false then (
    print_endline
    @@ String.init level ~f:(fun _ -> ' ')
    ^ string_of_int @@ List.length cs;
    Debug.print
    @@ lazy
         (sprintf "Cs: %s"
            (String.concat_map_list ~sep:"\n\t" cs ~f:Formula.str_of));
    Debug.print @@ lazy (str_of_asserts_of_solver solver));
  try
    Z3.Solver.push solver;
    let cs', _, has_changed =
      List.fold_left cs
        ~init:([], List.tl_exn cs, false)
        ~f:(fun (cs', cs, has_changed) c ->
          if false then Debug.print @@ lazy (sprintf "c: %s" (Formula.str_of c));
          Z3.Solver.push solver;
          z3_solver_add solver
          @@ List.map ~f:(expr_of_default_true ~id ctx fenv dtenv)
          @@ List.filter_map cs ~f:(star and_flag);
          if false then Debug.print @@ lazy (str_of_asserts_of_solver solver);
          let c', has_changed' =
            simplify_formula ~id ~level:(level + 1) solver ctx fenv dtenv c
          in
          Z3.Solver.pop solver 1;
          if false then
            Debug.print @@ lazy (sprintf "c': %s" (Formula.str_of c'));
          if
            (and_flag && Formula.is_false c')
            || ((not and_flag) && Formula.is_true c')
          then raise @@ Stdlib.Not_found
          else (
            (match star and_flag c' with
            | Some phi ->
                z3_solver_add solver
                  [ expr_of_default_true ~id ctx fenv dtenv phi ]
            | None -> ());
            ( c' :: cs',
              (match cs with _ :: tl -> tl | _ -> []),
              has_changed || has_changed' )))
    in
    Z3.Solver.pop solver 1;
    let cs' = List.rev cs' in
    if false && has_changed then
      Debug.print
      @@ lazy
           (sprintf "compare Cs to Cs':\nCs: %s\nCs': %s"
              (String.concat_map_list ~sep:"\n\t" cs ~f:Formula.str_of)
              (String.concat_map_list ~sep:"\n\t" cs' ~f:Formula.str_of));
    let ret =
      Evaluator.simplify
      @@ if and_flag then Formula.and_of cs' else Formula.or_of cs'
    in
    if has_changed then (
      if false then Debug.print @@ lazy "has changed.";
      ( fst @@ check_sub_formulas ~id level solver ctx fenv dtenv and_flag ret,
        true ))
    else (ret, false)
  with Stdlib.Not_found ->
    Z3.Solver.pop solver 1;
    ((if and_flag then Formula.mk_false () else Formula.mk_true ()), true)

and simplify_formula ~id ?(level = 0) solver ctx fenv (dtenv : dtenv) phi =
  if false then (
    Debug.print
    @@ lazy (sprintf "[z3:simplify_formula] input: %s" (Formula.str_of phi));
    Debug.print @@ lazy (str_of_asserts_of_solver solver));
  let res =
    match phi with
    | Formula.Atom (atom, _) when not (Atom.is_true atom || Atom.is_false atom)
      ->
        let atom, has_changed = simplify_atom ~id solver ctx fenv dtenv atom in
        (Formula.mk_atom atom, has_changed)
    | Formula.UnaryOp (Not, Atom (atom, _), _)
      when not (Atom.is_true atom || Atom.is_false atom) ->
        let atom, has_changed = simplify_atom ~id solver ctx fenv dtenv atom in
        (Formula.negate (Formula.mk_atom atom), has_changed)
    | Formula.BinaryOp (And, _, _, _) ->
        check_sub_formulas ~id level solver ctx fenv dtenv true phi
    | Formula.BinaryOp (Or, _, _, _) ->
        check_sub_formulas ~id level solver ctx fenv dtenv false phi
    | Formula.LetFormula (var, sort, def, body, info) ->
        let def, _ = simplify_term ~id solver ctx fenv dtenv def in
        let body, has_changed =
          simplify_formula ~id ~level solver ctx fenv dtenv body
        in
        (Formula.mk_let_formula ~info var sort def body, has_changed)
    | _ -> (phi, false)
  in
  if false then
    Debug.print
    @@ lazy
         (sprintf "[z3:simplify_formula] output: %s"
            (Formula.str_of @@ fst res));
  res

and simplify ?(timeout = None) ~id fenv phi =
  let fenv = fenv_for_query fenv [ phi ] in
  Debug.print @@ lazy "===========simplify start=============";
  Debug.print @@ lazy (sprintf "input: %s" @@ Formula.str_of phi);
  let cfg = [ ("model", "true") ] in
  let instance = get_instance id cfg instance_pool in
  let ctx, solver =
    (instance.ctx, instance.solver (*Z3.Solver.mk_solver ctx None*))
  in
  instance.dtenv <- z3_dtenv_of_formula ~init:instance.dtenv ctx phi;
  instance.fenv <-
    z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv instance.dtenv;
  if false then
    Debug.print
    @@ lazy
         (sprintf "the smtlib2 formua:\n\t%s"
         @@ smtlib2_str_of_formula ~id ctx instance.fenv instance.dtenv phi);
  let set_timeout milliseconds =
    let params = Z3.Params.mk_params ctx in
    Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") milliseconds;
    Z3.Solver.set_parameters solver params
  in
  set_timeout (Option.value timeout ~default:0);
  (* [simplify_formula] asserts into the pooled solver, which [check_sat]
     shares; the reset used to run on the normal path only, so a query that
     raised left its assertions behind for the next caller of the instance. *)
  let finally () =
    z3_solver_reset solver;
    set_timeout 0;
    back_instance ~reset:ignore instance_pool id instance
  in
  match
    let phi =
      z3_simplify ~id fenv @@ Formula.nnf_of @@ Normalizer.normalize_let phi
    in
    Debug.print @@ lazy "*** start ***";
    let phi =
      fst @@ simplify_formula ~id solver ctx instance.fenv instance.dtenv phi
    in
    Debug.print @@ lazy "*** end ***";
    let phi = z3_simplify ~id fenv phi in
    Debug.print
    @@ lazy
         (sprintf "output: %s\n===========simplify end============="
            (Formula.str_of phi));
    phi
  with
  | phi ->
      finally ();
      phi
  | exception e ->
      finally ();
      raise e

(** For external calls converting ONE formula into [ctx]: it declares every
    recursive function of [fenv] in [ctx], so a second call on the same context
    declares them again.  Use [formula_converter] for several formulas. *)
let of_formula ~id ctx env penv fenv dtenv phi =
  of_formula_with_z3fenv ~id ctx env penv
    (z3_fenv_of ~id ctx env penv (fenv_for_query fenv [ phi ]) dtenv)
    dtenv phi

(** For external calls converting several formulas into one context: the
    recursive functions of [fenv] are declared once, at the first conversion
    (so a converter never applied declares nothing, as no [of_formula] call
    did), and the returned function converts a formula under a sort
    environment of its own.  Not to be shared between domains. *)
let formula_converter ~id ctx penv fenv dtenv =
  let z3fenv = lazy (z3_fenv_of ~id ctx [] penv fenv dtenv) in
  fun env phi ->
    of_formula_with_z3fenv ~id ctx env penv (Lazy.force z3fenv) dtenv phi
