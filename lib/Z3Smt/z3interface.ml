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

(* The Z3 work other than [check] calls, each kind under a phase of its own
   when the phase-time account is on (the report sums each name over every
   path): resetting a solver (which rebuilds its theory plugins), adding
   assertions, reading a model and evaluating in it, simplifying, and applying
   a tactic (quantifier elimination).  A check is accounted by
   [Common.PhaseTime.z3]; everything else here only times, it changes no
   call, and with the account off it calls straight through (no phase, no
   fork-guard poll). *)
let z3_kind name f =
  if !Common.PhaseTime.on then Common.PhaseTime.with_phase name f else f ()

module Z3 = struct
  include Z3

  module Solver = struct
    include Z3.Solver

    let reset s = z3_kind "z3-reset" (fun () -> reset s)
    let add s es = z3_kind "z3-add" (fun () -> add s es)

    let get_model s =
      z3_kind "z3-get-model" (fun () -> get_model s)
  end

  module Model = struct
    include Z3.Model

    let eval m e c =
      z3_kind "z3-model-eval" (fun () -> eval m e c)
  end

  module Expr = struct
    include Z3.Expr

    let simplify e p =
      z3_kind "z3-simplify" (fun () -> simplify e p)
  end

  module Tactic = struct
    include Z3.Tactic

    (* with the runtime lock released: one quantifier elimination can run
       for minutes, and a termination signal must be handled meanwhile *)
    let apply t g p =
      z3_kind "z3-tactic" (fun () -> Z3Released.tactic_apply t g p)
  end
end

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
(* With [COAR_Z3_DUMP_DIR=dir] in the environment, every check of the run, from
   any entry point and any domain, is written the same way to its own file
   [dir/q_k.smt2] (k counting from 0 over the whole run; the directory must
   exist), with [COAR_Z3_LAST_STACK] adding the asking call stack as comments.
   It is for collecting a run's questions to replay them under another solver,
   so the files spell recursive applications as SMT-LIB does ([dump_text]);
   a replay meets a fresh solver, not the pushed, pooled one that asked, and
   the file holds assertions, not the tactic or parameters the solver had.  A
   [with_query_dump] in force takes precedence.  With [COAR_Z3_DUMP_MIN_SECS=s]
   as well, a file of the directory whose check returned in less than [s]
   seconds is removed after the check, so only the slow checks remain (a check
   the run's end cuts short is kept, since it is written before it is asked). *)
(* The process that set the prefix is kept beside it: a forked copy inherits
   the setting and its counter, so without its own process id in the name a
   copy's question and the next question its parent asks get the same file,
   and the parent's overwrites the copy's (a killed copy never appends its
   answer, so the file then holds a different question's answer). *)
let query_dump : (string * int ref * int) option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_query_dump prefix f =
  let saved = Stdlib.Domain.DLS.get query_dump in
  Stdlib.Domain.DLS.set query_dump
    (Some (prefix, ref 0, Pid.to_int (Core_unix.getpid ())));
  Common.Timer.protect
    ~finally:(fun () -> Stdlib.Domain.DLS.set query_dump saved)
    f

let query_dump_dir = Sys.getenv "COAR_Z3_DUMP_DIR"
let query_dump_dir_count = Stdlib.Atomic.make 0

(* the process the run started in, read at start-up (before any fork) *)
let query_dump_dir_pid = Pid.to_int (Core_unix.getpid ())

let query_dump_min_secs =
  Option.bind (Sys.getenv "COAR_Z3_DUMP_MIN_SECS") ~f:Float.of_string_opt

let stack_comment () =
  ";; asked from\n"
  ^ String.concat_map_list ~sep:"\n"
      (String.split_lines
         (Stdlib.Printexc.raw_backtrace_to_string
            (Stdlib.Printexc.get_callstack 80)))
      ~f:(fun l -> ";; " ^ l)
  ^ "\n"

(* A census of the extensional rewrite of array equalities that contain a
   [lambda] ([lambda_array_eq_rewrite] below): how often a question reaching
   the solver holds such a rewritten equality, and what the solver answered.
   The rewrite is exact, but the form it produces is universally quantified,
   and on some questions the solver leaves the quantified form undecided
   where the unrewritten one is answered at once; this counts how often.

   Opt-in and diagnostic only; nothing is printed and no extra work is done
   unless the environment says so:
     COAR_LAMBDA_EQ_CENSUS -- one [LAMBDA_EQ_Q] line on stderr per question
       that holds a rewritten equality (its answer, the reason for an
       [unknown], the seconds taken and the first caller outside this file),
       and a [LAMBDA_EQ_SUMMARY] line at exit.
     COAR_LAMBDA_EQ_REPLAY (with the first) -- the same question is also asked
       with every rewritten equality put back as written, of a fresh solver
       in the question's context, under COAR_LAMBDA_EQ_REPLAY_MS (default 10000) ms; its
       answer is recorded beside the first and never used.  A [sat] there is
       untrustworthy: the solver answers some of these equalities [sat]
       wrongly, which is why the rewrite exists.

   A rewritten equality is matched to the question that holds it by testing
   whether putting the equality back changes the question; so a conversion done for another purpose
   (a simplification, a tactic) is counted among the converted atoms and
   never as a question.  A question asked of the solver directly, outside
   [z3_check] (the fixpoint engine, a few backends' own loops), is not seen. *)
module LambdaEqCensus = struct
  let on = Option.is_some (Sys.getenv "COAR_LAMBDA_EQ_CENSUS")
  let replay = on && Option.is_some (Sys.getenv "COAR_LAMBDA_EQ_REPLAY")

  let replay_ms =
    match Option.bind (Sys.getenv "COAR_LAMBDA_EQ_REPLAY_MS") ~f:Int.of_string_opt with
    | Some ms when ms > 0 -> ms
    | _ -> 10000

  let converted = Atomic.make 0
  let questions = Atomic.make 0
  let undecided = Atomic.make 0
  let replay_decided = Atomic.make 0
  let lock = Stdlib.Mutex.create ()

  (* the rewritten equalities converted in this domain since its last
     question, as (context, extensional form, form as written); at most [cap]
     kept *)
  let pending :
      (Z3.context * Z3.Expr.expr * Z3.Expr.expr) list Stdlib.Domain.DLS.key =
    Stdlib.Domain.DLS.new_key (fun () -> [])

  let cap = 64

  let note ctx ext plain =
    Atomic.incr converted;
    Stdlib.Domain.DLS.set pending
      (List.take ((ctx, ext, plain) :: Stdlib.Domain.DLS.get pending) cap)

  (* Whether [ctx] is the context [solver] lives in.  The bindings expose no
     accessor, but a context and a solver are the native library's values
     underneath ([Z3native.context], [Z3native.solver]), and two contexts
     compare by the native pointer.  Expressions of two contexts must never
     meet in one call, so a recorded equality is considered only for a
     question of its own context.  (Translating the question into a context
     of its own instead corrupted the heap on a PCSat run.) *)
  let same_context (ctx : Z3.context) (solver : Z3.Solver.solver) =
    Stdlib.( = )
      (Obj.magic ctx : Z3native.context)
      (Z3native.context_of_solver (Obj.magic solver : Z3native.solver))

  let emit line =
    Stdlib.Mutex.lock lock;
    Out_channel.output_string stderr (line ^ "\n");
    Out_channel.flush stderr;
    Stdlib.Mutex.unlock lock

  let () =
    if on then
      Stdlib.at_exit (fun () ->
          emit
            (sprintf
               "LAMBDA_EQ_SUMMARY pid=%d converted=%d questions=%d \
                unknown=%d replay_decided=%d"
               (Core_unix.getpid () |> Pid.to_int)
               (Atomic.get converted) (Atomic.get questions)
               (Atomic.get undecided) (Atomic.get replay_decided)))

  let status_str solver = function
    | Z3.Solver.SATISFIABLE -> "sat"
    | Z3.Solver.UNSATISFIABLE -> "unsat"
    | Z3.Solver.UNKNOWN ->
        "unknown(" ^ String.tr ~target:' ' ~replacement:'_'
          (Z3.Solver.get_reason_unknown solver) ^ ")"

  (* the first two stack frames in this tree's sources outside the solver
     interface and the common library, to say who asked *)
  let site () =
    let frames =
      String.split_lines
        (Stdlib.Printexc.raw_backtrace_to_string
           (Stdlib.Printexc.get_callstack 80))
    in
    let place l =
      match String.substr_index l ~pattern:"file \"" with
      | None -> None
      | Some i ->
          let rest = String.drop_prefix l (i + 6) in
          if
            String.is_prefix rest ~prefix:"lib/"
            && not
                 (String.is_prefix rest ~prefix:"lib/Z3Smt/"
                 || String.is_prefix rest ~prefix:"lib/common/")
          then
            Some
              (String.filter rest ~f:(fun c -> Char.(c <> '"' && c <> ' ')))
          else None
    in
    match List.take (List.filter_map frames ~f:place) 2 with
    | [] -> "?"
    | l -> String.concat ~sep:"<" l

  (* [check solver exprs] answers as [solver] would; under the census it also
     reports the question when it holds a rewritten equality *)
  let around solver exprs check =
    let pend = Stdlib.Domain.DLS.get pending in
    if (not on) || List.is_empty pend then check ()
    else (
      Stdlib.Domain.DLS.set pending [];
      let pairs =
        List.filter_map pend ~f:(fun (ctx, ext, plain) ->
            if same_context ctx solver then Some (ctx, ext, plain) else None)
      in
      let asked = Z3.Solver.get_assertions solver @ exprs in
      let put_back e =
        List.fold pairs ~init:e ~f:(fun e (_, ext, plain) ->
            Z3.Expr.substitute_one e ext plain)
      in
      let present =
        List.count pairs ~f:(fun (_, ext, plain) ->
            List.exists asked ~f:(fun e ->
                not (Z3.Expr.equal e (Z3.Expr.substitute_one e ext plain))))
      in
      if present = 0 then check ()
      else (
        Atomic.incr questions;
        let started = Common.Clock.now_float () in
        let status = check () in
        let secs =
          Time_float.Span.to_sec
            (Time_float.diff (Common.Clock.now_float ()) started)
        in
        (match status with
        | Z3.Solver.UNKNOWN -> Atomic.incr undecided
        | _ -> ());
        let replayed =
          match (replay, pairs) with
          | false, _ | _, [] -> ""
          | true, (ctx, _, _) :: _ -> (
              (* a solver of its own, in the question's context *)
              try
                let s = Z3.Solver.mk_simple_solver ctx in
                let params = Z3.Params.mk_params ctx in
                Z3.Params.add_int params
                  (Z3.Symbol.mk_string ctx "timeout")
                  replay_ms;
                Z3.Solver.set_parameters s params;
                Z3.Solver.add s (List.map asked ~f:put_back);
                let t0 = Common.Clock.now_float () in
                let st = Common.PhaseTime.z3 (fun () -> Z3.Solver.check s []) in
                let rs =
                  Time_float.Span.to_sec
                    (Time_float.diff (Common.Clock.now_float ()) t0)
                in
                (match (status, st) with
                | Z3.Solver.UNKNOWN, (SATISFIABLE | UNSATISFIABLE) ->
                    Atomic.incr replay_decided
                | _ -> ());
                sprintf " plain=%s plain_secs=%.3f" (status_str s st) rs
              with e ->
                " plain=error("
                ^ String.tr ~target:' ' ~replacement:'_' (Exn.to_string e)
                ^ ")")
        in
        emit
          (sprintf "LAMBDA_EQ_Q pid=%d answer=%s secs=%.3f eqs=%d site=%s%s"
             (Core_unix.getpid () |> Pid.to_int)
             (status_str solver status) secs present (site ()) replayed);
        status))
end

(* [dump_text solver]: [solver]'s assertions as SMT-LIB text for a file or a
   log meant to be read again, by this tool, Z3 or another solver.  Z3's
   printing spells an application of a recursive function as [((_ f 0) x)],
   which SMT-LIB does not define and cvc5 refuses; this is that printing with
   each such application written [(f x)] beside the [define-funs-rec] block
   that defines [f] (the text unchanged, under a comment saying so, where
   the plain name could mean another symbol).  For dumps only: no question
   asked of a solver is built from it. *)
let dump_text solver =
  Common.SmtlibRecursive.standard_text (Z3.Solver.to_string solver)

let z3_check solver exprs =
  (match Sys.getenv "COAR_Z3_LAST" with
   | Some path ->
       Out_channel.write_all path
         ~data:
           (Common.SmtlibRecursive.standard_text
              (Z3.Solver.to_string solver ^ "\n;; assumptions\n"
              ^ String.concat ~sep:"\n" (List.map exprs ~f:Z3.Expr.to_string))
           ^ "\n(check-sat)\n"
           ^
           match Sys.getenv "COAR_Z3_LAST_STACK" with
           | None -> ""
           | Some _ -> stack_comment ())
   | None -> ());
  let dump_path, with_stack, min_secs =
    match Stdlib.Domain.DLS.get query_dump with
    | Some (prefix, k, setter) ->
        let pid = Pid.to_int (Core_unix.getpid ()) in
        let path =
          if pid = setter then sprintf "%s_%d.smt2" prefix !k
          else sprintf "%s_%d-copy%d.smt2" prefix !k pid
        in
        incr k;
        (Some path, false, None)
    | None -> (
        match query_dump_dir with
        | None -> (None, false, None)
        | Some dir ->
            (* a forked copy inherits the counter, so a copy's checks and its
               parent's would get the same names and overwrite each other's
               files; a check of any process but the first is named with
               that process's id too *)
            let k = Stdlib.Atomic.fetch_and_add query_dump_dir_count 1 in
            let pid = Pid.to_int (Core_unix.getpid ()) in
            ( Some
                (if pid = query_dump_dir_pid then
                   sprintf "%s/q_%d.smt2" dir k
                 else sprintf "%s/q_%d-copy%d.smt2" dir k pid),
              Option.is_some (Sys.getenv "COAR_Z3_LAST_STACK"),
              query_dump_min_secs ))
  in
  LambdaEqCensus.around solver exprs @@ fun () ->
  match dump_path with
  | None -> Common.PhaseTime.z3 (fun () -> Z3.Solver.check solver exprs)
  | Some path ->
      Out_channel.write_all path
        ~data:
          (Common.SmtlibRecursive.standard_text
             ("(set-logic ALL)\n" ^ Z3.Solver.to_string solver
             ^ String.concat
                 (List.map exprs ~f:(fun e ->
                      "(assert " ^ Z3.Expr.to_string e ^ ")\n")))
          ^ "(check-sat)\n"
          ^ if with_stack then stack_comment () else "");
      let started = Common.Clock.now_float () in
      let status =
        Common.PhaseTime.z3 (fun () -> Z3.Solver.check solver exprs)
      in
      let secs =
        Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) started)
      in
      (match min_secs with
      | Some m when Float.(secs < m) -> Stdlib.Sys.remove path
      | _ ->
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
               secs)));
      status

(* with the runtime lock released, as [Z3.Solver.check] is: one optimisation
   check can run for tens of seconds *)
let z3_opt_check optimizer =
  Common.PhaseTime.z3 (fun () -> Z3Released.optimize_check optimizer)

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

(* With [int_to_bv_range] on, a question whose split rewrite introduced an
   integer quotient (a word [x] that also occurs outside [int_to_bv n]) is,
   after the strengthening with every quotient fixed to 0 has not given a
   model, asked AS GIVEN rather than in its split form.  The two are
   equisatisfiable, so the answer means the same either way; only which form
   Z3 is handed changes.  Why: the split form puts [2^n * q + ubv_to_int xb]
   beside the bit-vector terms, and Z3 5.1.0 did not decide such questions
   where the unrewritten one was decided -- a predicate-elimination validity
   question over a bit set's word index and bit (a bit index bounded only by
   a disjunctive [ite] on a [mod]) was [unsat] in 0.6-1.8 s as given under
   four seeds, and undecided at 5 s (and at 20 s standalone) split, where the
   strengthening with the quotient fixed to 0, whose [unsat] is not an
   answer, took 8 s.  A separate switch, off by default. *)
let int_to_bv_split_ask_original = Atomic.make false
let set_int_to_bv_split_ask_original b =
  Atomic.set int_to_bv_split_ask_original b

(* how many questions [int_to_bv_split_ask_original] asked as given; read by
   the tests *)
let int_to_bv_split_original_asked = Atomic.make 0

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
  mutable params_memo : ((int * int option * int option) * Z3.Params.params) list;
      (** the parameter sets [check_sat_base] has made for this solver, by
          (timeout, resource limit, arithmetic solver) *)
}

(* the pool is one Hashtbl shared by every solver domain (the table itself is
   not safe for concurrent mutation); guard the table operations — not the Z3
   work — with their own mutex *)
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
   after one question pile up unless a collection is forced.  There is no
   explicit release to call instead: the OCaml binding (Z3 5.1's ML stubs)
   counts the handles of a context -- the context itself and every term,
   solver, model and vector made in it -- and deletes the native context when
   the last of them is finalised, its [del_context] doing nothing while a
   handle is alive; and each handle is announced to the collector at its own
   few bytes, never at the native memory behind it.  So only a collection can
   release a dropped context, and only a full one does so promptly; a full major
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
  Common.Timer.protect
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

(* setting the value the rule already has changes nothing (the solving entry
   and the solver both write the configured rule) *)
let set_new_context_full_major_bytes b =
  let b = Option.map b ~f:(Int.max 1) in
  if not (Option.equal Int.equal b (Atomic.get new_context_full_major_bytes))
  then (
    Atomic.set new_context_full_major_bytes b;
    Atomic.set major_words_at_last_full_major Float.nan)

(* [full_major_due_by_bytes ~threshold ~last ~now]: [last] and [now] are
   [major_words] readings (words); due when there is no last reading or the
   growth in bytes reaches [threshold] *)
let word_bytes = Float.of_int (Stdlib.Sys.word_size / 8)

let full_major_due_by_bytes ~threshold ~last ~now =
  Float.is_nan last || Float.((now - last) * word_bytes >= of_int threshold)

let current_major_words () = (Gc.quick_stat ()).major_words

(* A collection trigger read off Z3's own memory.

   [set_new_context_full_major_z3_mb (Some t)] makes the forced collection
   before a new context depend on Z3's estimate of the native memory it holds
   ([Z3native.get_estimated_alloc_size], the process-wide count Z3's
   allocator keeps of every byte it has handed out and not taken back, synced
   from each thread in steps of about 100 KB): the collection is made exactly
   when that count exceeds the lowest reading taken since the last forced
   collection by at least [t] megabytes, or when it cannot be read.  The first
   context of the process takes the first reading and is not preceded by a
   collection, as under the count rules.  While set it replaces the count and
   byte rules, as the byte rule does (an override of [Int.max_value] still
   means no collection).

   Why: the memory a forced collection exists to release is exactly what this
   count measures -- the native memory of contexts dropped by their askers
   and not yet finalised -- which neither a context count nor the OCaml heap
   sees.  The memory argument: a context is made without a collection only
   when Z3's count is below [low + t], where [low] is at most the reading
   right after the last forced collection, which released every context
   unreachable when it began.  So the native memory of dropped contexts
   waiting for the collector, plus whatever live Z3 memory grew in the
   meantime, stays under [t] at a new context; the overshoot beyond it is what one question
   allocates after its context is made.  Under the count rule of every n-th
   context the bound is n - 1 contexts of any size.  A context costs about
   16 MB of the count by itself (Z3 5.1's [mk_context]; its solver, goal and
   a first trivial check add under 1 MB), so for small questions [t] of
   [16 n] MB collects about as often as every n-th context.
   A run whose questions are small makes many contexts per collection, and
   one whose questions are large collects as often as they need; live growth
   (a pooled context accumulating terms) costs one collection per [t] of it.
   The questions asked are the same under every rule; only the collector's
   timing changes, and with it, possibly, the identifiers Z3 reuses in a
   pooled context.  Process-wide, written once when a solver configuration
   that asks for it is loaded. *)
let new_context_full_major_z3_mb : int option Atomic.t = Atomic.make None

(* the lowest Z3 allocation reading (MB) since the last forced collection
   under the Z3 memory rule; -1 before the first reading *)
let z3_mb_since_full_major = Atomic.make (-1)

let set_new_context_full_major_z3_mb mb =
  let mb = Option.map mb ~f:(Int.max 1) in
  if not (Option.equal Int.equal mb (Atomic.get new_context_full_major_z3_mb))
  then (
    Atomic.set new_context_full_major_z3_mb mb;
    Atomic.set z3_mb_since_full_major (-1))

(* Z3's estimate of its allocated memory in MB; -1 when it cannot be read *)
let z3_alloc_mb () =
  try
    Int64.to_int_exn (Z3native.get_estimated_alloc_size ()) / 1_048_576
  with exn when not (Common.Timer.is_async exn) -> -1

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

(* [native_mb ()]: the process's resident set less its OCaml major heap, in MB
   -- the part of the resident memory the OCaml collector does not account
   for: native allocations (Z3's contexts among them), the minor heaps, the
   code and the stacks.  -1 when the resident set cannot be read; never
   below 0 otherwise (a heap counted larger than what is resident reads 0).
   The heap size is [Gc.quick_stat]'s, the sum over every domain of the
   statistics each sampled at its last minor collection, so it lags the
   heap by at most a minor heap per domain.  The reading errs towards more
   native memory, not less: heap the collector has freed but the process
   still holds (a full collection of a growing heap took the heap statistic
   down by 500 MB while the resident set stayed) reads as native until the
   heap reuses it, and the reading then falls back. *)
let native_mb () =
  match rss_mb () with
  | rss when rss < 0 -> -1
  | rss ->
      let heap_mb =
        (Gc.quick_stat ()).heap_words * (Stdlib.Sys.word_size / 8) / 1_048_576
      in
      Int.max 0 (rss - heap_mb)

(* A collection trigger for a caller that drops whole native contexts in
   bursts (the template synthesizer replaces its contexts on every qualifier
   search and template rebuild): [full_major_if_resident_grew ()] forces a full
   major collection exactly when the native part of the process's resident set
   ([native_mb]) has grown by at least [resident_growth_mb] megabytes over the
   lowest reading taken since the last such collection, before the first call,
   and whenever the resident set cannot be read.

   Why the resident set and not a count: the memory at stake is the dropped
   contexts' native heaps, which neither a context count nor the OCaml heap's
   size sees, and which the resident set does.

   Why the OCaml heap is subtracted: a process whose OCaml heap grows (the
   other domain building a large clausal form, say) grows its resident set
   with no context dropped, and a collection then releases nothing the trigger
   is for, yet costs a full stop-the-world collection of that heap.  Read on
   the whole resident set, the trigger fired at every new context of such a
   run: on three term-comp inputs whose resident set rose to 5-12 GB, every
   one of their 10-25 forced collections came back with the resident set
   within 65 MB of its reading before, and they took 6-20 s each, up to 148 s
   of a 300 s run.  The OCaml heap is the collector's own business: its major
   cycles are paced by allocation, which is what the native heaps of dropped
   contexts escape.  What this gives up: those collections also reclaimed
   the growing heap's garbage early, so without them such a run's peak
   resident set is higher (on one input 8.2 GB became 10.5 GB, and another
   reached a 12 GB cap in 3 runs of 3 instead of 1 of 3).  A forced
   collection before
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

(* the lowest [native_mb] reading since the last forced collection, -1
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
  let now = native_mb () in
  let low = Atomic.get resident_mb_since_full_major in
  let due =
    full_major_due_by_resident ~threshold_mb:resident_growth_mb ~low_mb:low
      ~now_mb:now
  in
  if synth_gc_log then
    Stdlib.Printf.eprintf
      "synthgc rss_mb=%d native_mb=%d low_mb=%d forced=%d\n%!" (rss_mb ()) now
      low
      (if due then 1 else 0);
  if due then (
    Common.PhaseTime.with_phase "gc-full-major" Gc.full_major;
    Atomic.incr resident_full_majors;
    Atomic.set resident_mb_since_full_major (native_mb ()))
  else if now < low then Atomic.set resident_mb_since_full_major now

(* The domain a pooled context belongs to, part of every pool key.

   A pooled context is handed only to the domain that made it.  An instance id
   does not guarantee that: the same id is asked for from different domains
   (an id threaded into a task that a task pool runs on whichever domain is
   free, the default id of a caller that passes none), and a context made by
   one domain and later used by another ends up with OCaml handles (solvers,
   expressions, models) in both domains' heaps.  The Z3 OCaml bindings count
   the handles of a context and each finalizer decrements that count and
   then, in a separate read, deletes the context when it reads zero; under
   OCaml 5 every domain sweeps its own heap, in parallel with the others, so
   two finalizers of one context can both decrement, both read zero and
   delete the context twice -- glibc's "double free or corruption", an abort
   after the answer was printed.  A finalizer also calls into the context
   (a reference-count decrement) while the other domain may be asking a
   question in it, and a Z3 context is not safe for concurrent use.  Keeping a
   context in one domain keeps all of its handles in one heap, swept by one
   domain at a time. *)
let pool_domain () = (Stdlib.Domain.self () :> int)

let get_instance =
  let new_instance cfg =
    Caml_threads.Mutex.lock mutex;
    Common.Timer.protect ~finally:(fun () -> Caml_threads.Mutex.unlock mutex) @@ fun () ->
    (let k = Atomic.fetch_and_add new_contexts 1 in
     let override = Stdlib.Domain.DLS.get full_major_every_override in
     (* No collection before the first context this function makes in the
        process: what the collection is for is releasing the contexts it made
        earlier and its callers dropped, and there are none yet, so it could
        only collect OCaml garbage, at the cost of a full collection of
        whatever heap the input's reading has built (0.6 s of a 60 MB heap on
        a loaded machine, before each of the first questions of a solve).
        (Contexts made directly with [Z3.mk_context] elsewhere were never
        counted by these rules; their makers collect for them.)  Under the
        byte rule the growth is then measured from this first context. *)
     let first = k = 0 in
     let z3_rule = Atomic.get new_context_full_major_z3_mb in
     (* under the Z3 memory rule, one reading serves both the decision and the
        low-water mark *)
     let z3_now = if Option.is_some z3_rule then z3_alloc_mb () else -1 in
     let due =
       (not first)
       &&
       match (override, Atomic.get new_context_full_major_bytes) with
       | Some n, _ when n = Int.max_value -> false
       | _, _ when Option.is_some z3_rule ->
           let low = Atomic.get z3_mb_since_full_major in
           (* no low reading yet under this rule (set after the first
              context): take this one as the low *)
           if low < 0 && z3_now >= 0 then false
           else
             full_major_due_by_resident
               ~threshold_mb:(Option.value_exn z3_rule)
               ~low_mb:low ~now_mb:z3_now
       | _, Some threshold ->
           full_major_due_by_bytes ~threshold
             ~last:(Atomic.get major_words_at_last_full_major)
             ~now:(current_major_words ())
       | Some n, None -> k % n = 0
       | None, None -> k % Atomic.get new_context_full_major_every = 0
     in
     if gc_bytes_log then
       Stdlib.Printf.eprintf
         "gcbytes ctx=%d forced=%d grow_mb=%.1f heap_mb=%d rss_mb=%d z3_mb=%d\n%!"
         k
         (if due then 1 else 0)
         (let last = Atomic.get major_words_at_last_full_major in
          if Float.is_nan last then -1.
          else
            Float.((current_major_words () - last) * word_bytes / 1_048_576.))
         ((Gc.quick_stat ()).heap_words * (Stdlib.Sys.word_size / 8)
         / 1_048_576)
         (rss_mb ())
         (if z3_now >= 0 then z3_now else z3_alloc_mb ());
     (* both marked for the phase report, which then counts the contexts made
        under each phase and the time the forced collections took there *)
     if due then (
       (* A full collection, not a single major cycle, under every rule:
          garbage found by one cycle is swept during the next, and a block
          marked before it became unreachable survives the cycle in
          progress, so it takes the three cycles of [Gc.full_major] to
          release every context dropped before the collection.  Making the
          cycles one at a time and stopping once Z3's reading was back near
          its low-water mark was tried: on runs of a hundred and more
          contexts nearly every collection needed all three. *)
       Common.PhaseTime.with_phase "gc-full-major" Gc.full_major;
       Atomic.incr new_context_full_majors;
       Atomic.set major_words_at_last_full_major (current_major_words ());
       if Option.is_some z3_rule then
         Atomic.set z3_mb_since_full_major (z3_alloc_mb ()))
     else (
       if first then
         Atomic.set major_words_at_last_full_major (current_major_words ());
       (* the low-water mark: the lowest reading since the last forced
          collection (a natural major cycle may have released contexts) *)
       if z3_now >= 0 then
         let low = Atomic.get z3_mb_since_full_major in
         if low < 0 || z3_now < low then Atomic.set z3_mb_since_full_major z3_now));
    let ctx, solver, goal =
      Common.PhaseTime.with_phase "new-context" @@ fun () ->
      let ctx = Z3.mk_context cfg in
      ( ctx,
        Z3.Solver.mk_solver ctx None,
        Z3.Goal.mk_goal ctx false false false )
    in
    let dtenv = Set.Poly.empty in
    let fenv = Map.Poly.empty in
    { ctx; solver; goal; dtenv; fenv; cfg; uses = 0; params_memo = [] }
  in
  fun (id : int option) cfg instance_pool ->
    if not enable_solver_pool then new_instance cfg
    else
      match
        with_pool_lock (fun () ->
            Hashtbl.Poly.find instance_pool (pool_domain (), id, cfg))
      with
      | None -> new_instance cfg
      | Some instance -> instance

let back_instance ~reset instance_pool id instance =
  if enable_solver_pool then (
    reset instance;
    with_pool_lock (fun () ->
        Hashtbl.Poly.set instance_pool
          ~key:(pool_domain (), id, instance.cfg)
          ~data:instance))

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

   The pool is keyed by the domain ([pool_domain]), the instance id, the
   context configuration and the
   arithmetic solver the question asks for (that parameter is fixed when a
   solver's core is first set up, so solvers asked with different ones are not
   mixed).  A lease removes the context from the pool, so two domains never
   share one; at most [clean_pool_per_key] wait per key.  Off by default:
   [lease_clean_instance] is then [get_instance] on an empty table, which is
   exactly the fresh context it replaces, and [release_clean_instance] does
   nothing. *)
let clean_reset_pool = Atomic.make false
let set_clean_reset_pool b = Atomic.set clean_reset_pool b

(* [with_clean_reset_pool f] runs [f] with the clean pool on in the calling
   domain, whatever the process-wide [clean_reset_pool] is, and restores the
   domain's setting on return and on raise.  For one stage whose questions
   are known to need only what a clean context keeps (never pushed, no
   recursive function declared), so that the pool can serve that stage
   without serving every fresh-context question of the process.  A context
   leased inside [f] is released inside [f] ([check_sat]'s fresh path does
   both in one call), so lease and release see the same setting. *)
let clean_reset_pool_override : bool option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let clean_reset_pool_on () =
  match Stdlib.Domain.DLS.get clean_reset_pool_override with
  | Some b -> b
  | None -> Atomic.get clean_reset_pool

let with_clean_reset_pool f =
  let saved = Stdlib.Domain.DLS.get clean_reset_pool_override in
  Stdlib.Domain.DLS.set clean_reset_pool_override (Some true);
  Common.Timer.protect
    ~finally:(fun () -> Stdlib.Domain.DLS.set clean_reset_pool_override saved)
    f
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

(* domain ([pool_domain]), instance id, context configuration, arithmetic
   solver *)
type clean_key = int * int option * (string * string) list * int option

let clean_pool : (clean_key, instance list) Hashtbl.Poly.t =
  Hashtbl.Poly.create ()

let lease_clean_instance ~arith id cfg =
  if not (clean_reset_pool_on ()) then
    get_instance id cfg (Hashtbl.Poly.create ())
  else
    let key = (pool_domain (), id, cfg, arith) in
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
  if clean_reset_pool_on () then (
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
            let key = (pool_domain (), id, inst.cfg, arith) in
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

(* the name Z3 prints for each sequence sort met by [of_sort] in this domain
   (the key of [seq_instances]); a function of the sort, whatever the context *)
let seq_name_memo : (Sort.t, string) Hashtbl.Poly.t Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> Hashtbl.Poly.create ())

(* A display name is not a sort identity: [S<int>] may itself be a legal
   declared name, and an uninterpreted sort named [int] prints like [SInt].
   Tag each sort constructor and preserve name/parameter boundaries instead.
   Datatypes are identified by their declared name and parameters, not by
   expanding their potentially recursive selector graph. *)
let sus_sort_key = Datatype.structural_sort_key

let hex_digits = "0123456789abcdef"

(* [s] with every character written as two lower-case hex digits: what
   [String.concat_map s ~f:(fun c -> sprintf "%02x" (Char.to_int c))] gives,
   without a [sprintf] per character *)
let hex_of_string s =
  let n = String.length s in
  let b = Bytes.create (2 * n) in
  for i = 0 to n - 1 do
    let c = Char.to_int (String.unsafe_get s i) in
    Bytes.unsafe_set b (2 * i) (String.unsafe_get hex_digits (c lsr 4));
    Bytes.unsafe_set b ((2 * i) + 1) (String.unsafe_get hex_digits (c land 15))
  done;
  Bytes.unsafe_to_string ~no_mutation_while_string_reachable:b

(* the name of each sort met by [z3_name_of_sus] in this domain: the name is a
   function of the sort, and computing it (the structural key printed and
   hex-encoded) cost about 15 us a call, against under 1 us for Z3 to make the
   sort -- most of the conversion of a question in the sequence-axiom form,
   whose every family function application converts its argument sorts. Per
   domain, so no lock is taken to read it *)
let sus_name_memo : (Sort.t, string) Hashtbl.Poly.t Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> Hashtbl.Poly.create ())

(* Encode every declaration, including a nullary one, so no legal user name
   can impersonate a generated name. Hex is injective over the tagged key and
   avoids depending on the quoting rules of a solver's printed symbols. *)
let z3_name_of_sus name params =
  let sort = T_dt.SUS (name, params) in
  let z3name =
    Hashtbl.Poly.find_or_add (Stdlib.Domain.DLS.get sus_name_memo) sort
      ~default:(fun () ->
        "#sus_" ^ hex_of_string (Sexp.to_string (sus_sort_key sort)))
  in
  (* registered on every call, as before: [clear_instance_pool] empties the
     table, and a name must decode back after it *)
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

let[@warning "-11"] rec sort_of z3_dtenv s =
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
  (* Z3's sort kinds grow between releases (5.3 added FINITE_FIELD_SORT); the
     catch-all keeps this match exhaustive on every supported Z3 version.  It
     is redundant (warning 11) on versions whose kinds are all listed above. *)
  | _ ->
      failwith @@ "[z3:sort_of] sort kind not supported: "
      ^ Z3.Sort.to_string s

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

(* Decoding a Z3 expression that shares subexpressions.  Z3 keeps one node
   per distinct expression, so an expression is a graph, while the decoders
   below walk it as a tree: a node reached along k paths is decoded k times,
   each time with a dozen calls of the Z3 API.  A refutation's proof term
   from the fixedpoint engine is the extreme case: each derivation step names
   the steps it uses, and a step used by several later ones is one node.
   Measured on one strategy check's counterexample, 3,211 distinct nodes stood
   for 2,539,164 tree nodes (1,430 against 102,890 derivation steps), and the
   decoding took about 115 s where the solver had taken 9 s.

   [with_shared_decoding f] runs [f] with a table, local to this domain and
   dropped when [f] returns or raises, in which every successful decoding of
   a node is kept, keyed by the node's identity in its context, the decoder
   (term, term as an atom, atom, formula) and the bound-variable environment
   it was decoded under, compared physically.  A node met again under the
   same environment gets the kept value.  Precondition: every expression
   decoded inside [f] belongs to one Z3 context, is decoded with the same
   predicate and datatype environments, and is alive while [f] runs (a
   node's identity is unique among live nodes of its context only); the
   decoders read nothing else that changes while [f] runs.
   What changes: a quantifier (or a Z3 lambda) met again is not given fresh
   binder names again, so its occurrences are one value with one set of bound
   names, as when a decoded term is copied; the values are the same up to the
   names of bound variables, and fewer fresh names are drawn.  A decoding that
   raises is not kept, so it raises again where it is met again, as without
   the table.  Nothing is cached outside [f]. *)
type decode_memo_value =
  | Decoded_term of Term.t
  | Decoded_atom of Atom.t
  | Decoded_formula of Formula.t

let decode_memo :
    (int * int, (sort_env_list * decode_memo_value) list) Stdlib.Hashtbl.t
    option
    Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_shared_decoding f =
  let saved = Stdlib.Domain.DLS.get decode_memo in
  Stdlib.Domain.DLS.set decode_memo (Some (Stdlib.Hashtbl.create 4096));
  Common.Timer.protect ~finally:(fun () -> Stdlib.Domain.DLS.set decode_memo saved) f

(* [decode_shared ~tag senv expr ~get ~put decode]: [decode ()] when no table
   is in scope; otherwise the kept value of [expr] under [senv] for the
   decoder [tag], or [decode ()] kept under them. *)
let decode_shared ~tag senv expr ~get ~put decode =
  match Stdlib.Domain.DLS.get decode_memo with
  | None -> decode ()
  | Some tbl -> (
      let key = (Z3.AST.get_id (Z3.Expr.ast_of_expr expr), tag) in
      let kept =
        Option.value ~default:[] (Stdlib.Hashtbl.find_opt tbl key)
      in
      match
        List.find_map kept ~f:(fun (senv', v) ->
            if phys_equal senv' senv then get v else None)
      with
      | Some v -> v
      | None ->
          let v = decode () in
          Stdlib.Hashtbl.replace tbl key ((senv, put v) :: kept);
          v)

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
  decode_shared
    ~tag:(if as_atom then 1 else 0)
    senv expr
    ~get:(function Decoded_term t -> Some t | _ -> None)
    ~put:(fun t -> Decoded_term t)
    (fun () -> term_of_unshared ~as_atom ctx senv penv dtenv expr)

and term_of_unshared ~as_atom ctx (senv : sort_env_list)
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
                        sprintf "%s %s in %s" Common.Util.UnreadableAnswer.prefix
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
  decode_shared ~tag:2 senv expr
    ~get:(function Decoded_atom a -> Some a | _ -> None)
    ~put:(fun a -> Decoded_atom a)
    (fun () -> atom_of_unshared ctx senv penv dtenv expr)

and atom_of_unshared ctx (senv : sort_env_list)
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
            let module U = Common.Util.UnreadableAnswer in
            (* Classify the cause before adding expression text, which may
               contain quoted symbols that resemble decoder diagnostics. *)
            if U.is_failure err then
              failwith
              @@ sprintf "%s in %s caused %s" U.atom_prefix
                   (Z3.Expr.to_string expr) err
            else
              failwith
              @@ sprintf "%s%s caused %s" U.atom_wrapper
                   (Z3.Expr.to_string expr) err)

and
    (* Conversion from Z3 expressions to formulas *)
    formula_of ctx (senv : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (dtenv : dtenv)
    expr =
  decode_shared ~tag:3 senv expr
    ~get:(function Decoded_formula phi -> Some phi | _ -> None)
    ~put:(fun phi -> Decoded_formula phi)
    (fun () -> formula_of_unshared ctx senv penv dtenv expr)

and formula_of_unshared ctx (senv : sort_env_list)
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

let decode_model ctx dtenv model_in =
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

(* A Z3 model describes everything its solver's CONTEXT knows, and the contexts
   here are pooled and reused, so a model can come back carrying declarations
   left by earlier queries: a query whose variables were [$1:X] and [$2:X]
   returned a model over [$1:X List ; $2:X List ; $2:X ; $1:X] and three
   further names it had never mentioned.  Clause variables are named per
   clause ([x0], [x1], ...), so one name at two sorts in one context is routine
   (measured: [x0 : X] and [x0 : int] in one run).  A reader that looks an
   entry up by name then gets a value of another sort, and a reader that turns
   the whole model into a substitution keyed by name gets two entries for one
   name (the process died on [Map.of_alist_exn] about one run in six on a
   tracked benchmark).

   [restrict_model_to_query phis model] removes exactly the entries that can
   be read at a wrong sort by a reader of the query [phis]:
   - an entry whose name the query uses is kept only at a sort the query uses
     it at;
   - an entry whose name the query does not use is kept only when the model
     holds that name once -- two entries for one name the query never
     mentioned cannot both be meant, and a substitution would take an
     arbitrary one.
   Exact (the identity) on a model in which no name collides: every name is
   held once and, where the query uses it, at the query's sort (a function
   declaration held once is kept whatever its printed sort).  Sorts are
   compared as printed, because a sort can be a datatype and polymorphic
   comparison does not order those reliably.  What this cannot see is a reader
   that asks about a name the query does not use, at a sort other than the
   one left-over entry has; such a reader reads by name AND sort through
   [LogicOld.model_find] / [model_subst ~target]. *)
let restrict_model_to_query phis model =
  if List.is_empty model then model
  else
    let counts =
      List.fold model ~init:Map.Poly.empty ~f:(fun acc ((x, _), _) ->
          Map.Poly.update acc x ~f:(function None -> 1 | Some n -> n + 1))
    in
    let query_sorts =
      Map.Poly.of_alist_multi
      @@ List.filter_map
           (Set.to_list @@ Set.Poly.union_list
           @@ List.map phis ~f:Formula.term_sort_env_of)
           ~f:(fun (x, srt) ->
             if Map.Poly.mem counts x then Some (x, Term.str_of_sort srt)
             else None)
    in
    let keep ((x, srt), _) =
      let unique = Map.Poly.find_exn counts x = 1 in
      match Map.Poly.find query_sorts x with
      | Some _ when unique && Sort.is_arrow srt ->
          (* a function declaration (arity > 0), which the model lists with no
             value: the query spells a function's sort differently from the
             model reader, so the printed sorts are not compared for it, and a
             single such entry is kept as it always was *)
          true
      | Some ss -> List.mem ss (Term.str_of_sort srt) ~equal:String.equal
      | None -> unique
    in
    let all_kept = List.for_all model ~f:keep in
    if count_model_collisions then (
      Atomic.incr query_models;
      if not all_kept then (
        Atomic.incr query_models_dropping;
        let dropped = List.filter model ~f:(Fn.non keep) in
        let by_query =
          List.count dropped ~f:(fun ((x, _), _) -> Map.Poly.mem query_sorts x)
        in
        ignore
          (Atomic.fetch_and_add query_model_entries_dropped (List.length dropped)
            : int);
        ignore
          (Atomic.fetch_and_add query_model_entries_dropped_in_query by_query
            : int)));
    if all_kept then model
    else (
      Debug.print
      @@ lazy
           "[z3:check_sat] the model holds a name at a sort the query does \
            not use it at; restricting it to the query";
      List.filter model ~f:keep)

(* [model_of ~query ctx dtenv m]: the model [m] decoded, restricted to what a
   reader of the query can mean ([restrict_model_to_query]).  [query] is
   REQUIRED so that no model leaves this module unrestricted: [`Query phis] for
   a model of [phis] asked in a pooled context (or any context that may hold
   other declarations), [`Fresh_context] only for a context made for this one
   query and discarded, whose declarations are the query's own. *)
let model_of ~query ctx dtenv m =
  let model = decode_model ctx dtenv m in
  match query with
  | `Fresh_context -> model
  | `Query phis ->
      Common.PhaseTime.with_phase "restrict" (fun () ->
          restrict_model_to_query phis model)

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

(* Recursive local references must identify the exact structural instance.
   Nominal keys deliberately never expand the recursive field graph. *)
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

(* The checks [find_z3_datatype] makes of the member it finds: raise unless
   [dt] is the declared instance itself and, where [dt] carries constructors,
   the same definition.  A function of the two values alone (datatypes are
   immutable), so a pair that passed once passes again. *)
let check_found_datatype declared dt =
  check_datatype_instance declared dt;
  if (not (List.for_all (Datatype.full_dts_of dt) ~f:(fun member ->
              List.is_empty (Datatype.conses_of_dt member))))
     && Stdlib.compare declared
          (Datatype.update_dts dt (List.filter (Datatype.full_dts_of dt)
              ~f:(fun member -> not (List.is_empty (Datatype.conses_of_dt member))))) <> 0 then
    failwith ("[z3] duplicate definition of the datatype " ^ Datatype.name_of dt)

(* The member of a declared environment whose instance key is [dt]'s, as
   [Set.find] over the members' keys gives it, followed by the checks above.

   An index of the environment last asked about in this domain stands in for
   the scan: one conversion looks a datatype up at every sort, constructor
   and selector it meets, and a scan computes the key of every member each
   time -- on a Thrust input with 109 declared datatypes, 159,239 lookups
   spent 13 of the 27 seconds of one conversion there.  The index is built
   from the environment by physical identity (the sets are immutable, so an
   index never goes stale), holds a key only when exactly one member has it
   (a key two members share is looked up by the scan, which decides which one
   [Set.find] returns), and remembers, per key, the datatype values
   (physically) that have passed the checks, so that those are not repeated
   on a value already checked against the same member.  The answer, and
   whether it raises, are the scan's. *)
type dt_index_entry = {
  member : Datatype.t * Z3.Sort.sort;
  mutable checked : Datatype.t list;  (* at most [dt_index_checked_max] *)
}

let dt_index_checked_max = 16

let dt_index_key :
    ((Datatype.t * Z3.Sort.sort) Set.Poly.t
    * (string, dt_index_entry option) Stdlib.Hashtbl.t)
    option
    Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let dt_index_of dtenv =
  match Stdlib.Domain.DLS.get dt_index_key with
  | Some (env, index) when phys_equal env dtenv -> index
  | _ ->
      let index = Stdlib.Hashtbl.create (2 * Set.length dtenv + 1) in
      Set.iter dtenv ~f:(fun ((declared, _) as member) ->
          let key = Datatype.instance_key declared in
          match Stdlib.Hashtbl.find_opt index key with
          | None -> Stdlib.Hashtbl.replace index key (Some { member; checked = [] })
          | Some _ -> Stdlib.Hashtbl.replace index key None);
      Stdlib.Domain.DLS.set dt_index_key (Some (dtenv, index));
      index

let find_z3_datatype_by_scan dtenv dt =
  let found =
    Set.find dtenv
      ~f:
        (fst >> Datatype.instance_key >> String.( = ) (Datatype.instance_key dt))
  in
  Option.iter found ~f:(fun (declared, _) -> check_found_datatype declared dt);
  found

(* Off only to compare the index against the scan it replaces. *)
let dt_index_enabled = Atomic.make true

let find_z3_datatype dtenv dt =
  if not (Atomic.get dt_index_enabled) then find_z3_datatype_by_scan dtenv dt
  else
  let index = dt_index_of dtenv in
  match Stdlib.Hashtbl.find_opt index (Datatype.instance_key dt) with
  | None -> None
  | Some None -> find_z3_datatype_by_scan dtenv dt
  | Some (Some entry) ->
      if not (List.exists entry.checked ~f:(phys_equal dt)) then (
        check_found_datatype (fst entry.member) dt;
        entry.checked <-
          dt :: List.take entry.checked (dt_index_checked_max - 1));
      Some entry.member

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
  | T_seq.SSeq se as sort ->
      let z3sort = Z3.Seq.mk_seq_sort ctx (of_sort ctx dtenv se) in
      (* the printed name of a sequence sort is a function of the sort:
         [seq_name_memo] keeps it, since printing it cost about 20 us a call,
         paid at every occurrence of a sequence variable in a converted
         formula *)
      let name =
        Hashtbl.Poly.find_or_add (Stdlib.Domain.DLS.get seq_name_memo) sort
          ~default:(fun () -> Z3.Sort.to_string z3sort)
      in
      with_pool_lock (fun () ->
          Hashtbl.Poly.set seq_instances ~key:name ~data:sort);
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
  let name = unint_tuple_prefix ^ "_" ^
    hex_of_string (Sexp.to_string (sus_sort_key (T_tuple.STuple sorts))) in
  Z3.Tuple.mk_sort ctx (Z3.Symbol.mk_string ctx name)
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
  match find_z3_datatype dtenv t with
  | Some _ -> dtenv
  | None -> (match Datatype.flag_of t with
  | Undef ->
      (* [declare-sort S n] with [n > 0] arrives here as an [Undef] datatype
         whose [params] are the instantiation; name the Z3 sort by them too *)
      Set.add dtenv
        ( t,
          Z3.Sort.mk_uninterpreted_s ctx
            (z3_name_of_sus (Datatype.name_of t) (Datatype.params_of t)) )
  | FCodt ->
      Common.Refusal.refuse
        "native Z3 SMT backend does not support codatatype %s"
        (Datatype.full_name_of t)
  | Alias _ -> failwith "not supported"
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
            let dt_name = Datatype.instance_name (Datatype.update_name t (Datatype.name_of_dt dt)) in
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
              sort )))

(* [z3_dtenv_of_dtenv ~init ctx dtenv]: [init] with every datatype of
   [dtenv] whose instance key it does not yet hold declared to [ctx] (with the
   datatypes its fields need) and added; raises where a held member and a
   datatype of [dtenv] share a key but are not the same instance or
   definition.  [~declared] is set when some datatype was not held, the only
   branch that calls Z3 or builds a new set; a call that leaves it unset made
   no Z3 call and returned [init] itself, having computed only functions of
   the values [init] and [dtenv] (instance keys, the checks) and filled the
   lookup caches of [find_z3_datatype], which change no answer. *)
and z3_dtenv_of_dtenv ?(init = Set.Poly.empty) ?(disambiguate_among = [])
    ?(declared = ref false) ctx dtenv =
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
                  (Datatype.instance_name (Datatype.update_name data (Datatype.name_of_dt dt)))
                  ~equal:String.equal
              then
                let owner = Datatype.instance_name (Datatype.update_name data (Datatype.name_of_dt dt)) in
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
        let name = Datatype.instance_key dt in
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
        let name = Datatype.instance_key data in
        match Map.Poly.find names name with
        | Some _ ->
            if Datatype.is_dt data then ignore (find_z3_datatype env data);
            (env, names)
        | None ->
            declared := true;
            let env = update_z3env ~qualify ctx env data in
            (env, names_of env))
  in
  if false then Debug.print @@ lazy (str_of_z3_env z3_dtenv);
  z3_dtenv

(* The pairs (global datatype environment, declared environment) of this
   domain for which [z3_dtenv_of_dtenv ~init:env ctx genv] has been seen to
   declare nothing, compared by physical identity (both are immutable):
   entry [i] is slot [i] of the two arrays, written round robin.  Bounded, so
   that a domain alternating between a few pooled instances keeps each one's
   pair.  Held weakly: a declared environment holds Z3 sorts, and a Z3 object
   keeps its whole context alive, so a strong entry kept up to eight contexts
   per domain from ever being freed after their instances were dropped -- on
   a MuStrat run of an integer transition system declaring an uninterpreted
   sort, whose checks each build a new context, the process peaked at about
   8 GB against about 2 GB with the memo never stored.  An entry whose
   environment has been collected can
   never be hit again (a hit needs that very value as [init]), so dropping it
   loses nothing. *)
type dtenv_fixpoints = {
  genvs : DTEnv.t Stdlib.Weak.t;
  envs : dtenv Stdlib.Weak.t;
  mutable next : int;
}

let dtenv_fixpoints_max = 8

let dtenv_fixpoints : dtenv_fixpoints Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () ->
      {
        genvs = Stdlib.Weak.create dtenv_fixpoints_max;
        envs = Stdlib.Weak.create dtenv_fixpoints_max;
        next = 0;
      })

let dtenv_fixpoint_hit fx genv init =
  let rec go i =
    i < dtenv_fixpoints_max
    && ((match (Stdlib.Weak.get fx.genvs i, Stdlib.Weak.get fx.envs i) with
        | Some genv', Some env' -> phys_equal genv genv' && phys_equal init env'
        | _ -> false)
       || go (i + 1))
  in
  go 0

let dtenv_fixpoint_add fx genv env =
  Stdlib.Weak.set fx.genvs fx.next (Some genv);
  Stdlib.Weak.set fx.envs fx.next (Some env);
  fx.next <- (fx.next + 1) mod dtenv_fixpoints_max

(* [z3_dtenv_of_formula ?init ctx phi]: the global datatype environment
   extended by [phi]'s datatypes ([update_dtenv]), then [init] extended by all
   of the global environment's datatypes declared to [ctx]
   ([z3_dtenv_of_dtenv]).

   A refresh that finds nothing to declare is not repeated.  When the global
   environment [genv] (after the update) and [init] are physically a pair for
   which [z3_dtenv_of_dtenv ~init ctx genv] was observed, in this domain, to
   set no [~declared] flag, [init] is returned without the walk.  Exact: such
   a call made no Z3 call and returned [init] after computing only functions
   of the two immutable values (instance keys, the instance and definition
   checks, which passed), with nothing read from [ctx]; so the call it
   replaces would compute the same, pass the same checks and return the same
   [init], and the context, the returned environment and every expression
   later converted against it are what they were.  Every caller assigns the
   result back to the instance, so the next refresh of that instance hits
   while no new datatype has reached the global environment.  Why: the walk
   computes the printed structural key of every member of [init] and of
   [genv] on every conversion, about 85 microseconds a call on a Thrust input
   whatever the formula; one input made 164,741
   conversions, none mentioning a datatype (13.8 s). *)
let z3_dtenv_of_formula ?(init = Set.Poly.empty) ctx phi =
  Common.PhaseTime.with_phase "dtenv-refresh" @@ fun () ->
  update_dtenv @@ DTEnv.of_formula phi;
  Debug.print
  @@ lazy (sprintf "[z3_dtenv_of] from:\n%s" @@ DTEnv.str_of @@ get_dtenv ());
  let genv = get_dtenv () in
  let fx = Stdlib.Domain.DLS.get dtenv_fixpoints in
  if dtenv_fixpoint_hit fx genv init then (
    Common.PhaseTime.event_here ~in_copy:false "fixpoint-hit";
    init)
  else
    let declared = ref false in
    let env = z3_dtenv_of_dtenv ~init ~declared ctx genv in
    if not !declared then dtenv_fixpoint_add fx genv env;
    env

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

(* The real algebraic number [T_real.Alge (poly, n)]: the [n]-th real root,
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

(* Flooring and ceiling division and their remainders, which Z3 has no
   operator for, written exactly in terms of Z3's Euclidean [div] and [mod].

   For [b <> 0] write [a = b*q + r] with [q = div a b] and [0 <= r < |b|], so
   [a/b = q + r/b].  If [r = 0] every mode's quotient is [q].  Otherwise
   [r/b] lies in (0, 1) when [b > 0] and in (-1, 0) when [b < 0], hence
     floor(a/b) = q        if b > 0,   q - 1   if b < 0,
     ceil(a/b)  = q + 1    if b > 0,   q       if b < 0,
   and the remainders [a - b*floor(a/b)] and [a - b*ceil(a/b)] are [r + b]
   (flooring, [b < 0]) and [r - b] (ceiling, [b > 0]), [r] otherwise.  These
   agree with [Value.div_of] / [Value.rem_of] at every nonzero divisor.

   At [b = 0] both guards are false, so each term is exactly Z3's [div a 0]
   or [mod a 0]: the division by zero keeps SMT-LIB's uninterpreted reading,
   as the Euclidean arm does, rather than being given a value (the remainders
   are written through [mod], not as [a - b * quotient], so that [a frem 0] is
   not forced to equal [a]).  Consequently a flooring or ceiling division by
   zero denotes the same unspecified value as the Euclidean one over the same
   operands; that identifies three functions SMT-LIB leaves free, which is
   one admissible interpretation and does not constrain any nonzero case. *)
let mk_div_correction ctx ~flooring a b =
  let zero = Z3.Arithmetic.Integer.mk_numeral_i ctx 0 in
  Z3.Boolean.mk_and ctx
    [
      (if flooring then Z3.Arithmetic.mk_lt ctx b zero
       else Z3.Arithmetic.mk_gt ctx b zero);
      Z3.Boolean.mk_not ctx
        (Z3.Boolean.mk_eq ctx (Z3.Arithmetic.Integer.mk_mod ctx a b) zero);
    ]

let mk_fdiv ctx a b =
  Z3.Boolean.mk_ite ctx
    (mk_div_correction ctx ~flooring:true a b)
    (Z3.Arithmetic.mk_sub ctx
       [ Z3.Arithmetic.mk_div ctx a b; Z3.Arithmetic.Integer.mk_numeral_i ctx 1 ])
    (Z3.Arithmetic.mk_div ctx a b)

let mk_cdiv ctx a b =
  Z3.Boolean.mk_ite ctx
    (mk_div_correction ctx ~flooring:false a b)
    (Z3.Arithmetic.mk_add ctx
       [ Z3.Arithmetic.mk_div ctx a b; Z3.Arithmetic.Integer.mk_numeral_i ctx 1 ])
    (Z3.Arithmetic.mk_div ctx a b)

let mk_fmod ctx a b =
  Z3.Boolean.mk_ite ctx
    (mk_div_correction ctx ~flooring:true a b)
    (Z3.Arithmetic.mk_add ctx [ Z3.Arithmetic.Integer.mk_mod ctx a b; b ])
    (Z3.Arithmetic.Integer.mk_mod ctx a b)

let mk_cmod ctx a b =
  Z3.Boolean.mk_ite ctx
    (mk_div_correction ctx ~flooring:false a b)
    (Z3.Arithmetic.mk_sub ctx [ Z3.Arithmetic.Integer.mk_mod ctx a b; b ])
    (Z3.Arithmetic.Integer.mk_mod ctx a b)

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

(* The rewrite for a query this process asks its own library: the identity
   where that library answers the equality correctly *)
let expand_finite_array_eqs phi =
  if Atomic.get finite_array_literal_eq_rewrite then
    ArrayLiteralEq.expand_finite_array_eqs phi
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
   not an array.  Writable so that a test can exercise both sides. *)
let lambda_array_eq_rewrite =
  (* COAR_LAMBDA_EQ_OFF turns the rewrite off for a diagnosis that compares
     verdicts with and without it; with it set, an [unsat] may be wrong *)
  Atomic.make (Option.is_none (Sys.getenv "COAR_LAMBDA_EQ_OFF"))

let is_lambda_array_eq t1 t2 =
  Atomic.get lambda_array_eq_rewrite
  && (match Term.sort_of t1 with T_array.SArray _ -> true | _ -> false)
  && (ArrayLiteralEq.term_contains_lambda t1 || ArrayLiteralEq.term_contains_lambda t2)

let is_lambda_sequence_eq t1 t2 =
  Atomic.get lambda_array_eq_rewrite
  && (match Term.sort_of t1 with T_seq.SSeq _ -> true | _ -> false)
  && (ArrayLiteralEq.term_contains_lambda t1 || ArrayLiteralEq.term_contains_lambda t2)

(* Whether a datatype or tuple equality is taken apart into its components
   before it is asked ([ArrayLiteralEq.component_lambda_eq]).  Z3 5.1.0
   answers [sat] to a false equality between two records whose array field
   contains a [lambda], exactly as it does for the bare arrays: with [mk] the
   only constructor of a datatype with one [Array Int Int] field,
   [hd nil = mk (store (lambda x. x) 7 0) /\ hd nil = mk (store (const 3) 7 0)]
   is [sat] although the two arrays differ at index 0.  The extensional form
   of an array equality is reached only through an equality of ARRAY sort,
   which this one is not, so the datatype equality has to be taken apart
   first.  A satisfiable Horn problem whose goal clause said the open term
   [hd nil] cannot equal both records answered [unsat]. *)
let is_component_lambda_eq t1 t2 =
  Atomic.get lambda_array_eq_rewrite
  && (match Term.sort_of t1 with
     | T_dt.SDT _ | T_tuple.STuple _ -> true
     | _ -> false)
  && (ArrayLiteralEq.term_contains_lambda t1 || ArrayLiteralEq.term_contains_lambda t2)

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

(* The same n-ary form for the conversions [f] makes in this domain only,
   restored when [f] returns or raises; other domains and later conversions
   are unaffected.  Where the process-wide switch is on as well, the form is
   n-ary either way.  A backend that hands its formulas to Z3 for a purpose
   other than asserting them uses it: Z3's fixedpoint engine does not flatten
   a rule's constraint when it takes the rule, so a binary nest reaches its
   search as a nest. *)
let flat_and_or_scoped : bool Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> false)

let with_flat_and_or f =
  let saved = Stdlib.Domain.DLS.get flat_and_or_scoped in
  Stdlib.Domain.DLS.set flat_and_or_scoped true;
  Common.Timer.protect
    ~finally:(fun () -> Stdlib.Domain.DLS.set flat_and_or_scoped saved)
    f

let flat_and_or_on () =
  Atomic.get flat_and_or || Stdlib.Domain.DLS.get flat_and_or_scoped

(* [Some n]: a nest of [And] ([Or]) with at least [n] operands is handed to Z3
   as one n-ary [and] ([or]) even where [flat_and_or_on] is false; a shorter
   nest stays the binary nest it is.  The quadratic flattening described at
   [flat_and_or] is what this removes: a template synthesizer's hole over
   3,413 qualifiers reaches here as a chain of 3,413 conjuncts per example
   atom, and asserting one run's synthesis constraints took 6.6-17.1 s with
   the binary nests against 0.4-1.0 s with them n-ary.  The formula asked is
   the same (an n-ary
   connective is its nest up to associativity); only a nest of [n] operands
   or more reaches Z3 in another shape, so a question without one is the
   same Z3 term as before; each nest handed over n-ary on this account is
   counted as the phase-time event [z3/flat-long-nest], so a run's report
   says whether the threshold changed any question the process asked itself
   (a question asked in a forked copy is counted in the copy's table, which
   is not reported).  Process-wide,
   written once when a configuration asks for it. *)
let flat_long_and_or_min = Atomic.make None
let set_flat_long_and_or_min n = Atomic.set flat_long_and_or_min n

(* Whether the nest of [And] (with [conj]) or [Or] (otherwise) at [phi] has
   at least [limit] operands, counting the operands [Formula.conjuncts_list_of]
   ([disjuncts_list_of]) would give.  Visits at most [2 * limit] nodes, so
   asking it at every node of a nest shorter than [limit] costs at most
   quadratic time in that nest's length, which [limit] bounds. *)
let nest_has_operands ~conj limit phi =
  let rec go n = function
    | _ when n >= limit -> true
    | [] -> false
    | Formula.BinaryOp (And, phi1, phi2, _) :: rest when conj ->
        go n (phi1 :: phi2 :: rest)
    | Formula.BinaryOp (Or, phi1, phi2, _) :: rest when not conj ->
        go n (phi1 :: phi2 :: rest)
    | _ :: rest -> go (n + 1) rest
  in
  go 0 [ phi ]

let flat_nest_on ~conj phi =
  flat_and_or_on ()
  ||
  match Atomic.get flat_long_and_or_min with
  | None -> false
  | Some limit ->
      nest_has_operands ~conj limit phi
      && (Common.PhaseTime.event "z3/flat-long-nest";
          true)

(* Whether the conversion below creates the Z3 terms of an application's
   operands from the first to the last.  Z3 numbers every term it creates and
   orders the operands of what it simplifies, and its decision atoms, by that
   number, so two creation orders of one formula are one term (hash-consed,
   [Z3.Expr.equal]) that the solver may work on differently.  OCaml evaluates
   an application's arguments, and a list literal's elements, from the last
   to the first, so without the switch a connective's right operand is
   created before its left one; Z3's own reader and [Z3.Expr.translate]
   create left to right.  The same question created both ways was measured
   to cost a geometric mean of 1.14 times the resource units in the
   right-first order over 39 fresh-context questions, with one question
   decided only in the reading order.  The switch changes no term, only the
   order the terms are created in.  Process-wide, written once when a
   configuration asks for it. *)
let left_to_right_creation = Atomic.make false
let set_left_to_right_creation b = Atomic.set left_to_right_creation b

(* [(f (), g ())], with [f] run first under [left_to_right_creation] and [g]
   first otherwise, which is the order [(f (), g ())] itself evaluates in. *)
let in_creation_order f g =
  if Atomic.get left_to_right_creation then
    let x = f () in
    let y = g () in
    (x, y)
  else
    let y = g () in
    let x = f () in
    (x, y)

(* The conversion memo: within one conversion into one context, a constant
   of sort Bool, Int or Real and an integer or rational numeral are made once
   and the Z3 term reused at every later occurrence.

   Exact: Z3 hash-conses its terms, so making a constant (a symbol and a
   sort) or a numeral that already exists in the context returns the term
   that exists, with its identifier; and within one conversion every term
   made earlier is still alive (it is a subterm of an operand the conversion
   holds, or of the term it is building), so the plain conversion's second
   [mk_const] or [mk_numeral] would return exactly the term the memo
   returns.  Symbols are interned by name and sorts by kind in the same way.
   So the memo changes no term, no identifier and no creation order; it only
   skips the calls (the symbol's name built and looked up, the numeral
   printed and parsed again, the sort object and the wrapper allocated).
   The key carries the sort (Bool, Int, Real) of a constant and of a numeral,
   so one name or one value at two sorts gets two terms, as without it.
   Keyed by the context it was opened for: a conversion into another context
   nested inside it opens its own and finds nothing of this one.
   [conversion_memo] is the switch (process-wide). *)
let conversion_memo = Atomic.make true
let set_conversion_memo b = Atomic.set conversion_memo b

module ZTbl = Stdlib.Hashtbl.Make (struct
  type t = Z.t

  let equal = Z.equal
  let hash = Z.hash
end)

module QTbl = Stdlib.Hashtbl.Make (struct
  type t = Q.t

  let equal = Q.equal
  let hash (q : Q.t) = (Z.hash q.Q.num * 31) + Z.hash q.Q.den
end)

type conv_memo = {
  cm_ctx : Z3.context;
  cm_consts : (string * int, Z3.Expr.expr) Stdlib.Hashtbl.t;
      (** the constant's Z3 name and its sort (0 Bool, 1 Int, 2 Real) *)
  cm_ints : Z3.Expr.expr ZTbl.t;
  cm_reals : Z3.Expr.expr QTbl.t;
  mutable cm_binders :
    (sort_env_list * (Ident.tvar, int * Sort.t) Stdlib.Hashtbl.t) option;
      (** a binder list [env] and, for each variable it binds, the position
          of its first (innermost) occurrence and that occurrence's sort *)
}

let conv_memo_key : conv_memo option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

(* the memo open for [ctx] in this domain, if any *)
let conv_memo_for ctx =
  match Stdlib.Domain.DLS.get conv_memo_key with
  | Some m when phys_equal m.cm_ctx ctx -> Some m
  | _ -> None

(* [f ()] with a conversion memo open for [ctx] (the open one when it is
   for [ctx] already), the previous one restored after; [f ()] alone when
   the switch is off *)
let with_conv_memo ctx f =
  if not (Atomic.get conversion_memo) then f ()
  else
    match Stdlib.Domain.DLS.get conv_memo_key with
    | Some m when phys_equal m.cm_ctx ctx -> f ()
    | saved ->
        Stdlib.Domain.DLS.set conv_memo_key
          (Some
             {
               cm_ctx = ctx;
               cm_consts = Stdlib.Hashtbl.create 64;
               cm_ints = ZTbl.create 16;
               cm_reals = QTbl.create 16;
               cm_binders = None;
             });
        Common.Timer.protect
          ~finally:(fun () -> Stdlib.Domain.DLS.set conv_memo_key saved)
          f

(* The innermost binding of [var] in the binder list [env] (innermost
   first): [Some (i, sort)] with [i] the smallest position at which [env]
   binds [var] -- the de Bruijn index Z3 reads -- and [sort] the sort bound
   there; [None] when [env] does not bind [var].  So it answers what
   [List.findi env ~f:(fun _ (key, _) -> Stdlib.(key = var))] answers.

   WHY.  The conversion of a formula whose [let]s were lifted into one
   existential binds every lifted variable in a single [Bind], so [env]
   holds thousands of entries and every occurrence of a lifted variable
   scanned it: on one input, 213 thousand occurrences against a list of 2 to
   4 thousand cost 4.5 s of a 6.4 s conversion.  Within an open conversion
   memo the last long list scanned is indexed once, by a table filled from
   the innermost entry outwards that keeps the first position of each
   variable, and a lookup walks [env] only down to that list (physical
   identity: a list is immutable, so the same list has the same entries),
   comparing keys as the scan does, then adds the table's position to the
   number of entries walked.  A binder pushed inside the indexed one
   ([ALambda]'s [(x, s) :: env], an inner [Bind]) is thus walked only over
   what it pushed.  A walk that passes [index_after] entries without
   meeting the indexed list indexes the list it is in instead; building a
   table costs one insertion per entry, so a list is indexed only when
   scanning it has cost as much as indexing a list of [index_after] entries
   would, and short lists are scanned as before.  Without an open memo the
   lookup is the scan. *)
let find_binder env var =
  let index_after = 16 in
  let index env =
    let tbl = Stdlib.Hashtbl.create (List.length env) in
    List.iteri env ~f:(fun i (key, sort) ->
        if not (Stdlib.Hashtbl.mem tbl key) then
          Stdlib.Hashtbl.add tbl key (i, sort));
    tbl
  in
  let in_table walked tbl =
    Option.map (Stdlib.Hashtbl.find_opt tbl var) ~f:(fun (i, sort) ->
        (walked + i, sort))
  in
  let rec walk memo walked = function
    | [] -> None
    | l when (match memo.cm_binders with
             | Some (indexed, _) -> phys_equal l indexed
             | None -> false) ->
        in_table walked (snd (Option.value_exn memo.cm_binders))
    | (key, sort) :: _ when Stdlib.(key = var) -> Some (walked, sort)
    | _ :: tl when walked + 1 < index_after -> walk memo (walked + 1) tl
    | _ ->
        let tbl = index env in
        memo.cm_binders <- Some (env, tbl);
        in_table 0 tbl
  in
  match Stdlib.Domain.DLS.get conv_memo_key with
  | Some memo -> walk memo 0 env
  | None ->
      Option.map
        (List.findi env ~f:(fun _ (key, _) -> Stdlib.(key = var)))
        ~f:(fun (i, (_, sort)) -> (i, sort))

(* Counters a test reads to see the memos act: constants and numerals found
   in the conversion memo, and conjuncts found in the conjunct memo. *)
let conv_memo_hits = Atomic.make 0

(* Mutants, a test's only: [conv_memo_mutant_ignore_sort] keys a constant by
   its name alone; [conjunct_memo_mutant_by_position] reuses the previous
   question's terms by position, without the physical-identity test. *)
let conv_memo_mutant_ignore_sort = Atomic.make false
let conjunct_memo_mutant_by_position = Atomic.make false
let conjunct_memo_hits = Atomic.make 0
let conjunct_memo_misses = Atomic.make 0

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
  | Formula.BinaryOp (And, _, _, _) when flat_nest_on ~conj:true phi ->
      Z3.Boolean.mk_and ctx
        (of_operands_right_first ~id ctx env penv fenv dtenv
           (Formula.conjuncts_list_of phi))
  | Formula.BinaryOp (Or, _, _, _) when flat_nest_on ~conj:false phi ->
      Z3.Boolean.mk_or ctx
        (of_operands_right_first ~id ctx env penv fenv dtenv
           (Formula.disjuncts_list_of phi))
  | Formula.BinaryOp (And, phi1, phi2, _) ->
      let e1, e2 = of_formula_pair ~id ctx env penv fenv dtenv phi1 phi2 in
      Z3.Boolean.mk_and ctx [ e1; e2 ]
  | Formula.BinaryOp (Or, phi1, phi2, _) ->
      let e1, e2 = of_formula_pair ~id ctx env penv fenv dtenv phi1 phi2 in
      Z3.Boolean.mk_or ctx [ e1; e2 ]
  | Formula.BinaryOp (Iff, phi1, phi2, _) ->
      let e1, e2 = of_formula_pair ~id ctx env penv fenv dtenv phi1 phi2 in
      Z3.Boolean.mk_iff ctx e1 e2
  | Formula.BinaryOp (Xor, phi1, phi2, _) ->
      let e1, e2 = of_formula_pair ~id ctx env penv fenv dtenv phi1 phi2 in
      Z3.Boolean.mk_xor ctx e1 e2
  | Formula.BinaryOp (Imply, phi1, phi2, _) ->
      let e1, e2 = of_formula_pair ~id ctx env penv fenv dtenv phi1 phi2 in
      Z3.Boolean.mk_implies ctx e1 e2
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
  if Atomic.get left_to_right_creation then
    (* [List.map] applies its function from the first element on *)
    List.map phis ~f:(of_formula_aux ~id ctx env penv fenv dtenv)
  else
    List.fold (List.rev phis) ~init:[] ~f:(fun acc phi ->
        of_formula_aux ~id ctx env penv fenv dtenv phi :: acc)

(* the two operands of a binary connective, created in the order
   [in_creation_order] selects *)
and of_formula_pair ~id ctx env penv fenv dtenv phi1 phi2 =
  in_creation_order
    (fun () -> of_formula_aux ~id ctx env penv fenv dtenv phi1)
    (fun () -> of_formula_aux ~id ctx env penv fenv dtenv phi2)

and of_var_term ~id ctx env dtenv t =
  let (var, sort), _ = Term.let_var t in
  if false then
    Debug.print
    @@ lazy
         (sprintf "[z3:of_var_term] %s : %s" (Ident.name_of_tvar var)
            (Term.str_of_sort sort));
  match find_binder env var with
  | Some (i, sort') ->
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
      let z3_var =
        match id with
        | None -> var
        | Some id -> Ident.Tvar (InstanceName.encode ~id ~sort name)
      in
      let make () = Z3.Expr.mk_const ctx (of_var ctx z3_var) @@ of_sort ctx dtenv sort in
      let tag =
        match sort with
        | T_bool.SBool -> 0
        | T_int.SInt -> 1
        | T_real.SReal -> 2
        | _ -> -1
      in
      match if tag < 0 then None else conv_memo_for ctx with
      | None -> make ()
      | Some m -> (
          let key =
            ( Ident.name_of_tvar z3_var,
              if Atomic.get conv_memo_mutant_ignore_sort then 0 else tag )
          in
          match Stdlib.Hashtbl.find_opt m.cm_consts key with
          | Some e ->
              Atomic.incr conv_memo_hits;
              e
          | None ->
              let e = make () in
              Stdlib.Hashtbl.add m.cm_consts key e;
              e)

(* Conversion from terms to Z3 expressions *)
and of_term ~id ctx (env : sort_env_list)
    (penv : (Ident.pvar, Z3.FuncDecl.func_decl) List.Assoc.t) (fenv : fenv)
    (dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t) t =
  if false then Debug.print @@ lazy (sprintf "[z3:of_term] %s" @@ Term.str_of t);
  match t with
  | Var (var, T_bool.SBool, _)
    when Option.is_none (find_binder env var) -> (
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
      | T_int.Int n, [] -> (
          let make () = Z3.Arithmetic.Integer.mk_numeral_s ctx (Z.to_string n) in
          match conv_memo_for ctx with
          | None -> make ()
          | Some m -> (
              match ZTbl.find_opt m.cm_ints n with
              | Some e ->
                  Atomic.incr conv_memo_hits;
                  e
              | None ->
                  let e = make () in
                  ZTbl.add m.cm_ints n e;
                  e))
      | T_real.Real r, [] -> (
          match Q.classify r with
          | Q.ZERO | Q.NZERO -> (
              let make () =
                try Z3.Arithmetic.Real.mk_numeral_s ctx (Q.to_string r)
                with exn_ when not (Common.Timer.is_async exn_) ->
                  failwith @@ Q.to_string r ^ " cannot be parsed"
              in
              match conv_memo_for ctx with
              | None -> make ()
              | Some m -> (
                  match QTbl.find_opt m.cm_reals r with
                  | Some e ->
                      Atomic.incr conv_memo_hits;
                      e
                  | None ->
                      let e = make () in
                      QTbl.add m.cm_reals r e;
                      e))
          | Q.UNDEF ->
              let n, d =
                in_creation_order
                  (fun () -> Z3.Arithmetic.Real.mk_numeral_i ctx 0)
                  (fun () -> Z3.Arithmetic.Real.mk_numeral_i ctx 0)
              in
              Z3.Arithmetic.mk_div ctx n d
          | Q.INF ->
              let n, d =
                in_creation_order
                  (fun () -> Z3.Arithmetic.Real.mk_numeral_i ctx 1)
                  (fun () -> Z3.Arithmetic.Real.mk_numeral_i ctx 0)
              in
              Z3.Arithmetic.mk_div ctx n d
          | Q.MINF ->
              let n, d =
                in_creation_order
                  (fun () -> Z3.Arithmetic.Real.mk_numeral_i ctx (-1))
                  (fun () -> Z3.Arithmetic.Real.mk_numeral_i ctx 0)
              in
              Z3.Arithmetic.mk_div ctx n d)
      | T_real.Alge (poly, n), [] -> alge_of ctx poly n
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
      | T_int.Div Flooring, [ t1; t2 ] -> mk_fdiv ctx t1 t2
      | T_int.Div Ceiling, [ t1; t2 ] -> mk_cdiv ctx t1 t2
      | T_real.RDiv, [ t1; t2 ] ->
          (*ToDo: necessary? *)
          let as_real t () =
            if Z3.Arithmetic.is_int t then
              Z3.Arithmetic.Integer.mk_int2real ctx t
            else t
          in
          let t1, t2 = in_creation_order (as_real t1) (as_real t2) in
          Z3.Arithmetic.mk_div ctx t1 t2
      | T_int.Rem Euclidean, [ t1; t2 ] ->
          Z3.Arithmetic.Integer.mk_mod ctx t1 t2
      | T_int.Rem Truncated, [ t1; t2 ] -> mk_tmod ctx t1 t2
      | T_int.Rem Flooring, [ t1; t2 ] -> mk_fmod ctx t1 t2
      | T_int.Rem Ceiling, [ t1; t2 ] -> mk_cmod ctx t1 t2
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
          let lo, hi =
            in_creation_order
              (fun () -> Z3.Seq.mk_string ctx "\\u{0}")
              (fun () -> Z3.Seq.mk_string ctx "\\u{2FFFF}")
          in
          Z3.Seq.mk_re_range ctx lo hi
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
        && (Option.is_some (find_binder env (Ident.pvar_to_tvar pvar))
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
     [ArrayLiteralEq.expand_finite_array_eq_atom]) is rewritten HERE as well as in
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
         && ArrayLiteralEq.is_finite_array_literal_eq t1 t2 ->
      let phi = ArrayLiteralEq.expand_finite_array_eq_atom (T_bool.mk_eq t1 t2) in
      of_formula_aux ~id ctx env penv fenv dtenv
        (match sym with T_bool.Neq -> Formula.mk_neg phi | _ -> phi)
  (* an equality between array terms one of which contains a [lambda], asked
     extensionally ([lambda_array_eq_rewrite]); the element equality it leaves
     has a smaller sort, so the recursion ends *)
  | App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as sym), [ t1; t2 ], _)
    when is_lambda_array_eq t1 t2 ->
      let phi = ArrayLiteralEq.extensional_array_eq t1 t2 in
      if not LambdaEqCensus.on then
        of_formula_aux ~id ctx env penv fenv dtenv
          (match sym with T_bool.Neq -> Formula.mk_neg phi | _ -> phi)
      else
        (* the same conversion, with the extensional form and the equality as
           written recorded for the census *)
        let ext = of_formula_aux ~id ctx env penv fenv dtenv phi in
        let plain =
          let e1, e2 =
            in_creation_order
              (fun () -> of_term ~id ctx env penv fenv dtenv t1)
              (fun () -> of_term ~id ctx env penv fenv dtenv t2)
          in
          Z3.Boolean.mk_eq ctx e1 e2
        in
        LambdaEqCensus.note ctx ext plain;
        (match sym with T_bool.Neq -> Z3.Boolean.mk_not ctx ext | _ -> ext)
  | App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as sym), [ t1; t2 ], _)
    when is_lambda_sequence_eq t1 t2 ->
      let phi = ArrayLiteralEq.extensional_sequence_eq t1 t2 in
      of_formula_aux ~id ctx env penv fenv dtenv
        (match sym with T_bool.Neq -> Formula.mk_neg phi | _ -> phi)
  (* the same for a datatype or tuple equality holding a [lambda]
     ([ArrayLiteralEq.component_lambda_eq]): the equalities it leaves are between proper
     subterms of the side it took apart, so the recursion ends *)
  | App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as sym), [ t1; t2 ], _)
    when is_component_lambda_eq t1 t2
         && Option.is_some (ArrayLiteralEq.component_lambda_eq t1 t2) ->
      let phi = Option.value_exn (ArrayLiteralEq.component_lambda_eq t1 t2) in
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
          let m, z =
            in_creation_order
              (fun () -> Z3.Arithmetic.Integer.mk_mod ctx t2 t1)
              (fun () -> Z3.Arithmetic.Integer.mk_numeral_i ctx 0)
          in
          Z3.Boolean.mk_eq ctx m z
      | T_int.NotPDiv, [ t1; t2 ] ->
          let m, z =
            in_creation_order
              (fun () -> Z3.Arithmetic.Integer.mk_mod ctx t2 t1)
              (fun () -> Z3.Arithmetic.Integer.mk_numeral_i ctx 0)
          in
          Z3.Boolean.mk_not ctx @@ Z3.Boolean.mk_eq ctx m z
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
        let formals, body =
          in_creation_order
            (fun () ->
              List.map senv
                ~f:
                  (Tuple2.uncurry Term.mk_var
                  >> of_term ~id ctx env penv z3_fenv dtenv))
            (fun () -> of_term ~id ctx env penv z3_fenv dtenv def)
        in
        Z3.FuncDecl.add_rec_def ctx (Map.Poly.find_exn z3_fenv var) formals body);
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

  (* [f ()] (the conversion of [phi]), with the census of [phi] and the
     conversion's seconds printed under [label] when the census is on *)
  let timed label phi f =
    if not (Lazy.force on) then f ()
    else (
      run phi;
      let t = Common.Clock.now_s () in
      let r = f () in
      Stdlib.Printf.eprintf "[convert-time] %s %.3f s\n%!" label
        (Common.Clock.now_s () -. t);
      r)
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
  let res =
    with_conv_memo ctx (fun () ->
        of_formula_aux ~id ctx uni_senv penv fenv dtenv phi')
  in
  if false then Debug.print @@ lazy ("result: " ^ Z3.Expr.to_string res);
  res

(* [check_sat_base]'s parameter sets kept per instance (see there) *)
let params_memo_on = Atomic.make true
let set_params_memo b = Atomic.set params_memo_on b

(* The conjunct memo: for a caller that asks a run of questions sharing
   their first conjuncts (a linear program's common rows, asked with one set
   of strict rows after another), the Z3 terms of the conjuncts a question
   shares with the previous one, by physical identity, are reused instead of
   converted again, and each question is handed to Z3 as one n-ary [and]
   over its conjuncts rather than as the binary nest [Formula.and_of] built.

   The question Z3 is given is the same:
   - Reuse.  A conjunct physically equal to one converted for the previous
     question, into the same context with the same function and datatype
     environments and instance id, converts to the term held: Z3 hash-conses
     its terms, so converting it again would return that very term while the
     memo keeps it alive.  (Without the memo the term is freed once the
     previous question's wrappers are collected, and made again with a new
     identifier; the memo's case is the one where the collector has not run
     in between, which the plain path meets too.)
   - The n-ary [and].  Z3 rewrites what is asserted, and its rewriting of a
     conjunction flattens a nested [and] by one level at each node, keeps the
     operands in order, drops [true] and repeated operands (the first stays),
     answers [false] for a [false] operand or a complementary pair, and does
     not sort (Z3's [bool_rewriter::mk_flat_and_core] and
     [mk_nflat_and_core]; only disjunctions are sorted).  Bottom-up over the
     left-nested binary chain that is the same pass done one operand at a
     time, so the chain and the n-ary [and] of its operands in the same order
     rewrite to the same term.  On the binary chain that flattening is
     quadratic in its length -- every level copies and hashes the operands
     gathered below it -- and it was most of the time of asserting a linear
     program of a thousand rows.
   The operands not found in the memo are converted from the last to the
   first (or the first to the last under [left_to_right_creation]), the order
   the binary nest creates them in.  A conjunct with a [let] (which the plain
   conversion lifts out of the whole formula) makes the formula take the plain
   conversion.  The memo holds the last question's conjuncts only and lives
   for [with_conjunct_memo]'s scope, in one domain. *)
type conjunct_memo = {
  mutable cj_key : (Z3.context * fenv * dtenv * int option) option;
  mutable cj_entries : (Formula.t * Z3.Expr.expr) list;
}

let conjunct_memo_key : conjunct_memo option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

(* [f ()] with a conjunct memo of its own open in this domain, the previous
   one (if any) restored after *)
let with_conjunct_memo f =
  let saved = Stdlib.Domain.DLS.get conjunct_memo_key in
  Stdlib.Domain.DLS.set conjunct_memo_key
    (Some { cj_key = None; cj_entries = [] });
  Common.Timer.protect
    ~finally:(fun () -> Stdlib.Domain.DLS.set conjunct_memo_key saved)
    f

(* [phi] converted through the memo [memo] (see above), or [None] when a
   conjunct is not let-free and the plain conversion must be used *)
let of_formula_conjunct_memo ~id memo ctx (fenv : fenv) (dtenv : dtenv) phi =
  let conjs = Formula.conjuncts_list_of phi in
  let same_key =
    match memo.cj_key with
    | Some (c, f, d, i) ->
        phys_equal c ctx && phys_equal f fenv && phys_equal d dtenv
        && Option.equal Int.equal i id
    | None -> false
  in
  let rec shared cs es acc =
    match (cs, es) with
    | c :: cs', (p, e) :: es'
      when phys_equal c p || Atomic.get conjunct_memo_mutant_by_position ->
        shared cs' es' (e :: acc)
    | _ -> (List.rev acc, cs)
  in
  let reused, rest =
    shared conjs (if same_key then memo.cj_entries else []) []
  in
  if not (List.for_all rest ~f:Formula.is_let_free) then None
  else
    let fresh =
      with_conv_memo ctx (fun () ->
          of_operands_right_first ~id ctx [] [] fenv dtenv rest)
    in
    let exprs = reused @ fresh in
    ignore (Atomic.fetch_and_add conjunct_memo_hits (List.length reused));
    ignore (Atomic.fetch_and_add conjunct_memo_misses (List.length fresh));
    memo.cj_key <- Some (ctx, fenv, dtenv, id);
    memo.cj_entries <- List.zip_exn conjs exprs;
    Some (match exprs with [ e ] -> e | es -> Z3.Boolean.mk_and ctx es)

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

(* [may_ignore_timeout phi]: [may_not_return phi], or [phi] has a quantifier
   (of any binder sort) and reads a sequence anywhere.  The second arm is wider
   than "a sequence under the quantifier" and is meant to be: cheap, and a
   question it selects for no reason only costs a forked copy.
   Why: Z3 5.1.0, in a context that has been in a scope (a push, a reset), can
   ignore its own [timeout] on such a question and grow without bound -- a
   predicate-elimination validity question quantifying over three integers
   and reading a free sequence by [seq.nth]/[seq.len], which Z3 left undecided
   at its 5 s budget in every other run, ran past 75 s to a 6 GB memory cap in
   one run in fifteen, while the z3 binary given it alone kept the budget.
   [may_not_return] (a sequence-sorted binder) does not cover it, and a shape
   that is otherwise asked must not be refused for it, so the callers that
   select by this test ask the question in a killed copy instead
   ([PCSatCommon.ForkedQuery.first_in_copy]).  A test for a WORKAROUND of
   Z3 5.1.0; remove it with its callers when the reproducer row for
   [benchmarks/SMT/simple/z3_seq_pin_scoped_timeout_unsat.smt2] in
   [script/rerun_external_reproducers.sh] reports GONE for the z3 that opam
   installs. *)
let may_ignore_timeout phi =
  may_not_return phi
  || ((not (Formula.is_quantifier_free phi)) && SeqAxiomEncoding.mentions_seq phi)

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
   variable is counted), which only makes a caller give up a question.
   [recursive_function_applied ~anywhere:true] counts an application outside
   every binder too. *)
let recursive_function_applied ~anywhere (fenv : FunEnv.t) phi =
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
    (not (Set.is_empty reaching)) && formula anywhere phi

let recursive_function_under_binder fenv phi =
  recursive_function_applied ~anywhere:false fenv phi

(* [applies_recursive_function fenv phi]: whether [phi] applies, anywhere, a
   function of [fenv] that is recursive or reaches one.  A recursive
   definition is a universally quantified axiom to the solver, which unfolds
   it lazily; on a quantifier-free question whose refutation needs induction
   over the definition (e.g. [length c <= -1] over a list [c], whose
   refutation needs [length x >= 0] for every [x]) Z3 5.1.0 unfolds without
   end.  So a caller that budgets quantified questions and leaves
   quantifier-free ones unbounded treats such a question as quantified.  The
   test over-approximates (a ground application is counted). *)
let applies_recursive_function fenv phi =
  recursive_function_applied ~anywhere:true fenv phi

(* A caller that reads only whether a question is satisfiable, never the
   model ([is_sat], [is_valid]), says so with [with_model_unread]; [check_sat]
   then has its satisfiable answers come back as [`Sat []] without asking Z3
   for a model -- when no function values are asked for and the question's
   function environment is empty, the case in which nothing inside
   [check_sat] reads the model either (with definitions, the certification of
   a [sat] reads it, so the model is kept there).  Z3 builds a model on
   [get_model] after the check, which on a small linear question cost as much
   as the check (about 2 ms), so it is skipped only where no one reads it:
   the answer is the same, and so is everything decided from it.
   [model_unread] is the switch (process-wide).
   [model_skip_key] is the decision for the current [check_sat], set by it
   and read by [check_sat_z3]. *)
let model_unread = Atomic.make true
let set_model_unread b = Atomic.set model_unread b

let model_unread_key : bool Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> false)

let model_skip_key : bool Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> false)

let model_skips = Atomic.make 0

(* a test's mutant only: skip the model whatever the caller declared *)
let model_unread_mutant_always = Atomic.make false

let with_dls key v f =
  let saved = Stdlib.Domain.DLS.get key in
  Stdlib.Domain.DLS.set key v;
  Common.Timer.protect ~finally:(fun () -> Stdlib.Domain.DLS.set key saved) f

let with_model_unread f = with_dls model_unread_key true f

(* [fun_values_out], when given, receives the interpretations of the model's
   declarations of arity greater than zero ([fun_values_of]) on [SATISFIABLE];
   it is left untouched otherwise.  [model] itself carries no value for such a
   declaration (see [model_of]), so this is the only way a caller that asked
   about an uninterpreted function learns what the solver chose for it. *)
(* Z3 gave up on a question by raising from [check] rather than by answering
   [unknown]: a question whose terms reach Z3's own size limits raises
   [Z3.Error "Overflow encountered when expanding vector"].  Raised by
   [check_sat_z3] for an error of the check alone (an error while asserting
   is this tree's translation going wrong and stays a [Z3.Error]), and turned
   by [check_sat_base] into an undecided answer once the query's scope and
   context are cleaned up. *)
exception Check_gave_up of string

(* Where the last [`Unknown] of a question in this domain came from, for the
   fresh-context retry's narrow mode ([COAR_Z3_FRESH_RETRY=z3-unknown]):
   [z3_said_unknown_key] is set when Z3 itself answered unknown (not timeout
   or canceled) or raised, and cleared when it decided; [declined_key] is set
   when the interface turns a decided Z3 answer into [`Unknown] because it
   cannot certify it.  Both are cleared by the retry before the pooled ask, so
   after it they describe that ask and the questions it asked on the way. *)
let z3_said_unknown_key : bool Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> false)

let declined_key : bool Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> false)

let note_declined ret =
  (match ret with
  | `Unknown _ -> Stdlib.Domain.DLS.set declined_key true
  | _ -> ());
  ret

let check_sat_z3 ?fun_values_out ~query ctx solver dtenv phis =
  Common.PhaseTime.with_phase "assert" (fun () -> z3_solver_add solver phis);
  (* Dump the query as SMT-LIB2 when COAR_DUMP_Z3 is set in the environment.
     This was a dead [if false] branch, which is the same thing with the switch
     welded shut: the one investigation that needed it -- why a quantifier-free
     goal over datatypes with array fields comes back undecided -- could not
     answer "is the query what I think it is" without recompiling.  The lookup
     is done once, not per query. *)
  if dump_z3_queries then
    prerr_endline ("=== Z3 query ===\n" ^ dump_text solver);
  let started = if dump_z3_queries then Common.Clock.now_float () else Time_float.epoch in
  let status =
    try z3_check solver []
    with Z3.Error msg ->
      Stdlib.Domain.DLS.set z3_said_unknown_key true;
      raise (Check_gave_up msg)
  in
  (match status with
  | UNKNOWN -> (
      match Z3.Solver.get_reason_unknown solver with
      | "timeout" | "canceled" -> ()
      | _ -> Stdlib.Domain.DLS.set z3_said_unknown_key true)
  | SATISFIABLE | UNSATISFIABLE -> Stdlib.Domain.DLS.set z3_said_unknown_key false);
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
  | SATISFIABLE
    when Option.is_none fun_values_out && Stdlib.Domain.DLS.get model_skip_key ->
      Atomic.incr model_skips;
      `Sat []
  | SATISFIABLE -> (
      match z3_solver_get_model solver with
      | Some model ->
          if false then print_endline @@ Z3.Model.to_string model;
          (match fun_values_out with
          | Some out -> out := fun_values_of ctx dtenv model
          | None -> ());
          let model =
            Common.PhaseTime.with_phase "model" (fun () ->
                decode_model ctx dtenv model)
          in
          let model =
            match query with
            | `Fresh_context -> model
            | `Query phis ->
                Common.PhaseTime.with_phase "restrict" (fun () ->
                    restrict_model_to_query phis model)
          in
          if false then debug_print_z3_model model;
          `Sat model
      | None -> `Unknown "model production is not enabled?")
  | UNSATISFIABLE -> `Unsat
  | UNKNOWN -> (
      match Z3.Solver.get_reason_unknown solver with
      | "timeout" | "canceled" -> `Timeout
      | reason -> `Unknown reason)

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
      (int * int option * (string * string) list, instance) Hashtbl.Poly.t )
    Hashtbl.Poly.t =
  Hashtbl.Poly.create ()

(* [with_isolated_pools f] is [f ()] with this domain's pooled contexts set
   aside: [f] starts from no pooled context of this domain (the instance
   pool, the clean pool and every arithmetic-solver pool), and on return or
   raise the contexts [f] pooled are dropped and the set-aside ones put back,
   so the questions asked after [f] meet the contexts as the questions before
   [f] left them.  Other domains' entries are untouched throughout.
   Contract: it changes which context a question of [f] runs on, never which
   question is asked or how its answer is read; the context-making
   collection schedule ([new_context_full_major_every]) and the decoding
   tables are shared and still move.
   Why: a pooled context accumulates the declarations and the solver history
   of every earlier question, and a borderline later answer was seen to
   depend on what ran before it; a stage added in front of an existing path
   should not hand that path different contexts. *)
let with_isolated_pools f =
  let d = pool_domain () in
  let mine3 (k, _, _) = k = d in
  let mine4 (k, _, _, _) = k = d in
  let take tbl ~mine =
    let kept = Hashtbl.Poly.copy tbl in
    Hashtbl.Poly.filter_keys_inplace kept ~f:mine;
    Hashtbl.Poly.filter_keys_inplace tbl ~f:(Fn.non mine);
    kept
  in
  let put tbl kept ~mine =
    Hashtbl.Poly.filter_keys_inplace tbl ~f:(Fn.non mine);
    Hashtbl.Poly.iteri kept ~f:(fun ~key ~data ->
        Hashtbl.Poly.set tbl ~key ~data)
  in
  let saved =
    with_pool_lock (fun () ->
        ( take instance_pool ~mine:mine3,
          take clean_pool ~mine:mine4,
          List.map (Hashtbl.Poly.to_alist arith_solver_pools) ~f:(fun (n, t) ->
              (n, take t ~mine:mine3)) ))
  in
  Common.Timer.protect f ~finally:(fun () ->
      let inst, clean, ariths = saved in
      with_pool_lock (fun () ->
          put instance_pool inst ~mine:mine3;
          put clean_pool clean ~mine:mine4;
          Hashtbl.Poly.iter arith_solver_pools ~f:(fun t ->
              Hashtbl.Poly.filter_keys_inplace t ~f:(Fn.non mine3));
          List.iter ariths ~f:(fun (n, kept) ->
              let t =
                Hashtbl.Poly.find_or_add arith_solver_pools n
                  ~default:Hashtbl.Poly.create
              in
              put t kept ~mine:mine3)))

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

(* The bound, in milliseconds, for a query asked with no [timeout] of its own
   at a site that must not outlive the run's budget: what is left of an armed
   [Common.Timer] budget (at least 1 ms), or [None] when no budget is armed,
   in which case nothing changes.

   Why: [Z3.Solver.check], the optimiser's check and a tactic run in native
   code with the runtime released, where the budget's alarm cannot raise, so a
   question Z3 does not decide (a quantified one, an optimisation that does
   not converge) holds the run past its budget until something outside kills
   it, and the run's answer becomes a draw of that kill.  The bound changes no
   answer the run could have given: a question decided before the budget is
   spent is decided as before, and one still undecided when it is spent would
   have met the budget's [Timeout] the moment it returned.  It is not a bound
   over every question: Z3's own [timeout] does not hold over a binder of a
   sequence sort or over regular expressions, which is why such a shape is
   refused before the call ([may_not_return]).  The caller reads the answer
   it gets under this bound as it reads any undecided answer: never as a
   verdict. *)
let armed_budget_ms () =
  Option.map (Common.Timer.remaining_budget ()) ~f:(fun s ->
      Int.max 1 (Float.iround_up_exn (s *. 1000.)))

(* [timeout] if the caller gave one, else [armed_budget_ms ()] *)
let timeout_or_armed_budget = function
  | Some _ as timeout -> timeout
  | None -> armed_budget_ms ()

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

(* Shared by bounded, split and twin rewrites: arbitrary source spellings
   are not reserved by the global counter. *)
let word_fresh_allocator phis =
  let occupied = ref
    (Set.Poly.union_list (List.map phis ~f:Formula.names_spelled_in)) in
  fun prefix ->
    let name = Ident.mk_fresh_tvar_avoiding ~prefix
      ~taken:(fun name -> Set.mem !occupied name) () in
    occupied := Set.add !occupied name;
    name

let word_rewrite_bound_names phis =
  Set.Poly.union_list
    (List.map phis ~f:(fun phi ->
         (Evaluator.scalar_substitution_scope_of
            (Term.mk_fsym_app (T_bool.Formula phi) [])).bound_names))

let word_scalar_substitution_is_safe sub phis =
  List.for_all phis ~f:(Evaluator.scalar_substitution_is_safe sub)

let int_to_bv_bounded_subst phis =
  let fresh_word = word_fresh_allocator phis in
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
            (x, fresh_word "bvr", n) :: acc
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
      (if word_scalar_substitution_is_safe sub phis then
         (List.map phis ~f:(Formula.subst sub), picked)
       else (phis, []))

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
  let fresh_word = word_fresh_allocator phis in
  let free_ints = int_only_free_vars phis in
  let bound = word_rewrite_bound_names phis in
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
          (fresh_word "bvs", n))
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
              Some (fresh_word "bvq")
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
    if not (word_scalar_substitution_is_safe sub phis') then (phis, [])
    else
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
(* [word_interface_lemmas ~closed readings phis]: facts relating the integer
   world of a words question to its bit-vector world, each true in every
   model of the theory.  A READING [(m, t, w)] is an integer term [t] and a
   word [w] of width [m] that stands for [int_to_bv m t]: a word a words
   question forgot ([int_to_bv m t] replaced by a fresh variable), a key and
   its name, and, collected here, every unsigned [ubv_to_int e] of [phis] with
   [e] itself.  For each two readings of one width, and each reading against
   each integer literal [c] of [phis] with [0 < c < 2^m] ([2^m] itself is
   the word 0):
   - congruence: [t = u => w = v];
   - order: [0 <= t < 2^m /\ 0 <= u < 2^m => ((t < u) <=> bvult w v) /\
     ((u < t) <=> bvult v w)] and [0 <= t < 2^m => ((t < c) <=> bvult w c)
     /\ ((t = c) <=> w = c)], since [int_to_bv m] is the identity on
     [[0, 2^m)] read as unsigned words, which it maps in order;
   - homomorphism: for each integer equation [a = b] of [phis] whose sides
     are built from readings' integer terms, numerals, [+], [-], negation and
     products by a numeral, [a = b => bv a = bv b], where [bv] maps a reading
     to its word and the arithmetic to the same operations modulo [2^m]
     ([int_to_bv m] is a ring homomorphism onto the words of width [m]).
   Each lemma holds once every forgotten word is given back its value
   [int_to_bv m t], so adding them to a question weakened by forgetting keeps
   it a consequence of the original: an [unsat] is still one of the original.
   Why: Z3 5.1.0 does not carry an integer order between bounded integers
   into the bit-vector theory (a bit index [i mod 64] below a mask width
   [d mod 64]), and an [ubv_to_int] link left between the two worlds makes it
   slow to the point of not answering; with the worlds separated and only
   these facts between them, a bit-mask obligation that ran past 60 s was
   [unsat] in under a second.  The number of lemmas is quadratic in the
   readings of one width; only closed terms ([closed]) are related. *)
let word_interface_lemmas ~closed readings phis =
  let ubv_readings =
    List.concat_map phis ~f:(fun phi ->
        Set.to_list
        @@ Formula.filtered_terms_of phi ~f:(function
             | Term.FunApp (T_irb.BVToInt (_, signed), [ b ], _) as t ->
                 (not (T_bv.is_signed signed))
                 && closed t
                 && (match Term.sort_of b with
                    | T_bv.SBV (Some _) -> true
                    | _ -> false
                    | exception _ -> false)
             | _ -> false))
    |> List.filter_map ~f:(function
         | Term.FunApp (T_irb.BVToInt _, [ b ], _) as t -> (
             match Term.sort_of b with
             | T_bv.SBV (Some m) -> Some (m, t, b)
             | _ -> None)
         | _ -> None)
  in
  let readings =
    List.dedup_and_sort ~compare:Stdlib.compare (readings @ ubv_readings)
  in
  if List.is_empty readings then []
  else
    let literals =
      List.concat_map phis ~f:(fun phi ->
          Set.to_list
          @@ Formula.filtered_terms_of phi ~f:(function
               | Term.FunApp (T_int.Int c, [], _) -> Z.(gt c zero)
               | _ -> false))
      |> List.filter_map ~f:(function
           | Term.FunApp (T_int.Int c, [], _) -> Some c
           | _ -> None)
      |> List.dedup_and_sort ~compare:Z.compare
    in
    let range m t =
      Formula.and_of
        [
          Formula.leq (T_int.zero ()) t;
          Formula.lt t (T_int.mk_int (Z.shift_left Z.one m));
        ]
    in
    let ult m w v =
      Formula.mk_atom (T_bv.mk_bvlt ~size:(Some m) ~signed:(Some false) w v)
    in
    let bvnum m c = T_bv.mk_bvnum ~size:(Some m) c in
    let rec pairs = function
      | [] -> []
      | r :: rs -> List.map rs ~f:(fun r' -> (r, r')) @ pairs rs
    in
    let pair_lemmas =
      List.concat_map (pairs readings) ~f:(fun ((m, t, w), (m', u, v)) ->
          if m <> m' then []
          else
            [
              Formula.mk_imply (Formula.eq t u) (Formula.eq w v);
              Formula.mk_imply
                (Formula.and_of [ range m t; range m u ])
                (Formula.and_of
                   [
                     Formula.mk_iff (Formula.lt t u) (ult m w v);
                     Formula.mk_iff (Formula.lt u t) (ult m v w);
                   ]);
            ])
    in
    let literal_lemmas =
      List.concat_map readings ~f:(fun (m, t, w) ->
          List.filter_map literals ~f:(fun c ->
              if Z.(geq c (shift_left one m)) then None
              else
                let cl = T_int.mk_int c in
                Some
                  (Formula.mk_imply (range m t)
                     (Formula.and_of
                        [
                          Formula.mk_iff (Formula.lt t cl) (ult m w (bvnum m c));
                          Formula.mk_iff (Formula.eq t cl)
                            (Formula.eq w (bvnum m c));
                        ]))))
    in
    (* [bv m t]: the word of width [m] that [int_to_bv m t] equals, when [t]
       is built from readings of width [m] by ring operations *)
    let rec bv m t =
      match
        List.find readings ~f:(fun (m', t', _) -> m = m' && Stdlib.(t = t'))
      with
      | Some (_, _, w) -> Some (w, true)
      | None -> (
          let size = Some m in
          let un f t1 = Option.map (bv m t1) ~f:(fun (a, r) -> (f a, r)) in
          let bin f t1 t2 =
            match (bv m t1, bv m t2) with
            | Some (a, r1), Some (b, r2) -> Some (f a b, r1 || r2)
            | _ -> None
          in
          match t with
          | Term.FunApp (T_int.Int c, [], _) -> Some (bvnum m c, false)
          | Term.FunApp (T_int.Add, [ t1; t2 ], _) ->
              bin (T_bv.mk_bvadd ~size) t1 t2
          | Term.FunApp (T_int.Sub, [ t1; t2 ], _) ->
              bin (T_bv.mk_bvsub ~size) t1 t2
          | Term.FunApp (T_int.Neg, [ t1 ], _) -> un (T_bv.mk_bvneg ~size) t1
          | Term.FunApp (T_int.Mul, [ (Term.FunApp (T_int.Int _, [], _) as a); t1 ], _)
          | Term.FunApp (T_int.Mul, [ t1; (Term.FunApp (T_int.Int _, [], _) as a) ], _) ->
              bin (T_bv.mk_bvmul ~size) a t1
          | _ -> None)
    in
    let rec atoms acc = function
      | Formula.Atom (atm, _) -> atm :: acc
      | Formula.UnaryOp (_, p, _) -> atoms acc p
      | Formula.BinaryOp (_, p1, p2, _) -> atoms (atoms acc p1) p2
      | _ -> acc
    in
    let widths =
      List.dedup_and_sort ~compare:Int.compare
        (List.map readings ~f:(fun (m, _, _) -> m))
    in
    let hom_lemmas =
      List.fold phis ~init:[] ~f:atoms
      |> List.dedup_and_sort ~compare:Stdlib.compare
      |> List.concat_map ~f:(function
           | Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [ a; b ], _)
             when (try Stdlib.(Term.sort_of a = T_int.SInt)
                   with exn_ when not (Common.Timer.is_async exn_) -> false)
                  && closed a && closed b ->
               let eq = Formula.eq a b in
               List.filter_map widths ~f:(fun m ->
                   match (bv m a, bv m b) with
                   | Some (a', r1), Some (b', r2) when r1 || r2 ->
                       Some (Formula.mk_imply eq (Formula.eq a' b'))
                   | _ -> None)
           | _ -> [])
    in
    pair_lemmas @ literal_lemmas @ hom_lemmas

let int_to_bv_twins_subst ?(generalize = false) ?(interface = false) phis =
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
      (* An outer word must not stand for a value varying beneath a binder.
         Include Boolean aliases and binders in definitions/metadata, not just
         scalar term variables and the outer formula spine. *)
      let bound_names = word_rewrite_bound_names phis in
      let fresh_word = word_fresh_allocator phis in
      let closed t =
        (* Registered function heads can be absent from fvs_of, but a
           same-spelled local binder must still prevent outward abstraction. *)
        Set.are_disjoint
          (Set.union (Term.fvs_of t)
             (Evaluator.scalar_substitution_scope_of t).function_heads)
          bound_names
      in
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
            fresh_word "bvt")
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
      (* The bias/shift identity requires [0 <= k < w]. A divisor must
         likewise keep its positive value at the selected signedness; the
         result interval alone cannot establish either premise. *)
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
            when Atomic.get int_to_bv_pow2_shifts && is_pow2 c
                 && Z.log2 c < w ->
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
            when Atomic.get int_to_bv_pow2_shifts && is_pow2 c
                 && Z.log2 c < w ->
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
              | Some (a, (l, h)) when Z.(geq l zero && lt c (shift_left one w)) ->
                  Some
                    ( T_bv.mk_bvdiv ~size ~signed:(Some false) a (num c),
                      (Z.fdiv l c, Z.fdiv h c) )
              | Some (a, (l, h)) when Z.lt c smax ->
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
              | _ -> None)
          | Term.FunApp
              ( T_int.Rem ((Value.Euclidean | Value.Truncated | Value.Flooring) as md),
                [ t1; Term.FunApp (T_int.Int c, [], _) ],
                _ )
            when Z.(gt c zero) -> (
              match tr t1 with
              | Some (a, (l, h)) when Z.(geq l zero && lt c (shift_left one w)) ->
                  Some
                    ( T_bv.mk_bvrem ~size ~signed:(Some false) a (num c),
                      (Z.zero, Z.min h (Z.pred c)) )
              | Some (a, (l, h)) when Z.lt c smax ->
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
              | _ -> None)
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
        closed (Term.mk_fsym_app (T_bool.Formula (Formula.mk_atom atm)) [])
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
          when is_int t1 && closed_atom atm
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
         per term: the question then forgets [w = int_to_bv m t], so, provided [t] is independent of crossed binders and the word is
         genuinely fresh, it has more models, and its [unsat] -- the only answer a caller of this
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
                           fresh_word "bvw"))
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
        (* With [interface] (and [generalize]), the facts relating the
           forgotten words, the keys' names and the question's
           [ubv_to_int] terms to their integers ([word_interface_lemmas]) *)
        let lemmas =
          if not (interface && generalize) then []
          else
            word_interface_lemmas ~closed
              (Hashtbl.fold general ~init:[] ~f:(fun ~key:(m, t) ~data:v acc ->
                   (m, t, Term.mk_var v (T_bv.SBV (Some m))) :: acc)
              @ Hashtbl.fold names ~init:[] ~f:(fun ~key:k ~data:kb acc ->
                    (n, k, Term.mk_var kb (T_bv.SBV (Some n))) :: acc))
              phis'
        in
        ( phis' @ links @ twins @ lemmas,
          Hashtbl.data names @ Hashtbl.data general )

(* Whether some [phis] contains a word, a term [int_to_bv n t] of a known
   width [n] (searched by [Formula.filtered_terms_of], the traversal each of
   the three rewrites below finds its words by).

   A question with no word is returned unchanged by all three:
   [int_to_bv_bounded_subst] and [int_to_bv_split_subst] collect the widths of
   the words [int_to_bv n x] of a variable [x] and return [(phis, [])] when
   there are none, and [int_to_bv_twins_subst] collects the widths of all
   words and returns [(phis, [])] when there are none; the second and third
   are given the first's result, which is then [phis] itself.  Before
   answering they only compute sets (the names spelled in the question, its
   free integers, its bound names) that nothing outside them reads, and no
   fresh name is drawn before a word is picked.  So [int_to_bv_range_subst]
   and [int_to_bv_words_subst] may answer a wordless question at once with
   the same result; what that skips is those sets, which on the small linear
   questions of a ranking search took about a third of the time each question
   spent in [check_sat] after the call returned.  The one difference: a
   question on which collecting them would raise no longer raises here. *)
let is_int_to_bv_word = function
  | Term.FunApp (T_irb.IntToBV (Some _), [ _ ], _) -> true
  | _ -> false

(* [has_int_to_bv_word] by building the set of words, as it was written
   first; kept as the reference the early-exit search below is tested
   against *)
let has_int_to_bv_word_by_set phis =
  List.exists phis ~f:(fun phi ->
      not
        (Set.is_empty (Formula.filtered_terms_of phi ~f:is_int_to_bv_word)))

(* The same answer as [has_int_to_bv_word_by_set], found by a search that
   stops at the first word and allocates nothing.

   Contract: [term_has_word t] holds exactly when
   [Term.filtered_terms_of ~f:is_int_to_bv_word t] is not empty, and likewise
   [atom_has_word] and [formula_has_word] for [Atom] and [Formula].  Proof: it
   visits the subterms that [filtered_terms_of] visits, in the same places --
   a term itself, the arguments of an application, both parts of a [let],
   the formula inside a [T_bool.Formula], NOT the body of an array [lambda],
   an atom's arguments and a fixpoint predicate's body, both operands of a
   connective, a binder's body and its [Random] terms, the bodies of a
   [let rec]'s functions and its own body, and a [let]-formula's definition
   and body (which [filtered_terms_of] reads as the term
   [let x = def in Formula body], whose root is no word).  The only thing
   [filtered_terms_of] removes from what it collects is the set of
   variables a binder or a [let rec] function binds ([Set.diff]), and a
   word is an application, never a variable, so no word found is removed:
   the set is non-empty iff some visited term is a word.  The difference
   is cost alone -- no set is built and no structural comparison of terms is
   made (the set's), which on MuStrat's small questions was a third of the
   time the question spent before conversion -- except that a question on
   which building that set would raise no longer raises. *)
let rec term_has_word t =
  is_int_to_bv_word t
  ||
  match t with
  | Term.FunApp (T_bool.Formula phi, _, _) -> formula_has_word phi
  | Term.FunApp (T_array.ALambda _, _, _) -> false
  | Term.FunApp (_, args, _) -> List.exists args ~f:term_has_word
  | Term.LetTerm (_, _, def, body, _) -> term_has_word def || term_has_word body
  | Term.Var _ -> false

and atom_has_word = function
  | Atom.True _ | Atom.False _ -> false
  | Atom.App (Predicate.Fixpoint def, args, _) ->
      formula_has_word def.body || List.exists args ~f:term_has_word
  | Atom.App (_, args, _) -> List.exists args ~f:term_has_word

and formula_has_word = function
  | Formula.Atom (atom, _) -> atom_has_word atom
  | Formula.UnaryOp (_, phi, _) -> formula_has_word phi
  | Formula.BinaryOp (_, phi1, phi2, _) ->
      formula_has_word phi1 || formula_has_word phi2
  | Formula.Bind (binder, _, phi, _) ->
      formula_has_word phi
      ||
      (match binder with
      | Formula.Random rand -> List.exists (Rand.terms_of rand) ~f:term_has_word
      | Formula.Forall | Formula.Exists -> false)
  | Formula.LetRec (funcs, phi, _) ->
      formula_has_word phi
      || List.exists funcs ~f:(fun def -> formula_has_word def.body)
  | Formula.LetFormula (_, _, def, body, _) ->
      term_has_word def || formula_has_word body

let has_int_to_bv_word phis = List.exists phis ~f:formula_has_word

(* Whether [int_to_bv_range_subst] and [int_to_bv_words_subst] answer a
   wordless question without running the rewrites (see
   [has_int_to_bv_word]); on by default, a switch so that a test can compare
   the two.  [int_to_bv_wordless_skips] counts the questions answered so. *)
let int_to_bv_skip_wordless = Atomic.make true
let set_int_to_bv_skip_wordless b = Atomic.set int_to_bv_skip_wordless b
let int_to_bv_wordless_skips = Atomic.make 0

(* the three rewrites in turn, whatever the question *)
let int_to_bv_range_subst_all phis =
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

(* [int_to_bv_range_subst_with ~has_word phis]: [int_to_bv_range_subst] with
   the word test given (a test passes a wrong one to see it caught) *)
let int_to_bv_range_subst_with ~has_word phis =
  if Atomic.get int_to_bv_skip_wordless && not (has_word phis) then (
    Atomic.incr int_to_bv_wordless_skips;
    (phis, []))
  else int_to_bv_range_subst_all phis

let int_to_bv_range_subst phis =
  int_to_bv_range_subst_with ~has_word:has_int_to_bv_word phis

(* [int_to_bv_range_subst] with the twins and the generalisation of the
   words no key translates ([int_to_bv_twins_subst ~generalize:true]),
   whatever the switches; [None] when the twins step changes nothing.  The
   result is weaker than the question under the guarded binder-independence
   and fresh-name premises (it may have more models), so only its
   [unsat] may be read, as the question's [unsat]. *)
let int_to_bv_words_subst phis =
  if Atomic.get int_to_bv_skip_wordless && not (has_int_to_bv_word phis) then (
    Atomic.incr int_to_bv_wordless_skips;
    None)
  else
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
    (* each name read at the sort the rewrite gave it: [xb] a word of [n] bits,
       [q] an integer *)
    let find z srt = model_value model (z, srt) in
    let value_of xb n q =
      match find xb (T_bv.SBV (Some n)) with
      | Some (Term.FunApp (T_bv.BVNum (_, z), [], _)) -> (
          let low = Z.erem z (Z.shift_left Z.one n) in
          match q with
          | None -> Some (T_int.mk_int low)
          | Some q -> (
              match find q T_int.SInt with
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

(* true while [check_sat_fresh] asks its question, so that a line of the log
   above says whether it is a fresh-context retry; read only by the log *)
let fresh_retry_in_progress_key = Stdlib.Domain.DLS.new_key (fun () -> false)

(* With [COAR_Z3_ALT_LOG=path], every quantified question asked in a pooled
   context is asked twice more after its own check, for comparison: with Z3's
   "default" tactic as a solver in the same context, and in a context of its
   own as [check_sat_fresh] asks it.  The caller gets the pooled answer, except
   that an [`Unknown] the context of its own decides is replaced by that
   decision, as the always-on retry would replace it.  One line per
   alternative: the route, the pooled outcome and seconds, the alternative's
   outcome and seconds, the functions the context (for [fresh], the problem)
   declares and those the question reaches.  A diagnostic: read once at
   start-up, nothing written without it. *)
let z3_alt_log_path = Sys.getenv "COAR_Z3_ALT_LOG"

let z3_alt_log line =
  Option.iter z3_alt_log_path ~f:(fun path ->
      Out_channel.with_file path ~append:true ~f:(fun oc ->
          Out_channel.output_string oc line))

let str_of_status_with solver = function
  | Z3.Solver.SATISFIABLE -> "sat"
  | Z3.Solver.UNSATISFIABLE -> "unsat"
  | Z3.Solver.UNKNOWN ->
      let r = Z3.Solver.get_reason_unknown solver in
      if String.is_substring r ~substring:"timeout"
         || String.is_substring r ~substring:"canceled"
      then "timeout"
      else "unknown"


(* the resident memory of this process in KB (pages of 4 KB), -1 when it
   cannot be read *)
let resident_kb () =
  match In_channel.read_all "/proc/self/statm" |> String.split ~on:' ' with
  | _ :: rss :: _ -> (
      match Int.of_string_opt rss with Some pages -> pages * 4 | None -> -1)
  | _ -> -1
  | exception exn_ when not (Common.Timer.is_async exn_) -> -1

(* With [COAR_MEM_LOG=path], one line per check of [check_sat_base] is
   appended to [path] after the check and its clean-up: the process id, the
   open phase, whether the context was the question's own and the goal
   quantified, the goal's size, the seconds taken, and before/after readings
   of the resident set, the OCaml major heap and Z3's own count of the bytes
   it holds ([z3_alloc_mb]), all in MB.  With [COAR_MEM_LOG_GC] set too, a
   full major collection follows and the three readings are taken again, so
   that memory still held after it is told apart from memory only waiting for
   the collector.  A diagnostic: without the variable nothing is read or
   written, and with it the questions and answers are unchanged (the
   collection only moves the collector's timing). *)
let mem_log_path = Sys.getenv "COAR_MEM_LOG"
let mem_log_gc = Option.is_some (Sys.getenv "COAR_MEM_LOG_GC")

let mem_log_check ~fresh_solver ~quantified phis =
  match mem_log_path with
  | None -> fun () -> ()
  | Some path ->
      let heap () =
        (Gc.quick_stat ()).heap_words * (Stdlib.Sys.word_size / 8) / 1_048_576
      in
      let phase = Common.PhaseTime.current_path () in
      let t0 = Common.Clock.now_s () in
      let rss0 = rss_mb () and heap0 = heap () and z0 = z3_alloc_mb () in
      fun () ->
        let secs = Common.Clock.now_s () -. t0 in
        let rss1 = rss_mb () and heap1 = heap () and z1 = z3_alloc_mb () in
        let rss2, heap2, z2 =
          if mem_log_gc then (
            Gc.full_major ();
            (rss_mb (), heap (), z3_alloc_mb ()))
          else (-1, -1, -1)
        in
        let line =
          sprintf "%d\t%s\t%b\t%b\t%d\t%.3f\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n"
            (Core_unix.getpid () |> Pid.to_int)
            phase fresh_solver quantified
            (List.sum (module Int) phis ~f:Formula.ast_size)
            secs rss0 rss1 rss2 heap0 heap1 heap2 z0 z1 z2
        in
        try
          Out_channel.with_file path ~append:true ~f:(fun oc ->
              Out_channel.output_string oc line)
        with exn_ when not (Common.Timer.is_async exn_) -> ()

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

(* A diagnostic of how a question asked in a context of its own fares in
   this process against the same question asked again: with
   [COAR_Z3_INPROC_REPLAY=MIN_SIZE:MAX_COUNT:BUDGET_MS:FILE] in the
   environment, each of the first MAX_COUNT such questions of at least
   MIN_SIZE nodes appends a line to FILE for its own check (outcome, wall
   seconds, the asking thread's CPU seconds, Z3's resource units spent, the
   load average, the OCaml major heap in MB), and is then asked twice more
   under BUDGET_MS, each in a new context made with the same configuration
   and parameters: once with the asserted expressions translated into it
   ([translate], the same term DAG), once with the solver's printed text
   parsed into it (what a replay of the dumped file reads).  The replays'
   answers are only logged; the question's own answer is returned unchanged.
   Without the variable nothing is read, measured or asked.  The translated
   replay is not made unless asked for ([inproc_replay_variants]): with it,
   two of eleven solver runs ended in a heap corruption (an abort, a bus
   error), because a term or model copied by [translate] is wrapped by the
   OCaml bindings with the context it was copied FROM, so it outlives the
   context it belongs to and is released through the wrong one. *)
let inproc_replay =
  match Sys.getenv "COAR_Z3_INPROC_REPLAY" with
  | None -> None
  | Some spec -> (
      match String.lsplit2 spec ~on:':' with
      | None -> None
      | Some (min_size, rest) -> (
          match String.split rest ~on:':' with
          | max_count :: budget :: file ->
              Some
                ( Int.of_string min_size,
                  Atomic.make (Int.of_string max_count),
                  Int.of_string budget,
                  String.concat ~sep:":" file )
          | _ -> None))

(* which replays to make, by letter: S same context, R reconverted,
   T translated, P parsed ([COAR_Z3_INPROC_REPLAY_VARIANTS], default SRP);
   a BUDGET_MS of 0 replays under the question's own budget.

   T is asked for by name only, because it can corrupt the heap: the OCaml
   bindings wrap the result of [Z3.Expr.translate e dst] with the context of
   [e], not [dst], so the copies neither keep [dst] alive nor are released
   through it.  When [dst]'s own handles are collected first, [dst] is
   deleted under the live copies and their finalizers then touch freed
   memory; when a copy is the last holder of a term, its release frees the
   term into the source context's allocator.  P renumbers the question the
   same way (the reader creates terms left to right, as [translate] does)
   with every object made by a call on the context it belongs to. *)
let inproc_replay_variants =
  Option.value (Sys.getenv "COAR_Z3_INPROC_REPLAY_VARIANTS") ~default:"SRP"

let inproc_replay_wants c = String.mem inproc_replay_variants c

let inproc_replay_thread_cpu =
  match Core_unix.Clock.gettime with
  | Ok gettime ->
      fun () -> Int63.to_float (gettime Core_unix.Clock.Process_thread) /. 1e9
  | Error _ ->
      fun () ->
        let t = Core_unix.times () in
        t.tms_utime +. t.tms_stime

let inproc_replay_load () =
  try
    match String.split ~on:' ' (In_channel.read_all "/proc/loadavg") with
    | l :: _ -> l
    | [] -> "na"
  with exn_ when not (Common.Timer.is_async exn_) -> "na"

let inproc_replay_rlimit solver =
  try
    match
      Z3.Statistics.get (Z3.Solver.get_statistics solver) "rlimit count"
    with
    | Some e -> Float.of_string_opt (Z3.Statistics.Entry.to_string_value e)
    | None -> None
  with exn_ when not (Common.Timer.is_async exn_) -> None

(* [measured solver] checks [solver] and returns its outcome with the wall
   seconds, the thread's CPU seconds and the resource units it spent *)
let inproc_replay_measured solver =
  let r0 = inproc_replay_rlimit solver in
  let c0 = inproc_replay_thread_cpu () and w0 = Common.Clock.now_s () in
  let st = Z3.Solver.check solver [] in
  let w = Common.Clock.now_s () -. w0 and c = inproc_replay_thread_cpu () -. c0 in
  let units =
    match (r0, inproc_replay_rlimit solver) with
    | Some a, Some b -> sprintf "%.0f" (b -. a)
    | None, Some b -> sprintf "%.0f" b
    | _ -> "na"
  in
  (str_of_status_with solver st, w, c, units)

let inproc_replay_line file fields =
  Out_channel.with_file file ~append:true ~f:(fun oc ->
      Out_channel.output_string oc (String.concat ~sep:"\t" fields ^ "\n"))

let inproc_replay_heap_mb () =
  (Gc.quick_stat ()).heap_words * (Stdlib.Sys.word_size / 8) / 1_048_576

(* Keep the explicit Boolean-equation API contract separate from the broader
   file-context admission and Horn export family below. *)
let supports_boolean_equations (fenv : FunEnv.t) =
  (not (Map.Poly.is_empty fenv))
  && List.for_all (Map.Poly.data fenv) ~f:(fun (params, sret, _, _, property) ->
      Term.is_bool_sort sret
      && List.for_all params ~f:(snd >> Term.is_bool_sort)
      && Formula.is_true property)

(* Refutation may use eligible entries (Bool, Int and Real signatures with a
   true property) even when a sibling is unsupported.
   All signatures are retained; this makes no full-model certificate. *)
let supports_defining_equation_instances (fenv : FunEnv.t) =
  let supported s =
    Term.is_bool_sort s || Term.is_int_sort s || Term.is_real_sort s in
  List.exists (Map.Poly.data fenv) ~f:(fun (params, sret, _, _, property) ->
      supported sret
      && List.for_all params ~f:(snd >> supported)
      && Formula.is_true property)

(* A first-order sort whose values the SMT-LIB theory fixes the way Z3 reads
   them, so that an equation instance at such a formal is a consequence of the
   universally quantified defining equation as the theory states it: Bool,
   Int, Real, a bit-vector of known width, an array, a sequence or a tuple of
   such sorts, a declared sort, and a monomorphic datatype from which only
   inductive datatypes and declared sorts are reachable.  A codatatype is
   excluded: Z3 has none and reads one as an inductive datatype, whose
   acyclicity would refute [g x = cons(0, g x)], which has the cyclic value
   as its solution over a codatatype.  An arrow, a sort variable, a string,
   a regular expression or a trace sort is outside. *)
let rec first_order_instance_sort = function
  | T_bool.SBool | T_int.SInt | T_real.SReal -> true
  | T_bv.SBV (Some _) -> true
  | T_array.SArray (s1, s2) ->
      first_order_instance_sort s1 && first_order_instance_sort s2
  | T_seq.SSeq s -> first_order_instance_sort s
  | T_tuple.STuple sorts -> List.for_all sorts ~f:first_order_instance_sort
  | T_dt.SUS (_, sorts) -> List.for_all sorts ~f:first_order_instance_sort
  | T_dt.SDT dt ->
      let dts, field_sorts = Datatype.used_dt_and_sorts_of dt in
      (not (Datatype.is_poly dt))
      && (Datatype.is_dt dt || Datatype.is_undef dt)
      && Set.for_all dts ~f:(fun dt -> Datatype.is_dt dt || Datatype.is_undef dt)
      && List.for_all (Datatype.params_of dt) ~f:first_order_instance_sort
      && Set.for_all field_sorts ~f:(function
           | T_dt.SDT _ -> true
           | sort -> first_order_instance_sort sort)
  | _ -> false

let first_order_instance_entry (params, sret, _, _, property) =
  first_order_instance_sort sret
  && List.for_all params ~f:(snd >> first_order_instance_sort)
  && Formula.is_true property

(* The general instance route below may use an entry with any first-order
   signature; an entry outside it (an arrow, a property) is declared but
   contributes no instance. *)
let supports_first_order_defining_instances (fenv : FunEnv.t) =
  List.exists (Map.Poly.data fenv) ~f:first_order_instance_entry

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

(* Ground instances of the defining equations: each integer (real) formal is
   instantiated at 0 (0.0) and at every integer (real) literal that some call of the same
   function passes at that position, in a (let-eliminated) defining body or in
   [phis]; Boolean formals stay universal.  Every instance is a consequence of
   the universally quantified equation, so any set of them is a sound
   necessary condition; the literal positions are the cells a recursion such
   as [f x = ite (x = 1) (f 1 + 1) 0] constrains, which the instance at 0
   alone never reads (that equation has no solution, and only its instance at
   1 says so).  At most [max_defining_instances] argument vectors are taken per
   function, 0 first; dropping vectors only weakens the condition.  Inner
   binders and definition-site globals retain their scopes. These are
   necessary defining equalities, not a total function-model certificate. *)
let max_defining_instances = 16

let defining_equation_instances_of ?(first_order = false) ?(phis = [])
    (fenv : FunEnv.t) =
  let eligible (var, entry) =
    if first_order then first_order_instance_entry entry
    else supports_defining_equation_instances (Map.Poly.singleton var entry)
  in
  if not (List.exists (Map.Poly.to_alist fenv) ~f:eligible) then
    invalid_arg "Defining equation instances require at least one eligible entry";
  let let_free body = if Term.is_let_free body then body else Term.elim_let body in
  let calls =
    Set.Poly.union_list
      (List.map phis ~f:Formula.fvar_apps_of
       @ List.map (Map.Poly.data fenv) ~f:(fun (_, _, body, _, _) ->
           Term.fvar_apps_of (let_free body)))
  in
  let literals_at var i =
    Set.to_list calls
    |> List.filter_map ~f:(function
         | Term.FunApp (FVar (callee, _, _), args, _)
           when Ident.tvar_equal callee var -> (
             match List.nth args i with
             | Some arg -> (
                 match Evaluator.simplify_term arg with
                 | Term.FunApp ((T_int.Int _ | T_real.Real _), [], _) as lit ->
                     Some lit
                 | _ -> None
                 | exception exn_ when not (Common.Timer.is_async exn_) -> None)
             | None -> None)
         | _ -> None)
  in
  let int_literals var i =
    List.filter_map (literals_at var i) ~f:(function
      | Term.FunApp (T_int.Int n, [], _) when not (Z.equal n Z.zero) -> Some n
      | _ -> None)
    |> List.dedup_and_sort ~compare:Z.compare
  in
  let real_literals var i =
    List.filter_map (literals_at var i) ~f:(function
      | Term.FunApp (T_real.Real q, [], _) when not (Q.equal q Q.zero) -> Some q
      | _ -> None)
    |> List.dedup_and_sort ~compare:Q.compare
  in
  (* The general route (first_order): a formal of any other first-order sort
     stays universal, and is in addition instantiated at the closed
     background terms that some call of the same function passes at that
     position ([f (cons 1 nil)], [f #x05]): a variable-free term over theory
     symbols, with no function variable, binder, array lambda or embedded
     formula, so that the instance is a consequence of the equation and
     substituting it captures nothing. *)
  let background_ground_term t =
    Set.is_empty (Term.term_sort_env_of t)
    && Set.is_empty
         (Term.filtered_terms_of t ~f:(function
           | Term.Var _ | Term.LetTerm _ -> true
           | Term.FunApp ((FVar _ | T_bool.Formula _ | T_array.ALambda _), _, _) ->
               true
           | _ -> false))
  in
  let ground_args_at var i sort =
    Set.to_list calls
    |> List.filter_map ~f:(function
         | Term.FunApp (FVar (callee, _, _), args, _)
           when Ident.tvar_equal callee var -> (
             match List.nth args i with
             | Some arg
               when background_ground_term arg
                    && Stdlib.(Term.sort_of arg = sort) ->
                 Some arg
             | _ -> None
             | exception exn_ when not (Common.Timer.is_async exn_) -> None)
         | _ -> None)
    |> List.dedup_and_sort ~compare:(fun a b ->
           let c = Int.compare (Term.ast_size a) (Term.ast_size b) in
           if c <> 0 then c else Stdlib.compare a b)
  in
  Map.Poly.to_alist fenv
  |> List.filter ~f:eligible
  |> List.concat_map ~f:(fun (var, (params, sret, body, _, _)) ->
      let choices =
        List.mapi params ~f:(fun i (formal, sort) ->
            if Term.is_int_sort sort then
              List.map ~f:(fun n -> Some (formal, T_int.mk_int n))
                (Z.zero :: int_literals var i)
            else if Term.is_real_sort sort then
              List.map ~f:(fun q -> Some (formal, T_real.mk_real q))
                (Q.zero :: real_literals var i)
            else if first_order && not (Term.is_bool_sort sort) then
              None
              :: List.map (ground_args_at var i sort) ~f:(fun t ->
                     Some (formal, t))
            else [ None ])
      in
      (* the vectors in the order of the full product (the first position
         varying slowest), built lazily so that only the vectors taken are
         ever formed: the product over n integer positions has up to
         (literals + 1)^n members, and forming it before the cut would make
         a definition with thirty integer formals and one literal each build
         2^30 vectors to keep 16 *)
      let vectors =
        let rec product = function
          | [] -> Sequence.singleton []
          | choice :: rest ->
              Sequence.concat_map (Sequence.of_list choice) ~f:(fun c ->
                  Sequence.map (product rest) ~f:(fun tail -> c :: tail))
        in
        Sequence.to_list (Sequence.take (product choices) max_defining_instances)
      in
      let body = let_free body in
      List.map vectors ~f:(fun vector ->
          let args =
            List.map2_exn params vector ~f:(fun (formal, sort) -> function
              | Some (_, value) -> value
              | None -> Term.mk_var formal sort)
          in
          let sub = Map.Poly.of_alist_exn (List.filter_opt vector) in
          let lhs =
            Term.mk_fsym_app (FVar (var, List.map params ~f:snd, sret)) args
          in
          (* the formals left universal: every Boolean one, and on the
             general route each other formal not instantiated in this vector *)
          Formula.mk_forall_if_bounded
            (List.filter_map (List.zip_exn params vector) ~f:(function
               | p, None -> Some p
               | _, Some _ -> None))
            (Formula.eq lhs (Term.subst sub body))))

let boolean_defining_equations = defining_equations_of

(* Pure-unknown elimination: the satisfiability of a conjunction of formulas in
   which the unknowns (predicate variables) are uninterpreted predicates is
   preserved when an unknown that occurs only positively is replaced by [true]
   and one that occurs only negatively by [false] -- the conjunction is
   monotone (antitone) in it, so a model with any interpretation of it gives
   one with the constant -- and the result is simplified by constant
   propagation alone, dropping the formulas that become [true].  Repeated to a
   fixed point, since dropping a formula can leave another unknown pure.
   An occurrence inside a term (an embedded formula), an [iff], an [xor], a
   [let] definition or a recursive [let] counts as both polarities, and so does
   one under a probabilistic binder, whose body is not a plain conjunct; those
   unknowns are never replaced.

   Contract: [reduce_pure_unknowns phis] is satisfiable, with the unknowns read
   as uninterpreted predicates, exactly when [phis] is; it mentions no unknown
   [phis] does not; its formulas are no larger.  It is not a model-preserving
   rewrite: a model of the result interprets only the unknowns left.

   Why: the file entry's known-function admission asks whether instances of
   the defining equations are consistent with the whole problem read this
   way; on a generated input of 469 clauses (1.16 million nodes) most of the
   nodes sit under unknowns that occur at one polarity only, and the reduced
   question is a seventh of the size, where converting and asserting the
   whole of it took longer than the one-second check it was for. *)
let reduce_pure_unknowns (phis : Formula.t list) =
  let polarities phis =
    let tbl = Hashtbl.Poly.create () in
    let add p pol =
      Hashtbl.update tbl p ~f:(function
        | None -> (pol, not pol)
        | Some (pos, neg) -> (pos || pol, neg || not pol))
    in
    let both pvs = Set.iter pvs ~f:(fun p -> add p true; add p false) in
    let rec go pol = function
      | Formula.Atom (Atom.App (Predicate.Var (p, _), args, _), _) ->
          add p pol;
          List.iter args ~f:(fun t -> both (Term.pvs_of t))
      | Formula.Atom (a, _) -> both (Atom.pvs_of a)
      | Formula.UnaryOp (Formula.Not, phi, _) -> go (not pol) phi
      | Formula.BinaryOp ((Formula.And | Formula.Or), a, b, _) ->
          go pol a;
          go pol b
      | Formula.BinaryOp (Formula.Imply, a, b, _) ->
          go (not pol) a;
          go pol b
      | Formula.BinaryOp ((Formula.Iff | Formula.Xor), _, _, _) as phi ->
          both (Formula.pvs_of phi)
      | Formula.Bind (Formula.Random _, _, _, _) as phi -> both (Formula.pvs_of phi)
      | Formula.Bind (_, _, phi, _) -> go pol phi
      | Formula.LetRec _ as phi -> both (Formula.pvs_of phi)
      | Formula.LetFormula (_, _, def, body, _) ->
          both (Term.pvs_of def);
          go pol body
    in
    List.iter phis ~f:(go true);
    tbl
  in
  (* [phi] with the unknowns of [sub] replaced, simplified by constant
     propagation; a subformula with no replaced unknown is kept as it is *)
  let rec replace sub phi =
    match phi with
    | Formula.Atom (Atom.App (Predicate.Var (p, _), _, _), _) -> (
        match Map.Poly.find sub p with
        | Some true -> Formula.mk_true ()
        | Some false -> Formula.mk_false ()
        | None -> phi)
    | Formula.Atom _ -> phi
    | Formula.UnaryOp (Formula.Not, a, info) ->
        let a' = replace sub a in
        if Formula.is_true a' then Formula.mk_false ()
        else if Formula.is_false a' then Formula.mk_true ()
        else if phys_equal a a' then phi
        else Formula.mk_neg ~info a'
    | Formula.BinaryOp (Formula.And, a, b, info) ->
        let a' = replace sub a and b' = replace sub b in
        if Formula.is_false a' || Formula.is_false b' then Formula.mk_false ()
        else if Formula.is_true a' then b'
        else if Formula.is_true b' then a'
        else if phys_equal a a' && phys_equal b b' then phi
        else Formula.mk_and ~info a' b'
    | Formula.BinaryOp (Formula.Or, a, b, info) ->
        let a' = replace sub a and b' = replace sub b in
        if Formula.is_true a' || Formula.is_true b' then Formula.mk_true ()
        else if Formula.is_false a' then b'
        else if Formula.is_false b' then a'
        else if phys_equal a a' && phys_equal b b' then phi
        else Formula.mk_or ~info a' b'
    | Formula.BinaryOp (Formula.Imply, a, b, info) ->
        let a' = replace sub a and b' = replace sub b in
        if Formula.is_false a' || Formula.is_true b' then Formula.mk_true ()
        else if Formula.is_true a' then b'
        else if Formula.is_false b' then replace sub (Formula.mk_neg ~info a')
        else if phys_equal a a' && phys_equal b b' then phi
        else Formula.mk_imply ~info a' b'
    | Formula.BinaryOp ((Formula.Iff | Formula.Xor), _, _, _) -> phi
    | Formula.Bind (Formula.Random _, _, _, _) -> phi
    | Formula.Bind (binder, senv, a, info) ->
        (* a sort's carrier is never empty, so a quantifier over a constant
           body is that constant *)
        let a' = replace sub a in
        if Formula.is_true a' || Formula.is_false a' then a'
        else if phys_equal a a' then phi
        else Formula.mk_bind ~info binder senv a'
    | Formula.LetRec _ -> phi
    | Formula.LetFormula (x, s, def, body, info) ->
        let body' = replace sub body in
        if Formula.is_true body' || Formula.is_false body' then body'
        else if phys_equal body body' then phi
        else Formula.mk_let_formula ~info x s def body'
  in
  let rec fix phis =
    let sub =
      Hashtbl.fold (polarities phis) ~init:Map.Poly.empty
        ~f:(fun ~key ~data sub ->
          match data with
          | true, false -> Map.Poly.set sub ~key ~data:true
          | false, true -> Map.Poly.set sub ~key ~data:false
          | _ -> sub)
    in
    if Map.Poly.is_empty sub then phis
    else
      fix
        (List.filter_map phis ~f:(fun phi ->
             let phi = replace sub phi in
             if Formula.is_true phi then None else Some phi))
  in
  fix phis

let check_sat_base =
  let cfg = [ ("model", "true") ] in
  let cfg = if validate then cfg @ validate_cfg else cfg in
  fun ?(timeout = None)
    ?(fresh_solver = false)
    ?(scoped = false)
    ?(boolean_equations = false)
    ?(defining_equations = false)
    ?(defining_equation_instances = false)
    ?(first_order_instances = false)
    ?(reduce_pure = false)
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
      (first_order_instances && not defining_equation_instances)
      || defining_equation_instances
         && (full_equations || not fresh_solver
            || not
                 (if first_order_instances then
                    supports_first_order_defining_instances fenv
                  else supports_defining_equation_instances fenv))
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
    let fenv =
      if ordinary_definitions then fenv
      else
        Common.PhaseTime.with_phase "fenv-query" (fun () ->
            fenv_for_query fenv phis)
    in
    let phis =
      if defining_equation_instances then
        defining_equation_instances_of ~first_order:first_order_instances ~phis
          fenv
        @ phis
      else if full_equations then defining_equations_of fenv @ phis
      else phis
    in
    (* [reduce_pure]: the question's satisfiability with the unknowns read as
       uninterpreted predicates is all its caller reads, which pure-unknown
       elimination preserves ([reduce_pure_unknowns]); applied after the
       instances are drawn from the calls of the whole question *)
    let phis =
      if reduce_pure then
        Common.PhaseTime.with_phase "pure" (fun () -> reduce_pure_unknowns phis)
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
       goal reaches, and puts the goal in negation normal form.
       Z3 5.1.0 keeps the first two conditions and drops the third (the
       negated-existential form decides as the plain one does).  The two that
       remain are different mechanisms: the scope condition belongs to the
       default solver alone -- Z3's "default" tactic made a solver of the same
       pushed context decides as a fresh context does -- while a recursive
       definition anywhere in the context makes the elimination of
       unconstrained terms eliminate nothing in the tested solver configurations,
       tactic or not; among these tests only a context without the definition
       recovers it.
       A question that applies a recursive function cannot have both. *)
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
      let memo = Stdlib.Domain.DLS.get conjunct_memo_key in
      with_conv_memo ctx (fun () ->
      List.map phis
        ~f:(fun phi ->
          ConvertCensus.timed "native" phi (fun () ->
              match
                Option.bind memo ~f:(fun memo ->
                    of_formula_conjunct_memo ~id memo ctx instance.fenv
                      instance.dtenv phi)
              with
              | Some e -> e
              | None ->
                  of_formula_with_z3fenv ~id ctx [] [] instance.fenv
                    instance.dtenv phi))))
    in
    (* Empty parameter sets do not clear a pooled solver's previous timeout.
       The rlimit is set only when one is asked for ([with_rlimit]), and put
       back to 0 (no limit) afterwards, so a query asked without one sets
       exactly the parameters it set before the option existed. *)
    let rlimit = Stdlib.Domain.DLS.get rlimit_key in
    (* A parameter set is made once per instance and (timeout, resource
       limit, arithmetic solver) and handed to the solver again later
       ([params_memo], switch [params_memo_on]): [set_parameters] copies the
       values into the solver, so an equal set made again would set exactly
       the same; only its construction (a parameter object, a symbol per
       name) is skipped.  At most a handful of keys occur per instance
       (the caller's budgets, and 0 to clear). *)
    let set_timeout ?rlimit milliseconds =
      let make () =
        let params = Z3.Params.mk_params ctx in
        Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") milliseconds;
        Option.iter rlimit ~f:(fun r ->
            Z3.Params.add_int params (Z3.Symbol.mk_string ctx "rlimit") r);
        add_arith_solver_param ctx params arith_solver;
        params
      in
      let params =
        if not (Atomic.get params_memo_on) then make ()
        else
          let key = (milliseconds, rlimit, arith_solver) in
          match
            List.Assoc.find instance.params_memo key ~equal:(fun (a, b, c) (a', b', c') ->
                a = a' && Option.equal Int.equal b b' && Option.equal Int.equal c c')
          with
          | Some p -> p
          | None ->
              let p = make () in
              if List.length instance.params_memo < 16 then
                instance.params_memo <- (key, p) :: instance.params_memo;
              p
      in
      Z3.Solver.set_parameters solver params
    in
    Common.PhaseTime.with_phase "params" (fun () ->
        set_timeout ?rlimit (Option.value timeout ~default:0));
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
    Common.PhaseTime.with_phase "push" (fun () ->
        if fresh_solver then ()
        else if unscoped then z3_solver_reset solver
        else Z3.Solver.push solver);
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
    (* Hooks and diagnostic logging may raise after the query opens its scope.
       Keep cleanup independent of every such callback, and discard a clean
       lease unless the entire result path completed normally. *)
    let raised = ref true in
    let mem_log_done = mem_log_check ~fresh_solver ~quantified phis in
    Common.Timer.protect
      ~finally:(fun () ->
        Common.PhaseTime.with_phase "pop" (fun () -> finally ~raised:!raised);
        mem_log_done ())
      (fun () ->
      !query_solver_hook ctx solver;
      let log_check =
        match Stdlib.Domain.DLS.get rlimit_label_key with
        | None -> fun _ -> ()
        | Some label ->
            let before = rlimit_count_of solver in
            let t0 = Common.Clock.now_s () in
            fun outcome ->
              let after = rlimit_count_of solver in
              rlimit_log_line
                (sprintf "CHECK\t%d\t%s\t%s\t%.3f\t%s\t%d\t%d\t%b\t%b"
                   (Core_unix.getpid () |> Pid.to_int)
                   label
                   (match (before, after) with
                   | Some b, Some a -> sprintf "%.0f" (a -. b)
                   | _ -> "na")
                   (Common.Clock.now_s () -. t0)
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
            let rss0 = resident_kb () and t0 = Common.Clock.now_s () in
            fun outcome ->
              let z3_mb =
                match
                  Z3.Statistics.get (Z3.Solver.get_statistics solver) "memory"
                with
                | Some e -> Z3.Statistics.Entry.to_string_value e
                | None -> "na"
                | exception exn_ when not (Common.Timer.is_async exn_) -> "na"
              in
              (* the last three columns: how many functions the context has
                 declared (each declared as a recursive function, so a
                 nonzero count is a context Z3 answers quantified goals in
                 without eliminating unconstrained terms), how many of them
                 the question reaches, and whether this is the fresh-context
                 retry of [check_sat_fresh] *)
              let line =
                sprintf
                  "%d\t%b\t%b\t%d\t%d\t%d\t%d\t%.3f\t%s\t%s\t%d\t%d\t%b\n"
                  (Core_unix.getpid () |> Pid.to_int)
                  fresh_solver quantified max_id
                  (List.sum (module Int) phis ~f:Formula.ast_size)
                  rss0 (resident_kb ())
                  (Common.Clock.now_s () -. t0)
                  outcome z3_mb
                  (Map.Poly.length instance.fenv)
                  (Map.Poly.length (fenv_reached_by fenv (Formula.and_of phis)))
                  (Stdlib.Domain.DLS.get fresh_retry_in_progress_key)
              in
              Out_channel.with_file path ~append:true ~f:(fun oc ->
                  Out_channel.output_string oc line)
      in
      let t_pool = Common.Clock.now_s () in
      let replay =
        match inproc_replay with
        | Some (min_size, left, budget, file) when fresh_solver ->
            let budget =
              if budget > 0 then budget else Option.value timeout ~default:0
            in
            let size = List.sum (module Int) phis ~f:Formula.ast_size in
            if size >= min_size && Atomic.fetch_and_add left (-1) > 0 then (
              let r0 = inproc_replay_rlimit solver in
              let c0 = inproc_replay_thread_cpu () and w0 = Common.Clock.now_s () in
              let load0 = inproc_replay_load () and heap0 = inproc_replay_heap_mb () in
              fun outcome ->
                let w = Common.Clock.now_s () -. w0
                and c = inproc_replay_thread_cpu () -. c0 in
                let units =
                  match (r0, inproc_replay_rlimit solver) with
                  | Some a, Some b -> sprintf "%.0f" (b -. a)
                  | None, Some b -> sprintf "%.0f" b
                  | _ -> "na"
                in
                let pid = Core_unix.getpid () |> Pid.to_int in
                let tag = sprintf "%d-%d" pid (Atomic.get left) in
                inproc_replay_line file
                  [ "ASKED"; tag; string_of_int size; outcome; sprintf "%.3f" w;
                    sprintf "%.3f" c; units; load0; string_of_int heap0;
                    string_of_int (Option.value timeout ~default:0) ];
                let again how build =
                  try
                    let ctx2 = Z3.mk_context instance.cfg in
                    let s2 = Z3.Solver.mk_solver ctx2 None in
                    let params = Z3.Params.mk_params ctx2 in
                    Z3.Params.add_int params
                      (Z3.Symbol.mk_string ctx2 "timeout") budget;
                    add_arith_solver_param ctx2 params arith_solver;
                    Z3.Solver.set_parameters s2 params;
                    Z3.Solver.add s2 (build ctx2);
                    let load = inproc_replay_load () in
                    let st, w, c, units = inproc_replay_measured s2 in
                    inproc_replay_line file
                      [ how; tag; string_of_int size; st; sprintf "%.3f" w;
                        sprintf "%.3f" c; units; load;
                        string_of_int (inproc_replay_heap_mb ());
                        string_of_int budget ]
                  with exn_ when not (Common.Timer.is_async exn_) ->
                    inproc_replay_line file [ how; tag; "error"; Exn.to_string exn_ ]
                in
                (* the same expressions in a new solver of the asking
                   context: separates the context from the solver object *)
                if inproc_replay_wants 'S' then (try
                   let s2 = Z3.Solver.mk_solver ctx None in
                   let params = Z3.Params.mk_params ctx in
                   Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout")
                     budget;
                   add_arith_solver_param ctx params arith_solver;
                   Z3.Solver.set_parameters s2 params;
                   Z3.Solver.add s2 phis';
                   let load = inproc_replay_load () in
                   let st, w, c, units = inproc_replay_measured s2 in
                   inproc_replay_line file
                     [ "SAMECTX"; tag; string_of_int size; st; sprintf "%.3f" w;
                       sprintf "%.3f" c; units; load;
                       string_of_int (inproc_replay_heap_mb ());
                       string_of_int budget ]
                 with exn_ when not (Common.Timer.is_async exn_) ->
                   inproc_replay_line file [ "SAMECTX"; tag; "error"; Exn.to_string exn_ ]);
                let again how build =
                  if inproc_replay_wants how.[0] then again how build
                in
                (* the question converted again, in a new context, by the
                   same conversion the asking context received it from *)
                again "RECONVERTED" (fun ctx2 ->
                    let dtenv2 =
                      z3_dtenv_of_formula ~init:Set.Poly.empty ctx2
                      @@ Formula.and_of phis
                    in
                    let fenv2 =
                      if ordinary_definitions then Map.Poly.empty
                      else z3_fenv_of ~id ~init:Map.Poly.empty ctx2 [] [] fenv dtenv2
                    in
                    List.map phis
                      ~f:(of_formula_with_z3fenv ~id ctx2 [] [] fenv2 dtenv2));
                again "TRANSLATED" (fun ctx2 ->
                    List.map phis' ~f:(fun e -> Z3.Expr.translate e ctx2));
                let text = Z3.Solver.to_string solver in
                again "PARSED" (fun ctx2 ->
                    Z3.AST.ASTVector.to_expr_list
                    @@ Z3.SMT.parse_smtlib2_string ctx2 text [] [] [] []))
            else fun _ -> ()
        | _ -> fun _ -> ()
      in
      match
        check_sat_z3 ?fun_values_out ~query:(`Query phis) ctx solver
          instance.dtenv phis'
      with
      | ret -> (
          replay
            (match ret with
            | `Sat _ -> "sat"
            | `Unsat -> "unsat"
            | `Unknown _ -> "unknown"
            | `Timeout -> "timeout");
          (if Option.is_some z3_alt_log_path && quantified && not fresh_solver
           then
             let pooled =
               match ret with
               | `Sat _ -> "sat"
               | `Unsat -> "unsat"
               | `Unknown r ->
                   if String.is_substring r ~substring:"timeout"
                      || String.is_substring r ~substring:"canceled"
                   then "timeout"
                   else "unknown"
               | `Timeout -> "timeout"
             in
             let pooled_s = Common.Clock.now_s () -. t_pool in
             let tsolver =
               Z3.Solver.mk_solver_t ctx (Z3.Tactic.mk_tactic ctx "default")
             in
             let params = Z3.Params.mk_params ctx in
             Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout")
               (Option.value timeout ~default:0);
             Z3.Solver.set_parameters tsolver params;
             Z3.Solver.add tsolver phis';
             let t0 = Common.Clock.now_s () in
             let st = Z3.Solver.check tsolver [] in
             z3_alt_log
               (sprintf "tactic\t%s\t%.3f\t%s\t%.3f\t%d\t%d\n" pooled
                  pooled_s
                  (str_of_status_with tsolver st)
                  (Common.Clock.now_s () -. t0)
                  (Map.Poly.length instance.fenv)
                  (Map.Poly.length
                     (fenv_reached_by fenv (Formula.and_of phis)))));
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
          let result = match ret with
          | `Sat model ->
              `Sat
                (int_to_bv_range_model bv_ranged model)
          | `Unknown reason
            when Option.is_some rlimit && rlimit_exhausted_reason reason ->
              `Timeout
          | ret -> ret in
          raised := false;
          result)
      | exception e -> (
          log_ids "raised";
          log_check ("raised:" ^ Exn.to_string e |> String.tr ~target:'\t' ~replacement:' ' |> fun s -> String.prefix s 60);
          (* Z3 giving up inside [check] is a failure to decide this one
             question, so it is answered as undecided -- never a verdict, and
             never an exception that ends the caller's search or the run.
             [raised] stays set, so a clean context of the question's own is
             not reused after it.  Only [Check_gave_up] is caught here; the
             timer's asynchronous exceptions and every other error pass
             through. *)
          match e with
          | Check_gave_up ("canceled" | "timeout") -> `Timeout
          | Check_gave_up msg -> `Unknown ("Z3 error: " ^ msg)
          | e -> raise e))

(* A bounded necessary-context check for the file-level entry points only.
   Unsat of instances together with original constraints refutes the full
   defining context and those constraints. Sat/unknown/timeout or
   a synchronous encoding refusal supply no certificate and leave the caller
   on its existing route. Never register native recursive definitions here. *)
let refutes_defining_context_by_instances ?(timeout = Some 1000) ?(phis = []) ~id fenv =
  if not (supports_defining_equation_instances fenv) then false
  else
    try
      match
        check_sat_base ~timeout ~fresh_solver:true ~reduce_pure:true
          ~defining_equation_instances:true ~id fenv phis
      with
      | `Unsat -> true
      | `Sat _ | `Unknown _ | `Timeout -> false
    with exn when not (Common.Timer.is_async exn) -> false

(* The same necessary-context refutation over every first-order signature
   (datatypes, bit-vectors, arrays, sequences, declared sorts beside Bool,
   Int and Real; [first_order_instance_sort]).  Each formula asserted is an
   instance of a universally quantified defining equation -- a formal of a
   non-scalar sort stays universal, or takes a closed background term some
   call passes there -- so it is a consequence of the definitions, whatever
   the signature; Unsat of the instances with the constraints (the unknowns
   and universals read as uninterpreted symbols, kinds dropped) therefore
   refutes the context in every structure of the theory.  Sat, unknown,
   exhausted resources or a refused encoding supply nothing.  A body or
   constraint holding an array lambda is not asked: Z3's treatment of a
   closed lambda in an equation is where a false refutation over a true
   finite count was found, and this route has no guard of its own for it.
   Bounded by Z3's resource count ([first_order_instance_rlimit], measured
   on the reproducers of this route); the wall-clock budget is only a kill. *)
let first_order_instance_rlimit = 100_000

let first_order_instance_kill_ms = 30_000

let context_has_array_lambda (fenv : FunEnv.t) phis =
  List.exists (Map.Poly.data fenv) ~f:(fun (_, _, body, _, _) ->
      not (Set.is_empty (Term.filtered_terms_of body ~f:T_array.is_lambda)))
  || List.exists phis ~f:(fun phi ->
         not (Set.is_empty (Formula.filtered_terms_of phi ~f:T_array.is_lambda)))

let refutes_defining_context_by_first_order_instances
    ?(timeout = Some first_order_instance_kill_ms) ?(phis = []) ~id fenv =
  if
    (not (supports_first_order_defining_instances fenv))
    || context_has_array_lambda fenv phis
  then false
  else
    try
      with_rlimit ~label:"first_order_instances" (Some first_order_instance_rlimit)
        (fun () ->
          match
            check_sat_base ~timeout ~fresh_solver:true ~reduce_pure:true
              ~defining_equation_instances:true ~first_order_instances:true ~id
              fenv phis
          with
          | `Unsat -> true
          | `Sat _ | `Unknown _ | `Timeout -> false)
    with exn when not (Common.Timer.is_async exn) -> false

(* Either instance route: the scalar one exactly as before, then, only when it
   refutes nothing, the general one, so that no refutation the scalar route
   gives can be lost to the general route's larger question. *)
let refutes_defining_context_by_any_instances ?timeout ?(phis = []) ~id fenv =
  (supports_defining_equation_instances fenv
   && refutes_defining_context_by_instances ?timeout ~phis ~id fenv)
  || refutes_defining_context_by_first_order_instances ~phis ~id fenv

(* Ground constraints on the open terms of the known bodies, each a candidate
   background in which the defining context may have no model.  A pin set is
   a conjunction [t1 = v1 /\ ... /\ tk = vk] where each [ti] is a subterm of a
   (let-eliminated) body whose root value the theory leaves open
   ([ClauseOld.theory_open_at_root]) with every variable replaced by the
   zero of its sort, so that it mentions no variable, no function variable
   (known or unknown), no binder and no array lambda, and each [vi] is drawn
   from 0, 1, -1 and the literals of the bodies and constraints and their
   neighbours (false and true for a Boolean term).  How a pin set is chosen
   is a heuristic and plays no part in the soundness of the refutation
   below, which holds for any variable-free formula over background symbols.
   At most [max_terms] terms and [max_sets] sets, smallest values first. *)
let open_term_pins ?(datatype_terms = false) ?(max_terms = 3) ?(max_values = 7)
    ?(max_sets = 24) fenv phis =
  let bodies =
    List.map (Map.Poly.data fenv) ~f:(fun (_, _, body, _, _) ->
        if Term.is_let_free body then body else Term.elim_let body)
  in
  let unwanted = function
    | Term.Var _ -> true
    | Term.FunApp ((FVar _ | T_bool.Formula _ | T_array.ALambda _), _, _) -> true
    | Term.LetTerm _ -> true
    | _ -> false
  in
  (* a constructor of a first-order datatype with no field: a closed value
     of that sort, used both for a variable of the sort and as a pin value *)
  let nullary_conses = function
    | T_dt.SDT dt as sort when datatype_terms && first_order_instance_sort sort ->
        List.filter_map (Datatype.conses_of dt) ~f:(fun cons ->
            if List.is_empty (Datatype.sels_of_cons cons) then
              Some (T_dt.mk_cons dt (Datatype.name_of_cons cons) [])
            else None)
    | _ -> []
  in
  let zero_of sort =
    if Term.is_int_sort sort then Some (T_int.zero ())
    else if Term.is_real_sort sort then Some (T_real.rzero ())
    else if Term.is_bool_sort sort then Some (T_bool.make false)
    else List.hd (nullary_conses sort)
  in
  let close t =
    let senv = Set.to_list (Term.term_sort_env_of t) in
    let subst =
      List.map senv ~f:(fun (x, sort) -> Option.map (zero_of sort) ~f:(fun z -> (x, z)))
    in
    if List.exists subst ~f:Option.is_none then None
    else
      let t = Term.subst (Map.Poly.of_alist_reduce (List.filter_opt subst) ~f:(fun a _ -> a)) t in
      if Set.is_empty (Term.filtered_terms_of t ~f:unwanted) then Some t else None
  in
  let pin_terms =
    List.concat_map bodies ~f:(fun body ->
        Set.to_list (Term.filtered_terms_of body ~f:ClauseOld.theory_open_at_root))
    |> List.filter_map ~f:close
    |> List.filter ~f:(fun t ->
           let sort = Term.sort_of t in
           Term.is_int_sort sort || Term.is_real_sort sort || Term.is_bool_sort sort
           || not (List.is_empty (nullary_conses sort)))
    |> List.dedup_and_sort ~compare:(fun a b ->
           let c = Int.compare (Term.ast_size a) (Term.ast_size b) in
           if c <> 0 then c else Stdlib.compare a b)
    |> Fn.flip List.take max_terms
  in
  if List.is_empty pin_terms then []
  else
    let literals =
      List.concat_map bodies ~f:(fun body ->
          Set.to_list (Term.filtered_terms_of body ~f:(fun _ -> true)))
      @ List.concat_map phis ~f:(fun phi ->
            Set.to_list (Formula.filtered_terms_of phi ~f:(fun _ -> true)))
    in
    let ints =
      List.filter_map literals ~f:(function
        | Term.FunApp (T_int.Int n, [], _) -> Some n
        | _ -> None)
    in
    let reals =
      List.filter_map literals ~f:(function
        | Term.FunApp (T_real.Real q, [], _) -> Some q
        | _ -> None)
    in
    let near ~zero ~one ~add ~sub ~abs ~compare ns =
      zero :: one :: sub zero one :: List.concat_map ns ~f:(fun n -> [ sub n one; n; add n one ])
      |> List.dedup_and_sort ~compare:(fun a b ->
             let c = compare (abs a) (abs b) in
             if c <> 0 then c else compare a b)
      |> Fn.flip List.take max_values
    in
    (* a datatype-sorted pin takes the closed values of its sort that the
       bodies and constraints write, and the fieldless constructors, smallest
       first; all are variable-free terms over theory symbols *)
    let closed_values sort =
      List.filter literals ~f:(fun t ->
          Set.is_empty (Term.term_sort_env_of t)
          && Set.is_empty (Term.filtered_terms_of t ~f:unwanted)
          && Set.is_empty (Term.filtered_terms_of t ~f:ClauseOld.theory_open_at_root)
          && Stdlib.(Term.sort_of t = sort))
      @ nullary_conses sort
      |> List.dedup_and_sort ~compare:(fun a b ->
             let c = Int.compare (Term.ast_size a) (Term.ast_size b) in
             if c <> 0 then c else Stdlib.compare a b)
      |> Fn.flip List.take max_values
    in
    let values t =
      let sort = Term.sort_of t in
      if not (Term.is_int_sort sort || Term.is_real_sort sort || Term.is_bool_sort sort)
      then closed_values sort
      else if Term.is_int_sort sort then
        List.map ~f:T_int.mk_int
          (near ~zero:Z.zero ~one:Z.one ~add:Z.add ~sub:Z.sub ~abs:Z.abs ~compare:Z.compare ints)
      else if Term.is_real_sort sort then
        List.map ~f:T_real.mk_real
          (near ~zero:Q.zero ~one:Q.one ~add:Q.add ~sub:Q.sub ~abs:Q.abs ~compare:Q.compare reals)
      else [ T_bool.make false; T_bool.make true ]
    in
    (* every combination of value indices, ordered by their sum so that the
       small values of every term are tried before the large values of any *)
    let rec combos = function
      | [] -> [ (0, []) ]
      | t :: ts ->
          let rest = combos ts in
          List.concat_mapi (values t) ~f:(fun i v ->
              List.map rest ~f:(fun (w, pins) -> (i + w, Formula.eq t v :: pins)))
    in
    combos pin_terms
    |> List.stable_sort ~compare:(fun (a, _) (b, _) -> Int.compare a b)
    |> Fn.flip List.take max_sets
    |> List.map ~f:snd

(* Under the per-background reading of a file context, a defined symbol is
   chosen in each background together with the unknowns (for all M, exists f,
   exists I).  So the context is refuted by ONE background in which the
   definitions and constraints have no model.  A pin set P (above) mentions
   only background symbols and no variable; if P alone is satisfiable, some
   structure of the theory satisfies it, and if P together with the defining
   equations and the constraints is unsatisfiable, no structure satisfying P
   admits a defined symbol and an interpretation of the unknowns.  Both
   questions go to fresh solvers with ordinary declarations, never native
   recursive definitions, which constrain a function only where a query
   applies it.  Satisfiable, unknown, timed-out or refused questions supply
   nothing, and the refutation is then not claimed. *)
(* Each question is bounded by Z3's resource count, not by time, so whether a
   pin set is decided does not depend on the machine's load.  Measured on the
   deciding questions of the reproducers and controls (2026-10-20, Z3 5.1.0,
   [COAR_Z3_RLIMIT_LOG], 130 checks over seven files and two backends): a pin
   set alone is decided within 179 units and a pinned question with the
   defining equations within 914 (845 for a [sat] one); the bound is
   [open_term_pin_rlimit] units per question, more than a hundred times the
   largest.  So the pass asks at most 48 questions of at most 100,000 units
   each.  The wall-clock budget is only a kill for a check Z3 does not
   interrupt. *)
let open_term_pin_rlimit = 100_000

let open_term_pin_kill_ms = 30_000

(* The pin sets of the scalar terms are tried first, exactly as before the
   datatype-sorted terms (and datatype variables closed by a fieldless
   constructor) were added; the sets these add are tried only afterwards, so
   no refutation the scalar sets gave can be displaced by the cut at
   [max_sets]. *)
let refutes_defining_context_by_open_term_pins ?(phis = []) ~id fenv =
  let full = supports_defining_equations fenv in
  let timeout = Some open_term_pin_kill_ms in
  if
    not
      (full
      || supports_defining_equation_instances fenv
      || supports_first_order_defining_instances fenv)
  then false
  else
    let scalar_sets = open_term_pins fenv phis in
    let datatype_sets =
      List.filter (open_term_pins ~datatype_terms:true fenv phis) ~f:(fun pins ->
          not
            (List.mem scalar_sets pins ~equal:(fun a b ->
                 try Stdlib.( = ) a b with Invalid_argument _ -> false)))
    in
    List.exists (scalar_sets @ datatype_sets) ~f:(fun pins ->
        try
          (match
             with_rlimit ~label:"open_term_pins_alone" (Some open_term_pin_rlimit)
               (fun () ->
                 check_sat_base ~timeout ~fresh_solver:true ~id Map.Poly.empty pins)
           with
          | `Sat _ -> true
          | `Unsat | `Unknown _ | `Timeout -> false)
          && with_rlimit ~label:"open_term_pins_refute" (Some open_term_pin_rlimit)
               (fun () ->
                 if full then
                   match
                     check_sat_base ~timeout ~fresh_solver:true
                       ~defining_equations:true ~id fenv (phis @ pins)
                   with
                   | `Unsat -> true
                   | `Sat _ | `Unknown _ | `Timeout -> false
                 else
                   refutes_defining_context_by_any_instances ~timeout
                     ~phis:(phis @ pins) ~id fenv)
        with exn when not (Common.Timer.is_async exn) -> false)

(* A candidate is only a search heuristic. Its defining equalities must hold
   for all formals under the substituted constraints before their models can
   witness the original context. Failure supplies no certificate. *)
let defining_context_projection_model_core ~id ~(kept : FunEnv.t) fenv phis =
  if Map.Poly.is_empty fenv then None
  else
    try
      let entries =
        Map.Poly.to_alist
          (Map.Poly.filter_keys fenv ~f:(fun var -> not (Map.Poly.mem kept var)))
      in
      if List.is_empty entries then raise (Invalid_argument "Nothing to project");
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
            | FunApp (FVar (var, _, _), _, _) ->
                Map.Poly.mem fenv var && not (Map.Poly.mem kept var)
            | _ -> false)
        in
        let mentions_kept phi =
          Set.exists (Formula.fvar_apps_of phi) ~f:(function
            | FunApp (FVar (var, _, _), _, _) -> Map.Poly.mem kept var
            | _ -> false)
          || Set.exists (Formula.fvs_of phi) ~f:(Map.Poly.mem kept)
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
          (* a kept (total) symbol is read as uninterpreted below, which is
             sound for the validity of the equations and wrong for the model:
             the constraints must not mention one *)
          if List.exists phis ~f:mentions_kept then None
          else
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

let defining_context_projection_model ~id fenv phis =
  defining_context_projection_model_core ~id ~kept:Map.Poly.empty fenv phis

(* [omitted_definitions_have_constant_model ~id ~kept fenv]: every definition
   of [fenv] outside [kept] has a model in every structure, whatever the kept
   functions, the globals and the forall functions denote, namely the
   constant [0] or [false] for each omitted function at once.  Checked as the
   validity of each omitted equation [c = body[omitted := constants]] with its
   formals, the globals and the kept functions left free; a constant has no
   free variable, so the substitution cannot capture.

   Assumes: no constraint and no kept definition (body or property) applies
   an omitted function, which is what makes the omitted ones droppable.
   Guarantees on [true]: every model of the kept definitions and the
   constraints extends to a model of all of [fenv] and the constraints by
   interpreting each omitted function as its constant, so the kept context is
   satisfiable in a structure exactly when the whole one is.  Reachability
   alone does not give this: an unused [f x = f 0 + 1] has no integer model
   and makes the whole context inconsistent.  [false] (an omitted function of
   another result sort, a recorded property, an equation not proved valid
   within one second, a refused conversion) claims nothing. *)
let omitted_definitions_have_constant_model ~id ~(kept : FunEnv.t)
    (fenv : FunEnv.t) =
  try
    let omitted =
      Map.Poly.to_alist
        (Map.Poly.filter_keys fenv ~f:(fun var -> not (Map.Poly.mem kept var)))
    in
    (not (List.is_empty omitted))
    && List.for_all omitted ~f:(fun (_, (_, _, _, _, property)) ->
           Formula.is_true property)
    &&
    let constant sret =
      if Term.is_int_sort sret then Some (T_int.from_int 0)
      else if Term.is_bool_sort sret then Some (T_bool.make false)
      else None
    in
    match
      Option.all
        (List.map omitted ~f:(fun (var, (params, sret, _, _, _)) ->
             Option.map (constant sret) ~f:(fun c -> (var, (params, c)))))
    with
    | None -> false
    | Some entries ->
        let constants = Map.Poly.of_alist_exn entries in
        List.for_all omitted ~f:(fun (var, (_, _, body, _, _)) ->
            let _, c = Map.Poly.find_exn constants var in
            match
              check_sat_base ~timeout:(Some 1000) ~fresh_solver:true ~id
                (FunEnv.mk_empty ())
                [ Formula.mk_neg (Formula.eq c (Term.subst_funcs constants body)) ]
            with
            | `Unsat -> true
            | `Sat _ | `Unknown _ | `Timeout -> false)
  with exn when not (Common.Timer.is_async exn) -> false

(* Total definitions supply a background model for validity-based pCSP solving.
   Recognise generated sizes by their complete factory entries and finite
   datatype dependencies, never by names. Other definitions must be acyclic
   or, per strongly connected component of the call graph, have every call
   inside the component decrease a well-founded measure under the call's
   guards: an integer one, non-negative where it is lowered (a declared
   [:decreases] measure, or a formal), or the proper-subterm order on a formal
   of an inductive datatype, or a lexicographic pair of those.
   Array lambdas are excluded: an arbitrary array-theory carrier need not
   contain the function they denote. *)
(* Declaration and collected-instance entries can describe the same datatype.
   Merge only identical factory definitions; a name collision between distinct
   definitions is not permission to trust the first entry. *)
(* Set only by a property check: the structural rank proof then accepts a
   selector chain without proving its testers, the unsound mutant the check
   must tell apart.  Never set in a solving run. *)
let structural_testers_ignored = Atomic.make false

type total_context_key = FunEnv.t * TermSubst.t * DTEnv.t

(* Each entry: the proof-registry version and the key, the answer, and
   whether the key is equal to itself under [total_context_key_equal] (false
   only when comparing it raised, i.e. it holds a value polymorphic equality
   cannot compare). *)
let total_context_memo :
    ((int * total_context_key) * bool * bool) list Atomic.t =
  Atomic.make []

let total_context_key_equal (functions, measures, datatypes)
    (functions', measures', datatypes') =
  try
    Map.Poly.equal Poly.equal functions functions'
    && Map.Poly.equal Poly.equal measures measures'
    && Map.Poly.equal Poly.equal datatypes datatypes'
  with Invalid_argument _ ->
    (* Extensible AST payloads can contain non-comparable values. An
       unprovable equality is a cache miss, never a printed-key fallback. *)
    false

(* [total_context_key_equal k k'] when the three components of [k] and [k']
   are physically equal, given [self_equal = total_context_key_equal k' k']:
   the comparison is a deterministic function of the values it reads, so for
   physically equal arguments it is the stored self-comparison, and the walk
   over the whole defining and datatype environments is not repeated.  The
   memo's key is read on every certified positive answer, and the walk cost
   tens of milliseconds a time on an input with a hundred datatypes, one
   lookup per validity question of the predicate elimination. *)
let total_context_key_equal_given_self ~self_equal ((f, m, d) as k)
    ((f', m', d') as k') =
  if phys_equal f f' && phys_equal m m' && phys_equal d d' then self_equal
  else total_context_key_equal k k'

(* The properties of known functions proved true of their standard
   interpretation: a lemma pass registers [(f, prop)] when [prop], the
   function's whole property, was proved by well-founded induction along a
   measure that shows [f] total, from the defining equations and the
   properties the other functions had then.  The totality certificate below
   accepts a user function whose property is either [true] or registered with
   exactly that property: when every function of the context passes, every
   property is true or proved, so the proofs rest on nothing unproved, the
   defining equations have their standard solution in every model of the
   background theory, and it satisfies every property.  A lemma that assumed
   another function's unproved property is registered but never accepted
   alone: the certificate judges the complete context, and that property is
   refused.  Any other property is an assumption that may have no solution,
   which the certificate refuses as before.  The list only
   grows; each proof is tied to the complete final defining environment,
   measures and datatypes. A same-named function or property in another
   context cannot reuse it, even when only another definition changed. A
   projection of the proof's environment reuses it only through
   [proved_in_certified_superset] below: it must keep every definition the
   function reaches, and the proof's environment must itself be certified. The
   version counts registrations, so a totality answer remembered before a
   registration is not reused after it. *)
let proved_function_properties :
    (total_context_key * Ident.tvar * Formula.t) list Atomic.t =
  Atomic.make []

let proved_properties_version = Atomic.make 0

let register_proved_property ~fenv f prop =
  let context = (fenv, get_declared_measures (), get_dtenv ()) in
  let rec add () =
    let old = Atomic.get proved_function_properties in
    if not
         (Atomic.compare_and_set proved_function_properties old
            ((context, f, prop) :: old))
    then add ()
  in
  add ();
  Atomic.incr proved_properties_version

(* [current] extends [recorded]: every datatype the proof's environment held
   is present under the same key with an identical declaration.  Datatypes
   added since then (an instance registered during solving, a declaration
   read later) are not mentioned by the recorded definitions, measures or
   property, and an identical declaration denotes the same term algebra, so
   the proof's standard interpretation and its induction are unchanged.  A
   recorded datatype that is missing or declared differently is refused. *)
let datatype_env_extends ~recorded ~current =
  try
    Map.Poly.for_alli recorded ~f:(fun ~key ~data ->
        match Map.Poly.find current key with
        | Some data' -> Poly.equal data data'
        | None -> false)
  with Invalid_argument _ -> false

(* A registration counts for [context] when the defining environment and the
   declared measures are exactly the proof's and the datatype environment
   only extends the proof's. *)
let proof_context_admits ~recorded:(functions, measures, datatypes)
    ~current:(functions', measures', datatypes') =
  (try
     Map.Poly.equal Poly.equal functions functions'
     && Map.Poly.equal Poly.equal measures measures'
   with Invalid_argument _ -> false)
  && datatype_env_extends ~recorded:datatypes ~current:datatypes'

let is_proved_property ~context f prop =
  List.exists (Atomic.get proved_function_properties) ~f:(fun (proof_context, g, p) ->
      Ident.tvar_equal f g
      && proof_context_admits ~recorded:proof_context ~current:context
      && try Poly.equal p prop with Invalid_argument _ -> false)

(* For the totality trace only: for each registration of [f] with [prop], which
   part of its recorded context differs from [context] (functions, measures,
   datatypes, whether the datatypes only extend, and the function keys that
   differ). *)
let proved_property_mismatches ~context:(functions, measures, datatypes) f prop =
  List.filter_map (Atomic.get proved_function_properties)
    ~f:(fun ((functions', measures', datatypes'), g, p) ->
      let eq m m' = try Map.Poly.equal Poly.equal m m' with Invalid_argument _ -> false in
      if Ident.tvar_equal f g && (try Poly.equal p prop with Invalid_argument _ -> false)
      then
        Some
          (sprintf "fenv=%b meas=%b dt=%b extends=%b (%d recorded/%d now; fenv keys differing: %s)"
             (eq functions' functions) (eq measures' measures) (eq datatypes' datatypes)
             (datatype_env_extends ~recorded:datatypes' ~current:datatypes)
             (Map.Poly.length datatypes') (Map.Poly.length datatypes)
             (String.concat ~sep:","
                (List.filter_map
                   (Set.to_list
                      (Set.union (Set.Poly.of_list (Map.Poly.keys functions))
                         (Set.Poly.of_list (Map.Poly.keys functions'))))
                   ~f:(fun k ->
                     match (Map.Poly.find functions k, Map.Poly.find functions' k) with
                     | Some a, Some b when (try Poly.equal a b with Invalid_argument _ -> false) -> None
                     | Some _, Some _ -> Some (Ident.name_of_tvar k ^ "(changed)")
                     | Some _, None -> Some (Ident.name_of_tvar k ^ "(new)")
                     | None, _ -> Some (Ident.name_of_tvar k ^ "(gone)")))))
      else None)

let generated_size_function_map entries =
  Map.Poly.of_alist_reduce entries ~f:(fun left right ->
      if Poly.equal left right then left
      else failwith "conflicting generated datatype size definitions")

(* A diagnostic, read once: with [COAR_TOTALITY_TRACE] set, the totality
   certificate below prints to stderr why it refuses (the definition whose
   property or body is outside every certificate, the recursive component
   no measure proves with the obligations that failed, or the exception that
   ended the proof).  It changes no answer.  Evaluated now: a [lazy] forced
   by two domains at once raises [Lazy.Undefined]. *)
let totality_trace =
  Lazy.from_val (Option.is_some (Sys.getenv "COAR_TOTALITY_TRACE"))

(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let totality_memo_trace =
  Lazy.from_val (Option.is_some (Sys.getenv "COAR_TOTALITY_MEMO_TRACE"))

let rec has_total_defining_context ~id fenv =
  (* Keep immutable content, not diagnostic output: a variable named by
     another term's printed form must not inherit that term's certificate. *)
  let declared = get_declared_measures () in
  let dtenv = get_dtenv () in
  let key = (fenv, declared, dtenv) in
  let version = Atomic.get proved_properties_version in
  (* [COAR_TOTALITY_MEMO_TRACE] (instrument only): per lookup, the version
     and which key components are physically those of the newest entry *)
  if Lazy.force totality_memo_trace then
    (match Atomic.get total_context_memo with
     | ((v, (f, m, d)), _, se) :: _ ->
         eprintf "[totality-memo] version %d/%d fenv %b measures %b dtenv %b self %b entries %d dtenv-size %d\n%!"
           version v (phys_equal f fenv) (phys_equal m declared) (phys_equal d dtenv) se
           (List.length (Atomic.get total_context_memo)) (Map.Poly.length dtenv)
     | [] -> eprintf "[totality-memo] empty\n%!");
  let memo = Atomic.get total_context_memo in
  match
    List.find memo ~f:(fun ((v', k'), _, self_equal) ->
        version = v' && total_context_key_equal_given_self ~self_equal key k')
  with
  | Some (((_, (f', m', d')), answer, _) as entry) ->
      (* found by a structural comparison: the entry takes the caller's
         physical key, equal to its own, so that the next lookup with these
         values is decided by identity (callers reach this with the same
         environments, but not the ones the entry was first made with) *)
      if not (phys_equal f' fenv && phys_equal m' declared && phys_equal d' dtenv)
      then (
        let refreshed =
          ((version, key), answer, total_context_key_equal key key)
        in
        ignore
          (Atomic.compare_and_set total_context_memo memo
             (List.map memo ~f:(fun e -> if phys_equal e entry then refreshed else e))
            : bool));
      answer
  | None ->
      let answer =
        has_total_defining_context_uncached ~dtenv ~declared ~id fenv
      in
      let self_equal = total_context_key_equal key key in
      let rec remember () =
        let old = Atomic.get total_context_memo in
        if
          not
            (Atomic.compare_and_set total_context_memo old
               (List.take (((version, key), answer, self_equal) :: old) 16))
        then remember ()
      in
      remember ();
      answer

(* [proved_in_certified_superset ~id ~context f prop]: [prop], the property
   [f] has in [context], was proved in a larger defining environment of which
   [context] keeps a part, and that part is enough for the proof to hold.

   Precondition: [f] is a key of [context]'s environment with property
   [prop].  Accepts when some registration of [(f, prop)] was made against an
   environment [recorded] such that
   - [context]'s environment is a strict projection of [recorded]: fewer
     entries, each identical (body, formals and property) to [recorded]'s;
   - every function [f]'s definition or property reaches in [recorded]
     (through bodies and properties, transitively) is kept in [context];
   - the measures are the same and the datatypes only extend; and
   - [recorded] itself passes the totality certificate.
   Why that is sound: [recorded] passing the certificate means every property
   in it is true or proved and its equations have their standard solution,
   which satisfies every property -- [prop] included -- in every model of the
   background theory.  [f]'s standard interpretation is fixed by the
   definitions [f] reaches, all kept unchanged in [context], and [prop]
   mentions only functions among them, so [prop] holds of [f]'s standard
   interpretation in [context] too.  A projection that dropped a definition
   [f] reaches would leave a call to a function [context] does not define,
   and is refused.  Without this, a property a lemma pass proved was lost
   whenever a question was asked over only the functions it mentions (the
   query-reached slice of the environment), and every [sat] over such a slice
   was withheld as uncertified.
   Terminates: each recursive certificate check is on a registered
   environment with strictly more entries than the one asked about, and the
   registry is finite. *)
and proved_in_certified_superset ~id ~context:(functions, measures, datatypes)
    f prop =
  let same a b = try Poly.equal a b with Invalid_argument _ -> false in
  let is_projection_of recorded =
    Map.Poly.length functions < Map.Poly.length recorded
    && Map.Poly.for_alli functions ~f:(fun ~key ~data ->
           match Map.Poly.find recorded key with
           | Some data' -> same data data'
           | None -> false)
  in
  let reached recorded =
    let known var = Map.Poly.mem recorded var in
    let of_apps apps =
      Set.Poly.filter_map apps ~f:(function
        | Term.FunApp (FVar (var, _, _), _, _) when known var -> Some var
        | _ -> None)
    in
    let refs (body, prop) =
      Set.union
        (Set.union (Set.filter (Term.fvs_of body) ~f:known)
           (of_apps (Term.fvar_apps_of body)))
        (Set.union (Set.filter (Formula.fvs_of prop) ~f:known)
           (of_apps (Formula.fvar_apps_of prop)))
    in
    let rec close seen = function
      | [] -> seen
      | var :: rest -> (
          match Map.Poly.find recorded var with
          | None -> close seen rest
          | Some (_, _, body, _, prop) ->
              let next = Set.diff (refs (body, prop)) seen in
              close (Set.union seen next) (Set.to_list next @ rest))
    in
    close (Set.Poly.singleton f) [ f ]
  in
  List.exists (Atomic.get proved_function_properties)
    ~f:(fun ((recorded, measures', datatypes'), g, p) ->
      Ident.tvar_equal f g && same p prop
      && (try Map.Poly.equal Poly.equal measures' measures
          with Invalid_argument _ -> false)
      && datatype_env_extends ~recorded:datatypes' ~current:datatypes
      && is_projection_of recorded
      && Set.for_all (reached recorded) ~f:(Map.Poly.mem functions)
      && has_total_defining_context ~id recorded)

and has_total_defining_context_uncached ?(dtenv = get_dtenv ())
    ?(declared = get_declared_measures ()) ~id fenv =
  (* Do not serialize failed proof obligations when tracing is disabled. *)
  let trace message =
    if Lazy.force totality_trace then prerr_endline ("totality: " ^ message ())
  in
  try
    let generated =
      Map.Poly.data dtenv
      (* The problem builder generates a size function for every monomorphic
         entry of the datatype environment, and each one that is total must be
         recognised here, or an input that defines no function at all is
         withheld as having an unverified context.  Two shapes are total in
         every model of the SMT-LIB theory, whatever the carriers of the
         uninterpreted sorts are:
         - an inductive datatype whose reachable datatypes are all inductive:
           the theory interprets each as its algebra of finite terms, and the
           generated size recurses only through selectors to datatype-sorted
           fields, which yield proper subterms, so structural induction on the
           term gives the equation exactly one solution.  A field of any other
           sort (an uninterpreted sort, an integer, an array) contributes the
           constant 0 and is never recursed into;
         - an uninterpreted sort ([declare-sort]): it has no constructor, so
           its generated size is the constant 0 and its property is
           [forall x. true].
         A codatatype is excluded: a cyclic value such as [x = cons(a, x)]
         forces [size x = 1 + size x], so its size equation has no solution.
         A sort-polymorphic declaration is excluded, as the builder generates
         nothing for it; its instances are separate monomorphic entries.
         Recognition is still by the complete factory entry below, never by
         name, so a user definition spelled like a size function is judged as
         a user definition. *)
      |> List.filter ~f:(fun dt ->
             (not (Datatype.is_poly dt))
             && ((Datatype.is_dt dt
                  && Set.for_all (fst (Datatype.used_dt_and_sorts_of dt))
                       ~f:Datatype.is_dt)
                || Datatype.is_undef dt))
      |> List.map ~f:Datatype.size_fun_of
      (* The environment holds one datatype under several keys (its
         declaration name and its structural instance key), so the same size
         function is generated more than once.  Identical copies are one
         definition; a name generated with two different definitions is
         trusted under neither, and is then judged as a user definition.
         Raising on the duplicate made every positive answer over a datatype
         input uncertified, so validation never accepted a candidate. *)
      |> Map.Poly.of_alist_multi
      |> Map.Poly.filter_map ~f:(function
             | def :: defs when List.for_all defs ~f:(Poly.equal def) -> Some def
             | _ -> None)

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
    if not (Map.Poly.for_alli user ~f:(fun ~key ~data:(_, _, body, _, prop) ->
                  let prop_ok =
                    Formula.is_true prop
                    || is_proved_property ~context:(fenv, declared, dtenv) key prop
                    || proved_in_certified_superset ~id
                         ~context:(fenv, declared, dtenv) key prop
                  in
                  let lambda_free =
                    Set.is_empty (Term.filtered_terms_of body ~f:T_array.is_lambda)
                  in
                  if not prop_ok then
                    trace (fun () -> sprintf "%s: unproved property %s [registrations: %s]"
                             (Ident.name_of_tvar key) (Formula.str_of prop)
                             (String.concat ~sep:"; "
                                (proved_property_mismatches
                                   ~context:(fenv, declared, dtenv) key prop)));
                  if not lambda_free then
                    trace (fun () -> sprintf "%s: array lambda in body" (Ident.name_of_tvar key));
                  prop_ok && lambda_free))
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
        (* Only a call inside a strongly connected component of the call graph
           can recur; a call to a function of a lower component terminates by
           that component's own proof, so it carries no obligation. *)
        let reach =
          Map.Poly.mapi user ~f:(fun ~key ~data:_ ->
              let rec close seen = function
                | [] -> seen
                | var :: rest ->
                    let (_, _, body, _, _) = Map.Poly.find_exn user var in
                    let next = Set.diff (dependencies body) seen in
                    close (Set.union seen next) (Set.to_list next @ rest)
              in
              close Set.Poly.empty [ key ])
        in
        let components =
          Map.Poly.keys user
          |> List.filter ~f:(fun var -> Set.mem (Map.Poly.find_exn reach var) var)
          |> List.map ~f:(fun var ->
                 Set.filter (Map.Poly.find_exn reach var) ~f:(fun other ->
                     Set.mem (Map.Poly.find_exn reach other) var))
          |> List.dedup_and_sort ~compare:Set.compare_direct
        in
        let zero = T_int.from_int 0 in
        let valid phi =
          match check_sat_base ~timeout:(Some 1000) ~fresh_solver:true
                  ~id (FunEnv.mk_empty ()) [Formula.mk_neg phi] with
          | `Unsat -> true
          | _ -> false
        in
        (* A component is total when a measure per function makes every call
           inside the component, under the condition the call's value matters
           on, reach a strictly smaller measure in a well-founded order: an
           infinite chain of such calls would be an infinite descent, so in
           every model the equations have exactly one solution, built by
           well-founded induction on the measure (where the condition fails,
           the call's value does not affect the body's, so both the solution
           and its uniqueness are settled below the measure).  A measure is a
           lexicographic tuple of one or two components, each either
           - an integer term over the formals, ordered by [<] on the
             naturals: a strict step starts from a non-negative value and
             reaches a smaller one, a non-strict step reaches one no larger; or
           - the value of a formal whose sort is an inductive datatype
             reaching only inductive datatypes, ordered by the proper-subterm
             relation, well-founded because the theory interprets each such
             datatype as its algebra of finite terms: a strict step passes a
             selector chain over that formal, under conditions that imply the
             tester of each selector (a selector applied to another
             constructor, [tl nil], is a value the theory leaves open, not a
             subterm), and a non-strict step passes a value equal to it.
           A lexicographic step is strict on the first component, or
           non-strict on it and strict on the second; such steps cannot form
           an infinite chain, since the first components never increase, are
           strictly lowered from a non-negative or finite-tree value only
           finitely often, and between those the second components descend.
           Every member of a component uses components of one kind at each
           position, so the measure is one for the whole mutually recursive
           group.  Integer measures are tried first and alone, exactly as
           before structural ones were: a measure the input declares
           ([:decreases]) alone, since it is what the definition's author
           proved, otherwise each integer formal, the last first.  Then each
           inductive-datatype formal (the last first), then ordered pairs of
           them. *)
        let component_total component =
          let members = Set.to_list component in
          (* The integer fields of a formal of a record sort, an inductive
             datatype with exactly one constructor, read through its
             selectors (and through the selectors of a record-sorted field,
             to the given depth).  Such a selector is total and fixed by the
             theory -- every value of the sort is an application of its only
             constructor and the selector returns that application's field --
             so a field is an integer function of the formals in every model,
             and serves as a measure exactly as an integer formal does.  A
             selector of a datatype with two or more constructors is not
             offered: on another constructor its value is left open, and a
             measure must not be. *)
          let rec record_int_fields depth term sort =
            match sort with
            | T_dt.SDT dt when depth > 0 && Datatype.is_dt dt -> (
                match
                  try Some (Datatype.conses_of dt)
                  with exn when not (Common.Timer.is_async exn) -> None
                with
                | Some [ cons ] ->
                    List.concat_mapi (Datatype.sels_of_cons cons) ~f:(fun i sel ->
                        match sel with
                        | Datatype.Sel _ ->
                            let field =
                              T_dt.mk_sel_by_cons dt (Datatype.name_of_cons cons) i term
                            in
                            let field_sort = Term.sort_of field in
                            if Term.is_int_sort field_sort then [ field ]
                            else record_int_fields (depth - 1) field field_sort
                        | Datatype.InSel _ -> [])
                | _ -> [])
            | _ -> []
          in
          let int_candidates var =
            let (params, _, _, _, _) = Map.Poly.find_exn user var in
            match Map.Poly.find declared var with
            | Some measure
              when Term.is_int_sort (Term.sort_of measure)
                   && Set.are_disjoint (dependencies measure) component ->
                [ (params, [ `Int measure ]) ]
            | _ ->
                List.rev_filter_map params ~f:(fun (x, sort) ->
                    if Term.is_int_sort sort then
                      Some (params, [ `Int (Term.mk_var x sort) ])
                    else None)
          in
          (* the record fields beside the integer formals, tried only after
             the integer formals alone, so that a component they prove keeps
             its proof however many fields its members have *)
          let record_fields var =
            let (params, _, _, _, _) = Map.Poly.find_exn user var in
            List.concat_map (List.rev params) ~f:(fun (x, sort) ->
                List.map (record_int_fields 2 (Term.mk_var x sort) sort)
                  ~f:(fun field -> (params, [ `Int field ])))
          in
          let int_field_candidates var =
            match Map.Poly.find declared var with
            | Some _ -> int_candidates var
            | None -> int_candidates var @ record_fields var
          in
          let structural_positions var =
            let (params, _, _, _, _) = Map.Poly.find_exn user var in
            ( params,
              List.rev
                (List.filter_mapi params ~f:(fun i (_, sort) ->
                     if SubtermOrder.inductive_closure_sort sort then Some i
                     else None)) )
          in
          let structural_singletons var =
            let params, positions = structural_positions var in
            List.map positions ~f:(fun i -> (params, [ `Sub i ]))
          in
          let structural_pairs var =
            let params, positions = structural_positions var in
            List.concat_map positions ~f:(fun i ->
                List.filter_map positions ~f:(fun j ->
                    if i = j then None else Some (params, [ `Sub i; `Sub j ])))
          in
          let assignments_of candidates =
            let choices = List.map members ~f:(fun var -> (var, candidates var)) in
            let rec assignments = function
              | [] -> [ [] ]
              | (var, cands) :: rest ->
                  let tails = assignments rest in
                  List.concat_map cands ~f:(fun cand ->
                      List.map tails ~f:(fun tail -> (var, cand) :: tail))
            in
            let count =
              List.fold choices ~init:1 ~f:(fun n (_, cands) ->
                  min 65 (n * List.length cands))
            in
            if count = 0 then []
            else if count <= 64 then assignments choices
            else [ List.map choices ~f:(fun (var, cands) -> (var, List.hd_exn cands)) ]
          in
          (* the strict and the non-strict step of one component, from the
             caller's formals to the arguments of a call *)
          let step caller_params caller_comp callee_params callee_comp args =
            match (caller_comp, callee_comp) with
            | `Int caller_measure, `Int measure ->
                let sub = Map.Poly.of_alist_exn
                    (List.zip_exn (List.map callee_params ~f:fst) args) in
                (* Formals bind scalar variables, not independently named
                   function heads in an explicit measure. Generic substitution
                   also renames those heads, which can manufacture a decrease. *)
                if not (Evaluator.scalar_substitution_is_safe sub
                          (Formula.eq measure measure)) then
                  invalid_arg "Unsafe scalar substitution in totality measure";
                let callee_measure = Term.subst sub measure in
                ( Formula.and_of
                    [ Formula.mk_atom (T_int.mk_leq zero caller_measure);
                      Formula.mk_atom (T_int.mk_lt callee_measure caller_measure) ],
                  Formula.mk_atom (T_int.mk_leq callee_measure caller_measure) )
            | `Sub i, `Sub j ->
                let x, sort = List.nth_exn caller_params i in
                let a = List.nth_exn args j in
                let strict =
                  if Atomic.get structural_testers_ignored then
                    (* a deliberately unsound mutant, for a property check *)
                    match
                      SubtermOrder.selector_chain_testers x (SubtermOrder.eta a)
                    with
                    | Some _ -> Formula.mk_true ()
                    | None -> Formula.mk_false ()
                  else SubtermOrder.strict_decrease x a
                in
                (strict, Formula.or_of [ Formula.eq a (Term.mk_var x sort); strict ])
            | _ -> (Formula.mk_false (), Formula.mk_false ())
          in
          let obligations measures =
            let obligations = ref [] in
            List.iter members ~f:(fun caller ->
                let (_, _, body, _, _) = Map.Poly.find_exn user caller in
                let caller_params, caller_measure =
                  List.Assoc.find_exn measures caller ~equal:Poly.equal in
                let rec walk guards (term : Term.t) = match term with
                  | Var (var, _, _) when Set.mem component var ->
                      invalid_arg "Known function used as a value in rank proof"
                  | Var _ -> ()
                  | FunApp (T_array.ALambda _, _, _) as term ->
                      if not (Set.are_disjoint (dependencies term) component) then
                        invalid_arg "Array lambda is outside integer rank proof"
                  | FunApp (T_bool.IfThenElse, [condition; yes; no], _) ->
                      walk guards condition;
                      let guard = Formula.eq condition (T_bool.make true) in
                      walk (guard :: guards) yes;
                      walk (Formula.mk_neg guard :: guards) no
                  | FunApp (T_bool.Formula phi, [], _) -> walk_formula guards phi
                  | FunApp (T_bool.Formula _, _, _) as term ->
                      if not (Set.are_disjoint (dependencies term) component) then
                        invalid_arg "Recursive call under formula binder or operator"
                  | FunApp (sym, args, _) ->
                      List.iter args ~f:(walk guards);
                      (match sym with
                       | FVar (callee, _, _) when Set.mem component callee ->
                           let callee_params, callee_measure =
                             List.Assoc.find_exn measures callee ~equal:Poly.equal in
                           let decrease =
                             match
                               List.map2 caller_measure callee_measure
                                 ~f:(fun caller_comp callee_comp ->
                                   step caller_params caller_comp callee_params
                                     callee_comp args)
                             with
                             | Ok [ (strict, _) ] -> strict
                             | Ok [ (strict1, nonstrict1); (strict2, _) ] ->
                                 Formula.or_of
                                   [ strict1; Formula.and_of [ nonstrict1; strict2 ] ]
                             | _ -> Formula.mk_false ()
                           in
                           obligations := Formula.mk_imply (Formula.and_of guards)
                               decrease
                               :: !obligations
                       | _ -> ())
                  | LetTerm _ -> invalid_arg "Unexpected remaining let in rank proof"
                (* A Boolean body read short-circuit, in either operand order
                   (the reader reorders conjuncts and disjuncts): an operand
                   of an [and] matters only where the other holds, of an [or]
                   only where the other fails, the conclusion of an [=>] only
                   where the premise holds and the premise only where the
                   conclusion fails.  The other operand is used as a
                   condition only when it applies no function of the
                   component, so that its value is already fixed by the
                   formals and the lower components; conditions that each
                   rest on the other's recursive call would be circular.  A
                   call under a quantifier or a [let] has no condition that
                   can be read here, and refuses. *)
                and walk_formula guards (phi : Formula.t) =
                  let fixed p =
                    Set.are_disjoint (dependencies (T_bool.of_formula p)) component
                  in
                  let both p q ~guard_p ~guard_q =
                    walk_formula
                      (if fixed q then guard_p :: guards else guards) p;
                    walk_formula
                      (if fixed p then guard_q :: guards else guards) q
                  in
                  match phi with
                  | Formula.Atom (Atom.App (_, args, _), _) ->
                      List.iter args ~f:(walk guards)
                  | Formula.Atom _ -> ()
                  | Formula.UnaryOp (Formula.Not, p, _) -> walk_formula guards p
                  | Formula.BinaryOp (Formula.And, p, q, _) ->
                      both p q ~guard_p:q ~guard_q:p
                  | Formula.BinaryOp (Formula.Or, p, q, _) ->
                      both p q ~guard_p:(Formula.mk_neg q) ~guard_q:(Formula.mk_neg p)
                  | Formula.BinaryOp (Formula.Imply, p, q, _) ->
                      both p q ~guard_p:(Formula.mk_neg q) ~guard_q:p
                  | Formula.BinaryOp ((Formula.Iff | Formula.Xor), p, q, _) ->
                      walk_formula guards p; walk_formula guards q
                  | Formula.Bind _ | Formula.LetRec _ | Formula.LetFormula _ ->
                      if not (fixed phi)
                      then invalid_arg "Recursive call under formula binder"
                in
                walk [] (if Term.is_let_free body then body else Term.elim_let body));
            !obligations
          in
          let proved label candidates =
            List.exists (assignments_of candidates) ~f:(fun measures ->
                match List.find (obligations measures) ~f:(fun o -> not (valid o)) with
                | None -> true
                | Some failed ->
                    trace (fun () -> sprintf "{%s} %s measure: obligation not proved: %s"
                             (String.concat ~sep:"," (List.map members ~f:Ident.name_of_tvar))
                             label (Formula.str_of failed));
                    false)
          in
          let total =
            proved "integer" int_candidates
            || (List.exists members ~f:(fun var -> not (List.is_empty (record_fields var)))
                && proved "integer or record field" int_field_candidates)
            || proved "structural" structural_singletons
            || proved "structural pair" structural_pairs
          in
          if not total then
            trace (fun () -> sprintf "{%s}: no measure proves the component"
                     (String.concat ~sep:"," (List.map members ~f:Ident.name_of_tvar)));
          total
        in
        List.for_all components ~f:component_total
  with exn when not (Common.Timer.is_async exn) ->
    trace (fun () -> "refused by exception: " ^ Exn.to_string exn);
    false

(* The largest sub-context closed under calls that the totality certificate
   accepts: the union of the call closures that are total each, kept only
   when the union is certified as well (so it has a solution, its standard
   one, in every structure of the theory); empty otherwise.  On a datatype
   input this is at least the generated size functions, which no user body
   needs to call and which the projection below could not otherwise match. *)
let total_closed_subcontext ~id (fenv : FunEnv.t) : FunEnv.t =
  let callees var =
    match Map.Poly.find fenv var with
    | None -> Set.Poly.empty
    | Some (_, _, body, _, _) ->
        let body = if Term.is_let_free body then body else Term.elim_let body in
        Set.Poly.filter_map (Term.fvar_apps_of body) ~f:(function
          | FunApp (FVar (callee, _, _), _, _) when Map.Poly.mem fenv callee ->
              Some callee
          | _ -> None)
  in
  let rec closure seen = function
    | [] -> seen
    | var :: rest when Set.mem seen var -> closure seen rest
    | var :: rest ->
        closure (Set.add seen var) (Set.to_list (callees var) @ rest)
  in
  let restrict vars = Map.Poly.filter_keys fenv ~f:(Set.mem vars) in
  let total vars =
    (not (Set.is_empty vars))
    && (try has_total_defining_context ~id (restrict vars)
        with exn when not (Common.Timer.is_async exn) -> false)
  in
  let union =
    Map.Poly.keys fenv
    |> List.filter_map ~f:(fun var ->
           let vars = closure Set.Poly.empty [ var ] in
           if total vars then Some vars else None)
    |> Set.Poly.union_list
  in
  if Set.length union = Map.Poly.length fenv || not (total union) then
    Map.Poly.empty
  else restrict union

(* The projection with a total closed sub-context [T] (above) kept as
   defined: candidates are sought only for the other entries [R], whose
   bodies may call [T]; the candidate equalities are proved valid with [T]'s
   symbols uninterpreted, hence for every interpretation of them and in
   particular for [T]'s standard one, and the constraints, once the
   candidates are substituted, must not mention [T].  So in every structure
   satisfying those constraints, [T]'s standard solution and the candidates
   form a defining model.  Asked only where the plain projection found
   nothing; each question is bounded by Z3's resource count. *)
let projection_over_total_rlimit = 100_000

let defining_context_projection_model_over_total ~id fenv phis =
  let kept = total_closed_subcontext ~id fenv in
  if Map.Poly.is_empty kept then None
  else
    with_rlimit ~label:"projection_over_total" (Some projection_over_total_rlimit)
      (fun () -> defining_context_projection_model_core ~id ~kept fenv phis)

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
      let ((phis', picked) as pre) =
        Common.PhaseTime.with_phase "bv-range" (fun () ->
            int_to_bv_range_subst phis)
      in
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
      (* the question as given, in a context of its own like the split
         forms ([int_to_bv_split_ask_original]) *)
      let original () =
        Atomic.incr int_to_bv_split_original_asked;
        check_sat_base ~timeout ~fresh_solver ~scoped ~defining_equations
          ?fun_values_out ~id fenv phis
      in
      let full () =
        if
          Atomic.get int_to_bv_split_ask_original
          && not (List.is_empty quotients)
        then original ()
        else full ()
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
   otherwise report a satisfiable problem [unsat]. Unsupported native
   array-lambda refutations are also declined by [certify_shared_native_result];
   other negative answers are kept. The recursive-under-binder shape is tested
   only after a [`Sat], so a question without it costs
   nothing more.

   Rejected: confirming the [`Sat] by substituting the model's values into the
   question and asking whether the negation of the result is unsatisfiable.
   The model's array values arrive as [lambda] terms, and Z3 5.1.0 answers
   [unsat] to [cnt 0 3 (lambda i. ite (i = 2) 15922 0) >= 2] for the count of
   [x] among the first [t] cells -- a true ground formula -- so the
   confirmation accepted the very model it was to reject. *)
let without_known_interpretations fenv values =
  List.filter values ~f:(fun ((var, _), _) -> not (Map.Poly.mem fenv var))

(* [finite_model_value_is_independent fenv term]: [true] only if [term]
   mentions no symbol defined by [fenv], looking inside every binder body.

   Contract.  Assumes nothing of [term]'s shape.  Guarantees: if the answer is
   [true], no subterm of [term] -- including the body of an array [lambda], of
   an embedded formula, of a quantifier or of a [let] -- is a variable or a
   function application whose identifier [fenv] defines, and no predicate
   application names such an identifier.  Hence the denotation of [term] in a
   structure does not depend on how that structure interprets the defined
   symbols: two structures agreeing on everything else give it one value.
   Conservative in three places, each answering [false] where it could not
   prove independence: a bound variable spelled like a defined symbol (no
   scope tracking), a predicate fixpoint or [letrec] (whose bodies the term
   visitors do not expose uniformly), and a predicate variable spelled like a
   defined symbol.  It is total and raises nothing.

   Serialized array lambdas are thus allowed exactly when their bodies are
   independent: a lambda is a closed description of an array value, and the
   array it denotes is fixed by its body alone. *)
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
        | Atom.App (Predicate.Var (Ident.Pvar name, _), _, _)
          when Map.Poly.mem fenv (Ident.Tvar name) -> false
        | Atom.App (_, args, _) -> List.for_all args ~f:term_ok
        | Atom.True _ | Atom.False _ -> true)
    | Formula.UnaryOp (_, phi, _) | Formula.Bind (_, _, phi, _) -> formula_ok phi
    | Formula.BinaryOp (_, left, right, _) -> formula_ok left && formula_ok right
    | Formula.LetFormula (_, _, def, body, _) -> term_ok def && formula_ok body
    | Formula.LetRec _ -> false
  in
  term_ok term

(* [value_uses_known_functions fenv term]: may the value [term], read from a
   native model, depend on the native interpretation of a symbol [fenv]
   defines?  [false] only when [finite_model_value_is_independent] proves it
   does not; every doubt answers [true].

   Why the lambda body is inspected rather than every lambda refused.  A
   background value is returned to a caller as part of a countermodel, and the
   certificate extends the background by the standard interpretation of the
   defined symbols, discarding the native one.  That is sound for a value whose
   denotation does not change when the defined symbols are reinterpreted --
   which holds for an array [lambda] whose body mentions none of them, as for
   any other term.  Refusing every lambda whenever [fenv] is non-empty withheld
   every countermodel that interprets an array-valued free symbol (each comes
   back as a lambda) in a context defining any function at all, so validation
   learnt nothing from those questions.  A lambda whose body applies a defined
   symbol is still refused: fixing it would pin the native interpretation. *)
let value_uses_known_functions fenv term =
  not (finite_model_value_is_independent fenv term)

(* [query_uses_known_functions fenv phis]: may the truth of some formula of
   [phis] depend on how a structure interprets a symbol [fenv] defines?
   [false] only when no formula mentions such a symbol, looking inside every
   binder body; every doubt answers [true].

   Contract.  Assumes nothing of [phis].  Guarantees: if the answer is
   [false], no subterm of any formula of [phis] -- including the body of an
   array [lambda] -- is a variable or a function application whose
   identifier [fenv] defines.  So two structures agreeing on every other
   symbol give each formula one truth value under every assignment (the
   induction of [finite_model_value_is_independent], for formulas): a
   background structure satisfying [phis] still satisfies them once the
   defining equations' standard interpretation replaces the native one.  It
   is total, raises nothing, and answers [false] for an empty [fenv].

   The original vocabulary is checked, nullary values included, before any
   declaration slicing.  The filtered traversal hides array-lambda bodies
   (its other callers use its result outside the binder's scope), so a
   lambda is judged by [finite_model_value_is_independent], which reads the
   body: a lambda is refused when its body mentions a defined symbol, when
   its binder (or a binder inside it) is spelled like one -- no scope is
   tracked, so a shadowing binder is read as an occurrence -- and when it
   holds a predicate fixpoint, a [letrec] or a predicate variable spelled
   like a defined symbol.  Refusing every lambda instead declined every
   validation countermodel whose array values (each returned as a lambda)
   were substituted into a query applying a defined symbol, although the
   residual left after unfolding no longer mentioned one. *)
let query_uses_known_functions fenv phis =
  (not (Map.Poly.is_empty fenv))
  && List.exists phis ~f:(fun phi ->
         not
           (Set.is_empty
              (Formula.filtered_terms_of phi ~f:(function
                | Var (var, _, _) | FunApp (FVar (var, _, _), _, _) ->
                    Map.Poly.mem fenv var
                | FunApp (T_array.ALambda _, _, _) as lambda ->
                    not (finite_model_value_is_independent fenv lambda)
                | _ -> false))))

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
let shared_native_context_is_first_order_uncached fenv =
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

(* [shared_native_context_is_first_order_uncached] remembered for the last
   environment asked in this domain, by physical identity: the answer is a
   function of the (immutable) environment alone, and it is asked about the
   same environment once per certified answer -- one walk over every
   definition body per validity question of the predicate elimination. *)
let first_order_memo : (FunEnv.t * bool) option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let shared_native_context_is_first_order fenv =
  match Stdlib.Domain.DLS.get first_order_memo with
  | Some (fenv', answer) when phys_equal fenv fenv' -> answer
  | _ ->
      let answer = shared_native_context_is_first_order_uncached fenv in
      Stdlib.Domain.DLS.set first_order_memo (Some (fenv, answer));
      answer

(* Native recursive checking can refute a true ground count applied to a
   serialized array lambda, including one introduced by a known definition.
   Inspect the complete defining context and every embedded body, including local
   predicate definitions, instead of the synthesis visitor which hides them.
   Complete ordinary defining equations and empty contexts keep their negative
   answers; only the unsupported native lambda route supplies no certificate. *)
let rec term_contains_array_lambda (term : Term.t) = match term with
    | Var _ -> false
    | LetTerm (_, _, def, body, _) -> term_contains_array_lambda def || term_contains_array_lambda body
    | FunApp (T_array.ALambda _, _, _) -> true
    | FunApp (T_bool.Formula phi, args, _) ->
        formula_contains_array_lambda phi || List.exists args ~f:term_contains_array_lambda
    | FunApp (_, args, _) -> List.exists args ~f:term_contains_array_lambda
and formula_contains_array_lambda = function
    | Formula.Atom (atom, _) -> (match atom with
        | Atom.App (pred, args, _) ->
            (match pred with Predicate.Fixpoint def -> formula_contains_array_lambda def.Formula.body | _ -> false)
            || List.exists args ~f:term_contains_array_lambda
        | Atom.True _ | Atom.False _ -> false)
    | Formula.UnaryOp (_, phi, _) | Formula.Bind (_, _, phi, _) -> formula_contains_array_lambda phi
    | Formula.BinaryOp (_, left, right, _) -> formula_contains_array_lambda left || formula_contains_array_lambda right
    | Formula.LetFormula (_, _, def, body, _) -> term_contains_array_lambda def || formula_contains_array_lambda body
    | Formula.LetRec (defs, body, _) ->
        List.exists defs ~f:(fun def -> formula_contains_array_lambda def.Formula.body) || formula_contains_array_lambda body

let query_contains_array_lambda phis = List.exists phis ~f:formula_contains_array_lambda

let defining_context_contains_array_lambda fenv =
  Map.Poly.exists fenv ~f:(fun (_, _, body, _, _) -> term_contains_array_lambda body)

(* A native [sat] to a query that applies known functions is a model of the
   query extended by the native solver's interpretation of those functions,
   which nothing here certifies to satisfy their defining equations.  It is
   accepted only through a check that does not read that interpretation:

   - the complete defining context is first-order and certified total, so in
     every model of the background theory the defining equations have a
     solution (the standard interpretation; unique, as each certified
     recursion decreases a well-founded measure);
   - the model's values of the other free symbols, none of which mentions a
     known function, are substituted into the query, and every application of
     a known function is unfolded along the guards its definition reads
     ([Evaluator.unfold_rec_apps]), until none is left;
   - the result is valid with no known function in scope, and mentions no
     known symbol, inside array [lambda] bodies included
     ([query_uses_known_functions]).

   Unfolding replaces an application by the definition's body at its
   arguments, an equivalence in every model of the defining equations.  So in
   any model of the background agreeing with the substituted values and
   extended by the standard interpretation, the query holds whatever the
   symbols left open are: the background part of the native model, extended
   by that interpretation, satisfies the query.  The native values of the
   known functions are discarded.

   Binders.  A model value substituted under a [lambda] of the query cannot
   be captured: the substitution renames a binder that a value mentions
   free, and a binder shadows a substitution for its own name.  The
   unfolding gives up at a [lambda] whose body applies any function, so no
   application under a [lambda]'s binder is ever unfolded, and in particular
   none whose head the binder shadows.  A [lambda] whose body mentions no
   known symbol -- every array value of the model comes back as one -- is
   carried into the residual unchanged; its denotation does not read the
   known functions' interpretation, so the validity of a residual holding it
   is still a statement about the background alone.

   The values name an element of an uninterpreted sort by a constant
   ([<sort>!val!<k>]), distinct names denoting distinct elements of the
   native model.  The residual question is therefore asked under the premise
   that the element constants of one sort occurring in the values (and not
   among the query's own variables) are pairwise distinct: the background part
   of the native model satisfies that premise, so it is among the models in
   which the residual is shown to hold.  Without the premise a residual that
   reduces to [s!val!0 != s!val!1] is not valid, and every countermodel that
   separates two list elements of an uninterpreted element sort was withheld
   after its native question had been paid for (seconds each on list inputs
   with a recursive [length]).  A guard left undecided by the values
   (an unassigned variable, a selector applied off its constructor), the
   fuel running out, or a residual that is not valid declines, which keeps
   the answer [`Unknown] as before. *)
let known_function_body_is_closed = Evaluator.known_function_body_is_closed

(* The opt-in second check of [known_function_sat_is_certified]: [None] (the
   default) leaves it off; [Some n] asks it under a Z3 resource limit of [n]
   (with a 1 s wall clock kept only as a kill).  Process-wide, written once
   when a solver configuration that asks for it is loaded. *)
let known_function_open_residual_rlimit : int option Atomic.t = Atomic.make None
let set_known_function_open_residual_rlimit n =
  Atomic.set known_function_open_residual_rlimit n

(* Where [known_function_sat_is_certified] asks its residual question (the
   negated residual under the elements' distinctness, [Unsat] read as the
   proof).  The question is asked with an empty function environment and on
   the fresh-context path, which never pushes, so a clean pooled context
   ([lease_clean_instance]) holds nothing under which it decides less than a
   fresh one; only [Unsat] is read, and that is a proof in any context.
   - [Residual_fresh] (the default): a fresh context per question, under the
     process-wide collection rule;
   - [Residual_clean_pool]: a clean pooled context ([with_clean_reset_pool]),
     so that a new context, and its forced collection, is made only when the
     pool has none waiting;
   - [Residual_full_major_every n]: a fresh context per question, with the
     forced collection before every n-th new context only
     ([with_new_context_full_major_every]); the questions are the same.
   Why: the certificate is asked once per cell of a labeling or a synthesis
   round that Z3 answered [sat] in a context defining known functions, and on
   a run with hundreds of such cells over a heap of a few GB the collections
   before their fresh contexts (about 1.2 s each, one per eight contexts) were
   a quarter of the run.  Process-wide, written once when a solver
   configuration that asks for it is loaded. *)
type residual_contexts =
  | Residual_fresh
  | Residual_clean_pool
  | Residual_full_major_every of int

let known_function_residual_contexts = Atomic.make Residual_fresh
let set_known_function_residual_contexts r =
  Atomic.set known_function_residual_contexts r

let in_residual_contexts f =
  match Atomic.get known_function_residual_contexts with
  | Residual_fresh -> f ()
  | Residual_clean_pool -> with_clean_reset_pool f
  | Residual_full_major_every n -> with_new_context_full_major_every n f

(* The second check, for a residual that is not valid: it is accepted when it
   is quantifier-free, every free symbol it has is one of the model's element
   constants [elements] (no query variable left unassigned, no uninterpreted
   function left unsubstituted), and it is satisfiable together with the
   pairwise distinctness of those constants.

   Why that suffices.  Take a structure [M'] of the background theory
   satisfying the residual and the distinctness (one exists, by the [sat]).
   Interpret every query variable by the denotation in [M'] of the value the
   model gave it; the values are constructor terms over the element
   constants, so this assignment is the returned one up to an injective
   renaming of elements.  The defining context is certified total, so in
   [M'] its equations have exactly one solution, the standard interpretation;
   a defined symbol being chosen per background together with the unknowns,
   that solution is the only interpretation of the known functions available
   in [M'].  Unfolding is an equivalence in every model of
   the equations, so in [M'] extended by it the query holds at the assignment.
   Hence the query is satisfiable in a model of the theory with the
   definitions, which is all a [sat] answer claims: a native [sat] to a query
   applying no known function makes the same existential claim, its model
   fixing the terms the theory leaves open ([hd nil]) in some way the caller
   is never told.  What is not claimed, and what the validity check gives, is
   that the BACKGROUND PART OF THE NATIVE MODEL satisfies the query; the two
   models may disagree on the open terms.

   A residual with a free symbol other than an element constant is declined,
   since [M'] would choose its value and the returned assignment does not
   fix it; a quantified residual is declined because only a quantifier-free
   [sat] of Z3 is taken here as a model, and a residual holding an array
   [lambda] (a binder, which the quantifier-free test does not count) is
   declined for the same reason.  An [unsat], [unknown] or exhausted
   limit declines. *)
(* Set while [is_valid] runs: its caller reads only [true] for a proof, so a
   certified countermodel and a declined one both come back [false], and the
   open-residual question would be paid for nothing.  Under the flag it is not
   asked, which makes the answer exactly the one with the switch off. *)
let only_validity_read_key : bool Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> false)

(* how many open-residual questions were asked, for the self-check *)
let open_residual_asked = Atomic.make 0

let open_residual_is_satisfiable ~id ~elements ~distinct_elements residual =
  match Atomic.get known_function_open_residual_rlimit with
  | None -> false
  | Some _ when Stdlib.Domain.DLS.get only_validity_read_key -> false
  | Some rlimit ->
      Formula.is_quantifier_free residual
      && (not (formula_contains_array_lambda residual))
      && Set.for_all (Formula.fvs_of residual) ~f:(fun x ->
             List.exists elements ~f:(fun (y, _) -> Stdlib.(x = y)))
      && Common.PhaseTime.with_phase "known-fn-open-residual" (fun () ->
             Atomic.incr open_residual_asked;
             match
               with_rlimit (Some rlimit) (fun () ->
                   check_sat_base ~timeout:(Some 1000) ~fresh_solver:true ~id
                     (FunEnv.mk_empty ())
                     (residual :: distinct_elements))
             with
             | `Sat _ ->
                 Common.PhaseTime.with_phase "accepted" (fun () -> ());
                 true
             | _ -> false)

let known_function_sat_is_certified ~id fenv phis model =
  (* The legacy unfolding substitution also rewrites FVar heads. Scalar
     formals do not bind those heads, so a same-spelling overlap would make
     the residual an unsound certificate. Conservatively decline this context,
     including occurrences hidden by a nested binder; leave generic Term.subst
     unchanged. Unsupported traversal also declines, preserving async exits. *)
  let formal_substitution_is_safe params body =
    try
      not (Set.exists (Term.funsyms_of body) ~f:(function
        | FVar (var, _, _) ->
            List.exists params ~f:(fun (formal, _) -> Ident.tvar_equal var formal)
        | _ -> false))
    with exn when not (Common.Timer.is_async exn) -> false
  in
  Map.Poly.for_all fenv ~f:(fun (params, _, body, _, _) ->
    known_function_body_is_closed params body)
  && shared_native_context_is_first_order fenv
  && Map.Poly.for_all fenv ~f:(fun (params, _, body, _, _) ->
       formal_substitution_is_safe params body)
  && has_total_defining_context ~id fenv
  &&
  let background = without_known_interpretations fenv model in
  (not (List.exists background ~f:(fun (_, value) ->
            Option.exists value ~f:(value_uses_known_functions fenv))))
  &&
  let sub =
    Map.Poly.of_alist_reduce ~f:(fun first _ -> first)
      (List.filter_map background ~f:(fun ((var, _), value) ->
           Option.map value ~f:(fun value -> (var, value))))
  in
  let elements =
    let query_vars = Formula.tvs_of (Formula.and_of phis) in
    Map.Poly.data sub
    |> List.concat_map ~f:(fun value ->
           Set.to_list (Term.term_sort_env_of value))
    |> List.filter ~f:(fun (Ident.Tvar name, _) ->
           String.is_substring name ~substring:"!val!"
           && not (Set.mem query_vars (Ident.Tvar name)))
    |> List.dedup_and_sort ~compare:Stdlib.compare
  in
  let distinct_elements =
    elements
    |> List.sort_and_group ~compare:(fun (_, s1) (_, s2) ->
           Stdlib.compare s1 s2)
    |> List.concat_map ~f:(fun group ->
           let rec pairs = function
             | [] -> []
             | (x, s) :: rest ->
                 List.map rest ~f:(fun (y, _) ->
                     Formula.neq (Term.mk_var x s) (Term.mk_var y s))
                 @ pairs rest
           in
           pairs group)
  in
  try
    match
      Evaluator.unfold_rec_apps ~fenv
        (Formula.subst sub (Formula.and_of phis))
    with
    | None -> false
    | Some residual ->
        (not (query_uses_known_functions fenv [ residual ]))
        && (Formula.is_true (Evaluator.simplify residual)
           || (match
             in_residual_contexts (fun () ->
                 check_sat_base ~timeout:(Some 1000) ~fresh_solver:true ~id
                   (FunEnv.mk_empty ())
                   (Formula.negate residual :: distinct_elements))
           with
           | `Unsat -> true
           | _ -> false)
           || open_residual_is_satisfiable ~id ~elements ~distinct_elements
                residual)
  with exn when not (Common.Timer.is_async exn) -> false

(* [certify_shared_native_result ~id fenv phis ret]: the answer [ret] Z3 gave
   on [phis] in a context defining [fenv], kept only where it is evidence.

   The [`Unsat] arm is a workaround for a Z3 5.1.0 defect: Z3 answers
   [unsat] to a TRUE ground formula that applies a recursive function to an
   array [lambda] -- a function counting the cells below 3 of
   [lambda i. ite (i = 2) 15922 0] that hold 0 is refuted at the bound 2,
   while the same array written as a [store] chain is answered [sat], as is
   the formula by Z3 4.15.4 and 5.3.1.  So a native [unsat] is read as
   undecided when the context defines a recursive function outside the
   family whose defining equations are checked directly (Bool and Int
   formals and result) and a [lambda] array occurs in the question or in a
   definition.  The first [`Sat] arm is a workaround too, for the wrong
   [sat] described at [recursive_function_under_binder]; the last follows
   from the semantics, not from a defect: a native interpretation of a known
   function is not evidence that its defining equation holds. *)
(* Whether [phis] use a sequence whose elements are themselves sequences (or
   hold one): an operation of the sequence theory at such an element sort, or
   a variable of such a sequence sort. *)
let mentions_nested_sequence phis =
  let nested_elem se = SeqAxiomEncoding.mentions_seq_sort se in
  List.exists phis ~f:(fun phi ->
      Set.exists (Formula.funsyms_of phi) ~f:(function
        | T_seq.SqEmpty se
        | T_seq.SqUnit se
        | T_seq.SqConcat se
        | T_seq.SqLen se
        | T_seq.SqNth se
        | T_seq.SqExtract se
        | T_seq.SqStore se ->
            nested_elem se
        | _ -> false)
      || Set.exists
           (Set.union (Formula.term_sort_env_of phi)
              (Formula.quantified_sort_env_of phi))
           ~f:(function _, T_seq.SSeq se -> nested_elem se | _ -> false))

(* The second opinion a native [unsat] on a nested-sequence question needs
   before it is read as one ([certify_shared_native_result]):
   [confirm ~id fenv phis] is [true] only when another procedure has shown
   the conjunction of [phis] unsatisfiable in every model.  Installed by a
   layer above this one (an independent solver run as a process); while none
   is installed every such [unsat] is read as undecided. *)
let nested_sequence_refutation_confirmer :
    (id:int option -> FunEnv.t -> Formula.t list -> bool) option Atomic.t =
  Atomic.make None

(* [asked_sequence_free] says that the solver call which answered [ret] was
   given a question with no sequence sort and no sequence operation at all
   (the axiomatised copy of [phis] that [prove_valid_by_seq_axioms] asks:
   every sequence sort an uninterpreted sort, every operation an
   uninterpreted function, with axioms that are theorems of the sequence
   theory).  Z3's sequence theory then took no part in the refutation, so
   the nested-sequence arm below, whose reason is a defect of that theory,
   does not apply; the other arms read [phis] as before. *)
let certify_shared_native_result ?(asked_sequence_free = false) ~id fenv phis
    ret =
  (* counted only: a refutation the nested-sequence arm would have sent to
     the second procedure, read without it; changes nothing *)
  (match ret with
  | `Unsat when asked_sequence_free && mentions_nested_sequence phis ->
      Common.PhaseTime.event_here "nested-seq-unsat-sequence-free"
  | _ -> ());
  (fun result -> match ret, result with
    | (`Sat _ | `Unsat), `Unknown _ -> note_declined result
    | _ -> result) @@
  match ret with
  (* A workaround for a Z3 defect in its sequence theory, present from 4.12.0
     to the 5.3.4 nightly of 2026-11-02 (and absent from cvc5 1.4.2): with
     sequences of sequences, Z3's [smt] core (the one a pushed or pooled
     solver uses, and the default tactic on small questions) answers [unsat]
     to a satisfiable set of seven quantifier-free assertions over five
     sequences [A..E] of sequences of integers -- equalities between tails
     [seq.extract (x ++ [u]) 1 (len x)] of [x ++ [u]] for x in A..E, two
     disjunctions [len x <= 0 \/ seq.nth x 0 = u] and [len D <= 0] -- which
     every one of them being empty satisfies, as the same assertions with
     those values substituted are answered [sat] by the same core.  Read as a
     validity proof, that [unsat] let the predicate eliminator drop a goal
     resolvent whose body a Rust program's run satisfies (a push through
     [&mut v[0]] of a [Vec<Vec<i32>>], then an assertion on [v[0].len()] that
     fails), and the run answered [sat] for an unsatisfiable problem.  The
     same assertions over sequences of integers are answered [sat], so the
     guard is the element sort: such an [unsat] stands only when an
     independent procedure confirms it, and is undecided otherwise -- which
     can lose a proof, never give a wrong one. *)
  | `Unsat when (not asked_sequence_free) && mentions_nested_sequence phis -> (
      match Atomic.get nested_sequence_refutation_confirmer with
      | Some confirm when confirm ~id fenv phis ->
          Common.PhaseTime.event_here "nested-seq-unsat-confirmed";
          `Unsat
      | _ ->
          Common.PhaseTime.event_here "nested-seq-unsat-unconfirmed";
          `Unknown
            "nested-sequence refutation not confirmed by a second procedure")
  | `Unsat when not (Map.Poly.is_empty fenv)
                && not (supports_defining_equations fenv)
                && (query_contains_array_lambda phis
                    || defining_context_contains_array_lambda fenv) ->
      `Unknown "native recursive array-lambda refutation has no verified certificate"
  | `Sat _ when Common.PhaseTime.with_phase "c-recbind" (fun () -> recursive_function_under_binder fenv (Formula.and_of phis)) ->
      `Unknown "a recursive function under a quantifier: sat is not a model"
  | `Sat model when not (Map.Poly.is_empty fenv) ->
      if (not (Common.PhaseTime.with_phase "c-uses" (fun () -> query_uses_known_functions fenv phis)))
         && Common.PhaseTime.with_phase "c-fo" (fun () -> shared_native_context_is_first_order fenv)
         && Common.PhaseTime.with_phase "c-total" (fun () -> has_total_defining_context ~id fenv)
      (* Only the background assignment is certified extendable. Native
         interpretations of the unused known functions are not certificates. *)
      then
        let background = without_known_interpretations fenv model in
        if List.exists background ~f:(fun (_, value) ->
             Option.exists value ~f:(value_uses_known_functions fenv))
        then `Unknown "shared background model retains an uncertified known-function value"
        else `Sat background
      else if Common.PhaseTime.with_phase "c-kfn" (fun () -> known_function_sat_is_certified ~id fenv phis model) then
        `Sat (without_known_interpretations fenv model)
      else `Unknown "known-function context has no verified shared model certificate"
  | _ -> ret




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


let finite_expansion_skip_empty = Atomic.make true
let set_finite_expansion_skip_empty b = Atomic.set finite_expansion_skip_empty b

(* [None] at once for an empty [fenv] ([finite_expansion_skip_empty], on):
   then no term calls a function of [fenv], so [calls] below is empty and
   the guard answers [None]; the only parts of the guard evaluated before
   [List.is_empty calls] are a scope traversal of [phis] and a test over the
   empty [fenv], both total, so skipping them changes no answer.  Without
   the skip every question with no definitions -- nearly all of them --
   paid two full traversals of itself (a third of a millisecond on a small
   linear question, several on a linear program of a thousand rows). *)
let rec check_sat_by_finite_defining_expansion ~timeout ?fun_values_out ~id fenv phis =
  if Atomic.get finite_expansion_skip_empty && Map.Poly.is_empty fenv then None
  else check_sat_by_finite_defining_expansion_full ~timeout ?fun_values_out ~id fenv phis

and check_sat_by_finite_defining_expansion_full ~timeout ?fun_values_out ~id fenv phis =
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
      (* Asked in a pooled context: the expanded query mentions no known
         function, so it is an ordinary query, and the pool is what every
         query without definitions uses.  Only a [sat] is read here and
         every other answer falls back to the native question, so a context
         made for this question alone (a forced full major collection and
         the datatypes declared again, about 30 ms each) was paid on every
         validity question of the elimination and thrown away whenever the
         answer was [unsat]: about 920 of them exhausted 120 s on a
         30-function input. *)
      match check_sat_base ~timeout ~fresh_solver:false
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

(* [without_unreached_explicit fenv phis]: [fenv] without every entry that
   [phis] do not reach ([fenv_reached_by]) and that is EXPLICIT -- on no
   cycle of the call graph through bodies and properties, and with a true
   property.  The recursion flag is not read: an entry made by
   [define-fun-rec], or by reconstructing a function from a predicate, is
   flagged recursive whether or not its body calls itself, and only a cycle
   makes an equation constrain anything.  A variable spelled like a dropped nullary
   entry is therefore read as independent of it, which is the intended
   reading: a reference to a defined constant is always an application, so a
   same-named variable only arises from an accidental name clash.

   Contract: for every [phis], [phis] together with the defining equations
   (or the native definitions) of the result has a model iff it has one
   together with those of [fenv], and a model of the former extends to one of
   the latter by giving each dropped function the value of its body.  Why
   that holds: a dropped entry is applied by no formula of [phis] and, being
   unreached, by no kept entry either; the dropped entries call one another
   only acyclically, so they can be evaluated in a topological order from
   values the model already fixes (the theory's symbols, the kept
   functions, and the parameters), and a true property adds nothing to
   satisfy.  A recursive entry is never dropped: an unused recursive equation
   can be unsatisfiable or constrain the symbols it shares.

   Why: every entry of the environment is stated to Z3, as a universally
   quantified defining equation on the defining-equation route, whether or not
   the question applies it, and Z3 (4.13.3, 4.15.2 and 5.1.0 alike) does not
   decide even [forall a. f a = ite (a > 0) a 0] alone, which model-based
   quantifier instantiation never closes.  A function reconstructed from a
   predicate during preprocessing put one such definition into the
   environment, and every later question of the predicate elimination --
   three quantifier-free validity checks over Booleans and linear integer
   terms -- ran to the time limit beside it, on inputs answered in under a
   second when it is absent.  The returned value is [fenv] itself (physically)
   when nothing is dropped. *)
let without_unreached_explicit (fenv : FunEnv.t) phis =
  if Map.Poly.is_empty fenv then fenv
  else
    let reached = fenv_reached_by fenv (Formula.and_of phis) in
    if Map.Poly.length reached = Map.Poly.length fenv then fenv
    else
      (* the entries [var]'s body reaches, transitively, [var] excluded
         unless it is on a cycle *)
      let reaches_itself var def =
        let called syms =
          Set.Poly.filter_map syms ~f:(function
            | FVar (v, _, _) when Map.Poly.mem fenv v -> Some v
            | _ -> None)
        in
        let rec close seen frontier =
          if Set.mem frontier var then true
          else if Set.is_empty frontier then false
          else
            let seen = Set.union seen frontier in
            let next =
              Set.Poly.union_list
              @@ List.map (Set.to_list frontier) ~f:(fun v ->
                  let _, _, d, _, prop = Map.Poly.find_exn fenv v in
                  called (Set.union (Term.funsyms_of d) (Formula.funsyms_of prop)))
            in
            close seen (Set.diff next seen)
        in
        close Set.Poly.empty (called (Term.funsyms_of def))
      in
      let explicit var (_, _, def, _, property) =
        Formula.is_true property && not (reaches_itself var def)
      in
      let dropped =
        Map.Poly.filteri fenv ~f:(fun ~key ~data ->
            (not (Map.Poly.mem reached key)) && explicit key data)
      in
      if Map.Poly.is_empty dropped then fenv
      else Map.Poly.filter_keys fenv ~f:(fun v -> not (Map.Poly.mem dropped v))

let check_sat =
  fun ?(timeout = None) ?(fresh_solver = false) ?(scoped = false)
      ?fun_values_out ~id fenv phis ->
    let fenv = without_unreached_explicit fenv phis in
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
      else
        Common.PhaseTime.with_phase "cs-finite" (fun () ->
            check_sat_by_finite_defining_expansion ~timeout
              ?fun_values_out:staged_values ~id fenv phis)
    in
    (* [with_model_unread]: no model asked of Z3 where nothing reads it *)
    let skip_model =
      Atomic.get model_unread
      && (Stdlib.Domain.DLS.get model_unread_key
         || Atomic.get model_unread_mutant_always)
      && Option.is_none fun_values_out && Map.Poly.is_empty fenv
    in
    (* the declaration covers this question only: a question asked while
       answering it is asked with the model, unless its own caller says *)
    with_dls model_unread_key false @@ fun () ->
    let ret = match finite with
      | Some ret -> ret
      | None -> Common.PhaseTime.with_phase "cs-unguarded" (fun () ->
          with_dls model_skip_key skip_model (fun () ->
          check_sat_unguarded ~timeout ~fresh_solver ~scoped ~defining_equations
          ?fun_values_out:staged_values ~id fenv phis))
    in
    let ret =
      if defining_equations || Option.is_some finite then ret
      else Common.PhaseTime.with_phase "cs-certify" (fun () -> certify_shared_native_result ~id fenv phis ret)
    in
    let ret =
      match ret, staged_values with
      | `Sat _, Some staged
        when (not defining_equations) && Option.is_none finite
             && not (shared_native_function_values_are_independent fenv !staged) ->
          note_declined
          (`Unknown "shared function model retains an uncertified known-function value")
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
type base_session = {
  bs : instance;
  mutable bs_ok : bool;
  bs_memo : (Formula.t, Z3.Expr.expr) Hashtbl.t option;
  mutable bs_memo_envs : (fenv * dtenv) option;
  mutable bs_base : Formula.t list;
      (* the base last set, which a model of an extension also answers *)
}

(* [~memo:true]: the extensions' conjuncts are converted through a table
   kept for the session's lifetime, keyed by the formula's structure, so a
   conjunct asked in an earlier check (a frame lemma, which a run of checks
   against one base keeps asking) is not converted again.  Exact for the
   reason the conversion memo is: conversion into one context with the same
   function and datatype environments is a function of the formula, and Z3
   hash-conses its terms, so the held term is the one a new conversion would
   build; the table is emptied whenever the instance's environments are
   replaced.  The extension is asserted as the list of its conjuncts instead
   of their conjunction, the same question.  A conjunct with a [let], which
   the plain conversion lifts out of the whole formula, makes the extension
   take the plain conversion.  The table grows with the distinct conjuncts
   the session is asked, at most the formulas its caller built. *)
let base_session_create ?(memo = false) ~id () =
  let inst = get_instance id [ ("model", "true") ] (Hashtbl.Poly.create ()) in
  {
    bs = inst;
    bs_ok = false;
    bs_memo =
      (if memo then Some (Common.Ext.Hashtbl.PolyDeep.create ()) else None);
    bs_memo_envs = None;
    bs_base = [];
  }

(* [phis] converted in [s]'s context; [None] when a known-function context
   or the bit-vector range rewrite requires the caller's normal fallback.
   The context's datatypes are refreshed before every conversion; a refresh
   that has nothing to declare costs little ([z3_dtenv_of_formula] remembers
   it), which is what makes the range-guard session of
   [check_sat_seq_as_array] affordable (97,000 integer formulas in one run).
   With [~memo], through the session's table (see [base_session_create]),
   the result being the conjuncts' terms *)
let base_session_convert ?(memo = false) ~id s fenv phis =
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
    let convert = of_formula_with_z3fenv ~id ctx [] [] inst.fenv inst.dtenv in
    Some
      (Common.PhaseTime.with_phase "to-z3" (fun () ->
           let conjs = List.concat_map phis ~f:Formula.conjuncts_list_of in
           match s.bs_memo with
           | Some table when memo && List.for_all conjs ~f:Formula.is_let_free
             ->
               (match s.bs_memo_envs with
               | Some (f, d) when phys_equal f inst.fenv && phys_equal d inst.dtenv
                 ->
                   ()
               | _ ->
                   Hashtbl.clear table;
                   s.bs_memo_envs <- Some (inst.fenv, inst.dtenv));
               (* with COAR_MUCYC_PHASE_TIME, [session-memo-miss] counts the
                  conjuncts converted; observation only *)
               List.map conjs ~f:(fun phi ->
                   Hashtbl.find_or_add table phi ~default:(fun () ->
                       Common.PhaseTime.event "session-memo-miss";
                       convert phi))
           | _ -> List.map phis ~f:convert))

let base_session_set ~id s fenv base =
  s.bs_ok <- false;
  s.bs_base <- base;
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

(* [~read_model:false]: a satisfiable extension answers [`Sat []] without
   reading Z3's model, for a caller asking satisfiability only. *)
let base_session_check ?(read_model = true) ~id s ~timeout fenv phi =
  if not s.bs_ok then `Unknown
  else
    try
      match base_session_convert ~memo:true ~id s fenv [ phi ] with
      | None -> `Unknown
      | Some exprs ->
          let ctx = s.bs.ctx in
          let solver = s.bs.solver in
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
              | SATISFIABLE when not read_model -> `Sat []
              | SATISFIABLE -> (
                  match z3_solver_get_model solver with
                  | Some model ->
                      `Sat
                        (Common.PhaseTime.with_phase "model" (fun () ->
                             model_of ~query:(`Query (phi :: s.bs_base)) ctx
                               s.bs.dtenv model))
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

   WHAT.  A quantified query the pooled context answers [`Unknown] is asked
   once more in a fresh context; this is on by default ([fresh_retry_scope]
   below can narrow it or turn it off, for measurement).  For measuring what the
   pooled path loses, COAR_Z3_ALWAYS_FRESH=1 in the environment (read once,
   when the process starts) asks every quantified query in a fresh context
   first instead; it is a measurement mode, not for ordinary runs.
   The fresh question is told only the defined functions the formula reaches
   (directly or through other definitions), is put in negation normal form,
   carries the caller's own timeout, and is not asked when [may_not_return]
   says the solver may never return on its shape.  Leaving out a definition
   the formula does not reach does not change what it means, and negation
   normal form is an equivalence, so the fresh query is the same question.

   CONTRACT.  An answer the pooled query DECIDED ([`Sat], [`Unsat]) is
   returned unchanged, and so is a [`Timeout]: the caller's budget has been
   spent, and a second attempt would double it.  Only an [`Unknown] from a
   quantified query is replaced, and only by a decision of the fresh context;
   when that is undecided too, the pooled answer stands.  So the retry changes
   an answer only where the pooled path returned [`Unknown], never an answer
   the pooled path gave.

   The counters are atomic because queries are asked from several domains.

   WHEN TO REMOVE IT.  Whether the retry still earns anything depends on the
   Z3 version.  [fresh_retry_report] says how often the pooled path was
   undecided and how often the fresh context decided it, and a canary test
   checks, per Z3 version, that a pushed context still loses the decision.
   If a Z3 version stops losing it, the retry is dead weight, and this block
   and the measurement mode are to be removed. *)

(* The measurement mode above, read once from the environment. *)
let always_fresh_mode =
  Stdlib.(Sys.getenv_opt "COAR_Z3_ALWAYS_FRESH" = Some "1")

(* Which pooled [`Unknown]s the retry follows, read once from
   [COAR_Z3_FRESH_RETRY]: unset (the default) every one; [off] none, so that a
   run measures what the retry buys; [z3-unknown] only one that Z3 itself
   answered (or raised on), never one the interface made by declining a
   decided Z3 answer it could not certify, nor a refusal made before Z3 was
   asked.  Both settings are for measurement and off by default.  The narrow
   setting is not exact: a fresh context can answer [unsat] where the pooled
   one said [sat] and the interface declined that [sat]. *)
type fresh_retry_scope = Retry_every_unknown | Retry_off | Retry_z3_unknown

let fresh_retry_scope =
  match Sys.getenv "COAR_Z3_FRESH_RETRY" with
  | None | Some "" | Some "on" -> Retry_every_unknown
  | Some "off" -> Retry_off
  | Some "z3-unknown" -> Retry_z3_unknown
  | Some other ->
      failwith
        ("COAR_Z3_FRESH_RETRY: expected on, off or z3-unknown, not " ^ other)

let fresh_retry_declined_skipped = Atomic.make 0

let str_of_fresh_retry_mode () =
  if always_fresh_mode then "AlwaysFresh"
  else
    match fresh_retry_scope with
    | Retry_every_unknown -> "RetryOnUnknown"
    | Retry_off -> "Off"
    | Retry_z3_unknown -> "RetryOnZ3Unknown"

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
     (fresh-sat %d) (fresh-unsat %d) (fresh-undecided %d) (not-followed %d))"
    (str_of_fresh_retry_mode ())
    (Atomic.get fresh_retry_pooled_unknown)
    (Atomic.get fresh_retry_pooled_timeout)
    (Atomic.get fresh_retry_attempted)
    (Atomic.get fresh_retry_refused)
    (Atomic.get fresh_retry_sat)
    (Atomic.get fresh_retry_unsat)
    (Atomic.get fresh_retry_undecided)
    (Atomic.get fresh_retry_declined_skipped)

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
      let previous = Stdlib.Domain.DLS.get fresh_retry_in_progress_key in
      Stdlib.Domain.DLS.set fresh_retry_in_progress_key true;
      Common.Timer.protect
        ~finally:(fun () ->
          Stdlib.Domain.DLS.set fresh_retry_in_progress_key previous)
        (fun () ->
          check_sat_without_retry ~timeout ~fresh_solver:true ?fun_values_out
            ~id fenv
            (List.map phis ~f:Formula.nnf_of))
    in
    (match ret with
    | `Sat _ -> Atomic.incr fresh_retry_sat
    | `Unsat -> Atomic.incr fresh_retry_unsat
    | _ -> Atomic.incr fresh_retry_undecided);
    Some ret)

(* Keep the comparison's model-dependent outputs separate until its result
   is selected. Diagnostics of a decided/expired primary are observations,
   not policy retries, and must not replace the primary's outputs. The
   callbacks keep this result/output association testable without depending
   on a particular Z3 identifier draw returning Unknown. *)
let check_sat_diagnostic_comparison ?fun_values_out ~primary ~comparison
    ~record () =
  let ret = primary fun_values_out in
  let alt_values = ref [] in
  let is_retry = match ret with `Unknown _ -> true | _ -> false in
  let alt = comparison ~is_retry alt_values in
  record ret alt;
  match (ret, alt) with
  | `Unknown _, Some ((`Sat _ | `Unsat) as decided) ->
      Option.iter fun_values_out ~f:(fun out -> out := !alt_values);
      decided
  | _ -> ret

(* [always_fresh] is the measurement mode ([always_fresh_mode] unless a
   test asks for it explicitly). *)
let check_sat_policy ?(timeout = None) ?(fresh_solver = false)
    ?(always_fresh = always_fresh_mode) ?fun_values_out ~id fenv phis =
  let quantified () =
    List.exists phis ~f:(fun phi ->
        Formula.number_of_quantifiers (FunEnv.defined_formula_of fenv phi) > 0)
  in
  if fresh_solver then
    check_sat_without_retry ?fun_values_out ~timeout ~fresh_solver ~id fenv phis
  else if always_fresh then (
    if quantified () then (
      match check_sat_fresh ?fun_values_out ~timeout ~id fenv phis with
      | Some ret -> ret
      | None -> check_sat_without_retry ?fun_values_out ~timeout ~id fenv phis)
    else check_sat_without_retry ?fun_values_out ~timeout ~id fenv phis)
  else if Option.is_some z3_alt_log_path && quantified () then (
      (* the diagnostic of [z3_alt_log_path]: the pooled answer is returned
         as the policy would return it, and the same question is asked once
         more in a context of its own for the log *)
      let pooled_s = ref 0. in
      let alt_start = ref 0. in
      let result = check_sat_diagnostic_comparison ?fun_values_out
        ~primary:(fun out ->
          let t0 = Common.Clock.now_s () in
          let ret =
            check_sat_without_retry ?fun_values_out:out ~timeout ~id fenv phis
          in
          pooled_s := Common.Clock.now_s () -. t0;
          (match ret with
          | `Unknown _ -> Atomic.incr fresh_retry_pooled_unknown
          | `Timeout -> Atomic.incr fresh_retry_pooled_timeout
          | _ -> ());
          ret)
        ~comparison:(fun ~is_retry out ->
          alt_start := Common.Clock.now_s ();
          if is_retry then check_sat_fresh ~fun_values_out:out ~timeout ~id fenv phis
          else if List.exists phis ~f:may_not_return then None
          else
            Some
              (check_sat_without_retry ~fun_values_out:out ~timeout
                 ~fresh_solver:true ~id fenv (List.map phis ~f:Formula.nnf_of)))
        ~record:(fun ret alt ->
          let str = function
            | `Sat _ -> "sat"
            | `Unsat -> "unsat"
            | `Unknown _ -> "unknown"
            | `Timeout -> "timeout"
          in
          z3_alt_log
            (sprintf "fresh\t%s\t%.3f\t%s\t%.3f\t%d\t%d\n"
               (str ret) !pooled_s
               (match alt with Some a -> str a | None -> "refused")
               (Common.Clock.now_s () -. !alt_start)
               (Map.Poly.length fenv)
               (Map.Poly.length
                  (fenv_reached_by fenv
                     (Formula.and_of
                        (List.map phis ~f:(FunEnv.defined_formula_of fenv)))))))
        ()
      in
      (match result with
      | `Sat model -> `Sat model
      | `Unsat -> `Unsat
      | `Unknown reason -> `Unknown reason
      | `Timeout -> `Timeout))
  else (
      Stdlib.Domain.DLS.set z3_said_unknown_key false;
      Stdlib.Domain.DLS.set declined_key false;
      match check_sat_without_retry ?fun_values_out ~timeout ~id fenv phis with
      | `Unknown _ as ret when quantified () -> (
          Atomic.incr fresh_retry_pooled_unknown;
          let follow =
            match fresh_retry_scope with
            | Retry_every_unknown -> true
            | Retry_off -> false
            | Retry_z3_unknown ->
                Stdlib.Domain.DLS.get z3_said_unknown_key
                && not (Stdlib.Domain.DLS.get declined_key)
          in
          if not follow then (
            Atomic.incr fresh_retry_declined_skipped;
            ret)
          else
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
  (* under the byte rule ([new_context_full_major_bytes]) or the Z3 memory
     rule ([new_context_full_major_z3_mb]) the context's collection is
     decided by growth, so no thinning by count here *)
  if
    every <= 1
    || Option.is_some (Atomic.get new_context_full_major_bytes)
    || Option.is_some (Atomic.get new_context_full_major_z3_mb)
  then mk ()
  else
    let k = Atomic.fetch_and_add seq_axiom_contexts 1 in
    if k % every = 0 then
      (* this context's collection is forced here (an override of 1), not
         left to the process-wide count rule: under that rule it is made only
         when the process-wide context count is also a multiple of that
         rule's n, and the two counts advance together while the fallback
         makes every new context, so with an offset between them that is not
         a multiple of n no collection is made at all -- on one input 80
         fallback contexts in a row went uncollected and the resident set
         grew from 1.4 to 4.9 GB, of which a later collection returned little
         to the system.  An enclosing override of [Int.max_value] (a forked
         copy that lives for one question) still means no collection *)
      match Stdlib.Domain.DLS.get full_major_every_override with
      | Some n when n = Int.max_value -> mk ()
      | _ -> with_new_context_full_major_every 1 mk
    else
      (* [Int.max_value]: no collection for this context *)
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
   default; the runner is this domain's [with_seq_axiom_fork_runner] one when
   set, else the process-wide one) it is [ask ()], whose wall time Z3's
   [timeout] and [rlimit] are meant to bound and do not always bound.  With a
   runner set, [ask] runs in a forked copy
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
   context and the conversion, which the Z3 timeout does not cover, and for a
   check in which Z3 reads neither its timeout nor its resource limit.  So,
   with a runner set and a copy made, the call returns within
   [seq_axiom_fork_kill_ms timeout] milliseconds plus the fork and the reap,
   whatever the question: the only wall-clock bound on it that holds. *)
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
  (* no collection in this copy, which lives for one question: the override
     below skips every one (marking a context made keeps the counter's
     first-context case out of it too) *)
  if Atomic.get new_contexts = 0 then Atomic.incr new_contexts;
  Gc.set { (Gc.get ()) with space_overhead = 100_000 };
  with_new_context_full_major_every Int.max_value ask

(* A per-domain runner for the questions asked while [with_seq_axiom_fork_runner]
   runs, in place of the process-wide one: [Some r] asks them through [r]
   whatever the process-wide setting, [None] (the default) leaves the
   process-wide setting in force.  Restored on return and on raise.

   Why a caller wants it: asked in this process, a fallback question is bounded
   only by Z3's own [timeout] and [rlimit] parameters, and Z3 does not always
   read them: on a Rust-derived loop step one fallback check of a 61,176-node
   question given a 500 ms budget ran 52 s.  A solver call is not
   interruptible from OCaml (an alarm is handled only at a safe point), so a
   killed process is the only bound that holds.  Scoping the runner lets one
   caller ask its fallbacks in killed copies without the process-wide
   setting, which also moves every other fallback of the run and raises the
   peak resident size on large heaps. *)
let seq_axiom_fork_runner_here : seq_axiom_fork_runner option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_seq_axiom_fork_runner runner f =
  match runner with
  | None -> f ()
  | Some _ ->
      let saved = Stdlib.Domain.DLS.get seq_axiom_fork_runner_here in
      Stdlib.Domain.DLS.set seq_axiom_fork_runner_here runner;
      Exn.protect ~f ~finally:(fun () ->
          Stdlib.Domain.DLS.set seq_axiom_fork_runner_here saved)

(* the runner [ask_seq_axiom_question] uses now: this domain's, else the
   process-wide one *)
let current_seq_axiom_fork_runner () =
  match Stdlib.Domain.DLS.get seq_axiom_fork_runner_here with
  | Some r -> Some r
  | None -> Atomic.get seq_axiom_fork_runner

let ask_seq_axiom_question ~timeout ask =
  match current_seq_axiom_fork_runner () with
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
    match
      SeqAxiomEncoding.encode
        ~context:(Map.Poly.fold reached ~init:[]
          ~f:(fun ~key:name ~data:(params, result, body, _, property) context ->
            let args = List.map params ~f:(fun (v, sort) -> Term.mk_var v sort) in
            let call = Term.mk_fvar_app name (List.map params ~f:snd) result args in
            Formula.eq call body :: property :: context))
        ~sorts:(List.map (Map.Poly.data (get_dtenv ())) ~f:(fun dt -> T_dt.SDT dt))
        phi
    with
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
            (* the parts of the conversion, each a phase row of its own *)
            let part name f = Common.PhaseTime.with_phase name f in
            let local =
              part "dtenv-collect" @@ fun () ->
              List.fold copies ~init:(DTEnv.of_formula neg) ~f:(fun env c ->
                  Map.Poly.set env ~key:(Datatype.instance_key c) ~data:c)
            in
            let plain =
              Map.Poly.filter (get_dtenv ()) ~f:(fun dt ->
                  not (SeqAxiomEncoding.mentions_seq_sort (T_dt.SDT dt)))
            in
            let dtenv =
              part "dtenv-declare" @@ fun () ->
              z3_dtenv_of_dtenv ~init:instance.dtenv ctx
                (Map.Poly.merge_skewed plain local ~combine:(fun ~key:_ _ c ->
                     c))
            in
            if !reusable then instance.dtenv <- dtenv;
            let z3fenv = z3_fenv_of ~id ctx [] [] reached dtenv in
            let goal =
              part "goal" @@ fun () ->
              ConvertCensus.timed "seqax" neg (fun () ->
                  of_formula_with_z3fenv ~id ctx [] [] z3fenv dtenv neg)
            in
            let axioms =
              part "axioms" @@ fun () ->
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
            part "add" (fun () -> Z3.Solver.add solver (axioms @ [ goal ]));
            stage "ask";
            if dump_z3_queries then
              prerr_endline
                ("=== Z3 query (sequence axioms) ===\n"
               ^ dump_text solver);
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
                  let t0 = Common.Clock.now_s () in
                  fun outcome ->
                    let after = rlimit_count_of solver in
                    rlimit_log_line
                      (sprintf "CHECK\t%d\t%s:seqax\t%s\t%.3f\t%s\t%d\t%d\t%b\ttrue"
                         (Core_unix.getpid () |> Pid.to_int)
                         label
                         (match (before, after) with
                         | Some b, Some a -> sprintf "%.0f" (a -. b)
                         | _ -> "na")
                         (Common.Clock.now_s () -. t0)
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
          | `Asked Z3.Solver.UNSATISFIABLE ->
              (* [neg] and the axioms are sequence-free: [encode] declines
                 a copy in which a sequence survives, and a reached function
                 over sequences is declined above *)
              (match certify_shared_native_result ~asked_sequence_free:true
                 ~id fenv [Formula.negate phi] `Unsat with
               | `Unsat -> SeqAxProved
               | `Unknown reason -> SeqAxNotProved reason
               | _ -> SeqAxNotProved "native recursive refutation is uncertified")
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

(* [without_split_int_binders f]: [f ()] with the split off in this domain
   whatever is in force around it, the enclosing state restored afterwards
   (on an exception too).  Every question [f] asks through [check_valid],
   [check_valid_seq_as_array] or the sequence-axiom fallback is then asked as
   given. *)
let without_split_int_binders f =
  let saved = Stdlib.Domain.DLS.get split_int_binders_key in
  Stdlib.Domain.DLS.set split_int_binders_key false;
  Exn.protect ~f ~finally:(fun () ->
      Stdlib.Domain.DLS.set split_int_binders_key saved)

(* whether [split_int_binders_here phi] would ask something other than [phi]:
   the split is in force in this domain and makes at least one split of
   [phi].  Counts nothing in the ladder's tally. *)
let split_int_binders_would_change phi =
  Stdlib.Domain.DLS.get split_int_binders_key
  && snd (IntBinderSplit.rewrite_counted phi) > 0

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
  with_model_unread @@ fun () ->
  match check_sat ?timeout ~id fenv [ phi ] with `Sat _ -> true | _ -> false

(* [?ask_native]: how the negation's own check is asked, given that check as
   a function of its Z3 budget; by default it is called with [timeout].  A
   caller passes one ([check_valid_asking]) to ask it elsewhere (a killed
   copy) while the sequence-axiom fallback below still reads its answer in
   this process, under the caller's budget, as for an in-process check. *)
let check_valid_core ?timeout ?fresh_solver ?ask_native ~id fenv phi =
  (* a [with_model_unread] of the caller covers the main question only *)
  let unread = Stdlib.Domain.DLS.get model_unread_key in
  with_dls model_unread_key false @@ fun () ->
  let phi = split_int_binders_here phi in
  let native ~timeout =
    Common.PhaseTime.with_phase "check-sat" (fun () ->
        with_dls model_unread_key unread (fun () ->
            check_sat ~timeout ?fresh_solver ~id fenv [ Formula.negate phi ]))
  in
  with_seq_axiom_fallback_split ~caller_timeout:(Option.join timeout) ~id fenv
    phi
  @@
  match
    match ask_native with
    | None -> native ~timeout:(Option.join timeout)
    | Some ask -> ask native
  with
  | `Unsat -> `Valid
  | `Sat model -> `Invalid model
  | res -> res

let check_valid ?timeout ?fresh_solver ~id fenv phi =
  check_valid_core ?timeout ?fresh_solver ~id fenv phi

let check_valid_asking ~ask_native ?timeout ?fresh_solver ~id fenv phi =
  check_valid_core ?timeout ?fresh_solver ~ask_native ~id fenv phi

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

(* [words_interface]: [check_valid_by_words] first asks the question's
   separated words form ([int_to_bv_interface_subst]); process-wide once on. *)
let words_interface = Atomic.make false
let set_words_interface b = Atomic.set words_interface b

(* [int_to_bv_interface_subst phis]: [phis] with every [int_to_bv m t] whose
   argument no key translates forgotten into a fresh word, as the words
   question does, but without first replacing bounded integer variables by
   [ubv_to_int] of a word or splitting them into a quotient and a word, and
   with [word_interface_lemmas] added; [None] when there is no word to forget.
   The guarded binder-independent, fresh-word result is weaker than [phis]
   (forgetting adds models, and every lemma
   holds in each model of [phis] with the words given back), so only its
   [unsat] may be read, as [phis]'s.  Why without those replacements: they
   leave [x = 2^64 q + ubv_to_int xb] links between the integer and the
   bit-vector worlds, and on a bit-mask obligation the question with them ran
   2-29 s across seeds where the question with the worlds separated and only
   the lemmas between them ran under a second under every seed. *)
let int_to_bv_interface_subst phis =
  match int_to_bv_twins_subst ~generalize:true ~interface:true phis with
  | _, [] -> None
  | phis, fresh ->
      Some (phis, List.map fresh ~f:(fun kb -> (kb, kb, 0, None)))

let check_valid_by_words ?(timeout = None) ~id fenv phi =
  let by_interface () =
    if not (Atomic.get words_interface) then false
    else
      match int_to_bv_interface_subst [ Formula.negate phi ] with
      | None -> false
      | Some pre -> (
          let pre =
            if Atomic.get words_seq_as_arrays then
              let phis, picked = pre in
              (seq_reads_as_arrays phis, picked)
            else pre
          in
          let original = [ Formula.negate phi ] in
          let ask () =
            match
              check_sat_base ~timeout ~fresh_solver:true ~pre ~id fenv original
            with
            | `Unsat as ret -> certify_shared_native_result ~id fenv original ret
            | ret -> ret
          in
          let started = Common.Clock.now_float () in
          let proved =
            match
              match Sys.getenv "COAR_DUMP_WORDS" with
              | None -> ask ()
              | Some dir ->
                  with_query_dump
                    (sprintf "%s/i%d-%d" dir
                       (Atomic.fetch_and_add words_dump_count 1)
                       (Common.ForkGuard.self_pid ()))
                    ask
            with
            | `Unsat -> true
            | _ -> false
          in
          (* counted with the phase-time report on, so a run says whether the
             separated form was asked and what it bought; no answer changes *)
          if !Common.PhaseTime.on then
            Common.PhaseTime.add
              ("words-interface/" ^ if proved then "proved" else "unproved")
              (Time_float.Span.to_sec
                 (Time_float.diff (Common.Clock.now_float ()) started));
          proved)
  in
  if by_interface () then `Valid
  else
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
        let original = [ Formula.negate phi ] in
        match check_sat_base ~timeout ~fresh_solver:true ~pre ~id fenv original with
        | `Unsat as ret ->
            (* The words relaxation preserves refutations, but does not certify
               the native recursive kernel used to obtain one. Inspect the
               original vocabulary and complete definitions before accepting
               it; reachability slicing or word rewriting can hide a lambda.
               Positive native answers are ignored by this helper. *)
            certify_shared_native_result ~id fenv original ret
        | ret -> ret
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

(* [decide_valid ?timeout ~id fenv phi]: [`Valid] or [`Invalid] when Z3
   decides [phi]'s validity, [`Undecided reason] otherwise -- the question
   [is_valid] asks, with the undecided case kept apart from [`Invalid].  No
   model is read. *)
let decide_valid ?timeout ~id fenv phi =
  let saved = Stdlib.Domain.DLS.get only_validity_read_key in
  Stdlib.Domain.DLS.set only_validity_read_key true;
  Exn.protect
    ~finally:(fun () -> Stdlib.Domain.DLS.set only_validity_read_key saved)
    ~f:(fun () ->
      with_model_unread @@ fun () ->
      match check_valid ?timeout ~id fenv phi with
      | `Valid -> `Valid
      | `Invalid _ -> `Invalid
      | `Timeout -> `Undecided "timeout"
      | `Unknown reason -> `Undecided reason
      | `Sat _ | `Unsat -> `Undecided "not a validity answer")

let is_valid ?timeout ~id fenv phi =
  Debug.print @@ lazy "[Z3interface.is_valid]";
  match decide_valid ?timeout ~id fenv phi with `Valid -> true | _ -> false

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
        Formula.nnf_of @@ ArrayLiteralEq.expand_finite_array_eqs phi)
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
  let original = phis in
  let solver, phis = elimination_solver ~timeout ~id fenv phis in
  Option.iter smtlib2_out ~f:(fun out -> out := elimination_text solver);
  if List.exists phis ~f:may_not_return then `Refused
  else
    match z3_check solver [] with
    | UNSATISFIABLE ->
        (match certify_shared_native_result ~id fenv original `Unsat with
         | `Unsat -> `Unsat
         | `Unknown reason -> `Unknown reason
         | _ -> `Unknown "native recursive refutation is uncertified")
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
  | Some (prefix, _, _) ->
      let data =
        try
          Common.SmtlibRecursive.standard_text
            (elimination_query_text ~id fenv [ Formula.negate phi ])
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
        (* [COAR_VALID_DUMP_ALL_NATIVE] set: every question's native form
           is kept, whatever its outcome and whatever [native] says; a
           diagnostic for replaying decided questions too *)
        if
          (native && String.equal (outcome r) "undecided")
          || Option.is_some (Sys.getenv "COAR_VALID_DUMP_ALL_NATIVE")
        then dump_native_question ~id fenv phi;
        (r, secs)
      in
      Out_channel.with_file (dir ^ "/index.tsv") ~append:true ~f:(fun oc ->
          Out_channel.output_string oc
            (sprintf "%s\t%s\t%.3f\t%d\t%d\n" name (outcome r) secs timeout
               (String.length (Formula.str_of phi))));
      r

(* ------------------------------------------------------------------
   A sequence query asked as arrays plus a length.

   [seq.store] is expanded at this boundary into extraction and concatenation
   (the [SqStore] arm of [of_term]), because SMT-LIB sequences have no write,
   and Z3 (4.15.2) decides nothing about [seq.nth] over that expansion: the
   frame fact of a write times out at 20 s where cvc5 answers in 0.2 s.
   [Ast.SeqAsArray.translate] rewrites a formula whose sequence terms are
   variables, reads, lengths, writes, [seq.empty], [seq.unit], [ite] and
   [seq.++], and
   whose every read is range-guarded, into an EQUISATISFIABLE formula over an
   array and a length per sequence; its header states the fragment and the
   argument.  These entry points ask that translation first.

   CONTRACT.  The answer is the one the untranslated query would have if Z3
   decided it:
   - [`Unsat] of the translation is [`Unsat] of the input (equisatisfiable);
   - [`Sat] of the translation is returned with its model read back onto the
     input's sequence variables (each the word a_s[0..n_s-1], a sequence
     longer than [Ast.SeqAsArray.max_read_back_length] left out of the model)
     and the translation's own names removed; if the model cannot be read back
     otherwise, the untranslated query is asked instead;
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
  if not (List.exists phis ~f:Ast.SeqAsArray.mentions_seq) then untranslated ()
  else
  (* The translation's range-guard questions are asked in one solver of its
     own: each distinct hypothesis is converted and asserted once, as
     [label => h] with a fresh Boolean [label], and a question asserts the
     guard's negation in a scope and is checked under its hypotheses' labels
     as assumptions.  An unasserted label is free, so its implication
     constrains nothing, and [unsat] means exactly that the hypotheses
     entail the guard; [sat] that they do not.  [None] -- a hypothesis or
     guard the session cannot convert (a defined function it reaches, the
     bit-vector range rewrite), an [unknown], a timeout or any error -- asks
     the question as before.  A hypothesis is recognised by the number the
     translation gave its simplified printed form, without reading it
     again: hypotheses printed alike get one label, which is the
     identification the translation's memo of answered questions already
     makes (equal texts, equal questions), so the questions decided are
     the ones a label per hypothesis object decided.  Why:
     the guards of one translation share their hypotheses, the sibling
     literals of the context, and a clause of 66,000 nodes holding
     concatenations gave 1,200 reads some 200 hypotheses of 11,000 nodes
     each; asked one by one, the same literals were converted and asserted
     2,000 times, 40 s before anything was asked.  Not shared: the session
     belongs to this call. *)
  let guard_session = lazy (base_session_create ~id ()) in
  (* each hypothesis's label, at the number of its printed form: the numbers
     are dense from 0, and a question looks up some 200 of them *)
  let guard_labels : Z3.Expr.expr option array ref = ref [||] in
  let label_at n =
    if n < Array.length !guard_labels then !guard_labels.(n) else None
  in
  let set_label_at n label =
    let len = Array.length !guard_labels in
    if n >= len then (
      let grown = Array.create ~len:(Int.max (n + 1) (2 * len)) None in
      Array.blito ~src:!guard_labels ~dst:grown ();
      guard_labels := grown);
    !guard_labels.(n) <- Some label
  in
  let guard_session_ok = ref true in
  let session_entails hyps goal =
    let fenv' = without_unreached_explicit fenv (goal :: List.map hyps ~f:snd) in
    if (not !guard_session_ok) || not (Map.Poly.is_empty fenv') then None
    else
      Common.PhaseTime.with_phase "seq-as-array-guard" @@ fun () ->
      try
        let s = Lazy.force guard_session in
        let ctx = s.bs.ctx and solver = s.bs.solver in
        let label_of (n, h) =
          match label_at n with
          | Some label -> Some label
          | None -> (
              match base_session_convert ~id s fenv' [ h ] with
              | Some [ e ] ->
                  let label =
                    Z3.Expr.mk_fresh_const ctx "seq_as_array_hyp"
                      (Z3.Boolean.mk_sort ctx)
                  in
                  z3_solver_add solver [ Z3.Boolean.mk_implies ctx label e ];
                  set_label_at n label;
                  Some label
              | _ -> None)
        in
        match
          ( Option.all (List.map hyps ~f:label_of),
            base_session_convert ~id s fenv' [ Formula.mk_neg goal ] )
        with
        | Some labels, Some negated ->
            let set_timeout ms =
              let params = Z3.Params.mk_params ctx in
              Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") ms;
              Z3.Solver.set_parameters solver params
            in
            Z3.Solver.push solver;
            Common.Timer.protect
              ~finally:(fun () ->
                set_timeout 0;
                try Z3.Solver.pop solver 1
                with exn when not (Common.Timer.is_async exn) ->
                  (* a scope that cannot be closed leaves a negated guard
                     asserted: the session is not used again *)
                  guard_session_ok := false)
            @@ fun () ->
            set_timeout 1000;
            z3_solver_add solver negated;
            (match z3_check solver labels with
            | Z3.Solver.UNSATISFIABLE -> Some true
            | Z3.Solver.SATISFIABLE -> Some false
            | Z3.Solver.UNKNOWN -> None)
        | _ -> None
      with exn when not (Common.Timer.is_async exn) ->
        guard_session_ok := false;
        None
  in
  let entails hyps goal =
    match session_entails hyps goal with
    | Some entailed -> entailed
    | None -> (
        match
          check_sat ~timeout:(Some 1000) ~id fenv
            [ Formula.and_of (Formula.mk_neg goal :: List.map hyps ~f:snd) ]
        with
        | `Unsat -> true
        | _ -> false)
  in
  let reserved =
    Map.Poly.fold fenv ~init:Set.Poly.empty
      ~f:(fun ~key ~data:(params, _, body, _, property) names ->
        Set.Poly.union_list
          [ Set.add names key; Set.Poly.of_list (List.map params ~f:fst);
            Formula.names_spelled_in (Formula.eq body body);
            Formula.names_spelled_in property ])
  in
  match Ast.SeqAsArray.translate ~entails ~reserved (Formula.and_of phis) with
  | Error reason ->
      if not (String.equal reason "no sequence") then (
        Atomic.incr seq_as_array_outside;
        Debug.print
        @@ lazy (sprintf "[z3:seq-as-array] asked untranslated: %s" reason));
      untranslated ()
  | Ok tr -> (
      Atomic.incr seq_as_array_translated;
      (* answer-neutral: a phase report tells a run in which the translation
         was asked from one in which no question was in its fragment *)
      Common.PhaseTime.event "seq-as-array-translated";
      let read_seqs model =
        let changes_context =
          List.exists tr.bindings ~f:(fun binding ->
              Set.mem reserved binding.Ast.SeqAsArray.seq_var)
        in
        if changes_context then None else Ast.SeqAsArray.read_back tr model
      in
      let array_form () =
        let asked =
          if fresh_solver then Formula.nnf_of tr.formula else tr.formula
        in
        match check_sat ~timeout ~fresh_solver ~id fenv [ asked ] with
        | `Unsat ->
            Atomic.incr seq_as_array_decided;
            `Unsat
        | `Sat model -> (
            match read_seqs model with
            | Some model ->
                Atomic.incr seq_as_array_decided;
                `Sat model
            | None -> untranslated ())
        | _ -> untranslated ()
      in
      (* A translation that holds a concatenation is asked with its arrays as
         uninterpreted functions ([Ast.ArrayAsFun], equisatisfiable) and its
         integer binders split at the concatenation's boundaries
         ([IntBinderSplit], an equivalence), in place of the array form, when
         it is in that fragment.  Why: such a question was outside the
         translation until concatenation was admitted, and its typical
         premise defines a sequence elementwise over its whole range
         ([forall t. 0 <= t < len s => s[t] = start + t], an iterator's
         produced sequence); Z3 4.12.0 and cvc5 1.4.2 leave
         [exists A. forall t. 0 <= t < L => A[t] = t + b /\ L > 100]
         undecided for an array [A] (timeout and unknown at 10 s), and Z3
         answers it at once for a function [A]; inside a read of the
         concatenation, [ite(t < L, A[t], ..)], it does so only once the
         binder is split at [L].  So the newly admitted questions get one
         translated question, as the concat-free ones do, and a concat-free
         translation is asked exactly as before. *)
      if not tr.Ast.SeqAsArray.concat then array_form ()
      else
        match Ast.ArrayAsFun.translate tr.formula with
        | Error _ -> array_form ()
        | Ok ftr -> (
            Common.PhaseTime.event "seq-as-array-functions";
            let split = IntBinderSplit.rewrite ftr.formula in
            let asked = if fresh_solver then Formula.nnf_of split else split in
            let fun_values = ref [] in
            match
              check_sat_policy ~timeout ~fresh_solver
                ~fun_values_out:fun_values ~id fenv [ asked ]
            with
            | `Unsat ->
                Atomic.incr seq_as_array_decided;
                `Unsat
            | `Sat model -> (
                match
                  Option.bind
                    (Ast.ArrayAsFun.read_back ftr model !fun_values)
                    ~f:read_seqs
                with
                | Some model ->
                    Atomic.incr seq_as_array_decided;
                    `Sat model
                | None -> untranslated ())
            | _ -> untranslated ()))

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
     cost the budget twice.  The untranslated question is asked by
     [untranslated] when the caller passes one (its own in-process route, so
     that the caller's switches about how a question is asked still hold for
     every question this function does not decide itself), by [check_sat]
     otherwise.
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
    ?untranslated ~id fenv phis =
  let untranslated () =
    match untranslated with
    | Some ask -> ask ()
    | None -> check_sat ~timeout ~fresh_solver ~id fenv phis
  in
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

(* Tracking literals occupy Z3's integer-symbol namespace. Source converters
   use string symbols, including numeric-looking names. Native API callers must
   reserve integer symbols for this state. Keep one state per solver, retain it
   through pushes/pops and retries, and replace it when renewing the solver. *)
type core_tracking_state = {
  mutable next_tracking_id : int;
  tracking_names : (int, string) Hashtbl.Poly.t;
}

let create_core_tracking_state () =
  { next_tracking_id = 0; tracking_names = Hashtbl.Poly.create () }

let new_core_tracking_literal state ctx name =
  (* Z3 integer symbols are nonnegative 30-bit values. Refuse exhaustion before
     incrementing or touching the solver; wrapping would reuse another label. *)
  if state.next_tracking_id > 0x3fffffff then
    failwith "[z3] unsat-core tracking identifier space exhausted";
  let id = state.next_tracking_id in
  state.next_tracking_id <- id + 1;
  Hashtbl.set state.tracking_names ~key:id ~data:name;
  Z3.Boolean.mk_const ctx (Z3.Symbol.mk_int ctx id)

let original_core_tracking_names state literals =
  let names = List.map literals ~f:(fun literal ->
    let symbol = Z3.FuncDecl.get_name (Z3.Expr.get_func_decl literal) in
    if Z3.Symbol.is_int_symbol symbol then
      Hashtbl.find state.tracking_names (Z3.Symbol.get_int symbol)
    else None) in
  if List.exists names ~f:Option.is_none then None
  else Some (List.dedup_and_sort ~compare:String.compare (List.filter_opt names))

let incr_check_sat_unsat_core ~tracking_state ~id ?(enable = true) ?(z3str3 = false)
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
               "cannot synthesise quantifier prefixes of %d different lengths (%s) in one query: the preamble defines a single QSAT"
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
            tracked := (decl, new_core_tracking_literal tracking_state ctx label) :: !tracked
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
            let label = new_core_tracking_literal tracking_state ctx label in
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
    let with_non_tracked f =
      if Set.is_empty non_tracked then f ()
      else (
        Z3.Solver.push solver;
        (* Only this call's temporary constraints belong to the scope. Close
           it even when conversion, checking, diagnostics or model decoding
           raises, retaining the caller's accumulated tracked constraints. *)
        Common.Timer.protect ~finally:(fun () -> Z3.Solver.pop solver 1) (fun () ->
            Z3.Solver.add solver @@ Set.to_list
            @@ Set.Poly.map non_tracked
                 ~f:(of_formula_with_z3fenv ~id ctx [] [] fenv dtenv);
            f ()))
    in
    with_non_tracked @@ fun () ->
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
            (model_of
               ~query:
                 (`Query
                   (Map.Poly.data labeled_constr_map @ Set.to_list non_tracked))
               ctx dtenv model)
      | Ok (`Checked Z3.Solver.SATISFIABLE) -> (
          match z3_solver_get_model (asked_solver ()) with
          | Some model ->
              (* as in [check_sat]: a pooled solver's model can carry a name
                 this query never asked about, and a consumer that turns the
                 model into a substitution is keyed by name *)
              `Sat
                (model_of
                   ~query:
                     (`Query
                       (Map.Poly.data labeled_constr_map
                       @ Set.to_list non_tracked))
                   ctx dtenv model)
          | None -> `Unknown "model generation is not enabled?")
      | Ok (`Checked UNSATISFIABLE) ->
          if enable then (
            match original_core_tracking_names tracking_state
              (z3_solver_get_unsat_core (asked_solver ())) with
            | None -> `Unknown "unsat core contains an unregistered tracking literal"
            | Some unsat_keys ->
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
  let original_fenv = fenv in
  let original = Map.Poly.data pvar_clause_map in
  let full_equations = supports_defining_equations fenv in
  let equations = if full_equations then defining_equations_of fenv else [] in
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
    z3_dtenv_of_formula ctx @@ Formula.and_of (equations @ original)
  in
  let solver = Z3.Solver.mk_solver ctx None in
  let fenv =
    if full_equations then
      Map.Poly.mapi fenv ~f:(fun ~key:var ~data:(params, sret, _, _, _) ->
        Z3.FuncDecl.mk_func_decl_s ctx (Ident.name_of_tvar var)
          (List.map params ~f:(snd >> of_sort ctx dtenv))
          (of_sort ctx dtenv sret))
    else z3_fenv_of ~id ctx [] [] (fenv_for_query fenv original) dtenv
  in
  (match timeout with
  | None -> ()
  | Some timeout ->
      let params = Z3.Params.mk_params ctx in
      Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout;
      Z3.Solver.set_parameters solver params);
  (* Equations constrain the background; only input clauses receive labels. *)
  z3_solver_add solver
    (List.map equations ~f:(of_formula_with_z3fenv ~id ctx [] [] fenv dtenv));
  match incr_check_sat_unsat_core
    ~tracking_state:(create_core_tracking_state ()) ~id ~z3str3 ~timeout solver ctx fenv dtenv
    pvar_clause_map with
  | `Unsat core when full_equations -> `Unsat core
  | `Unsat core ->
      (match certify_shared_native_result ~id original_fenv original `Unsat with
       | `Unsat -> `Unsat core
       | `Unknown reason -> `Unknown reason
       | _ -> `Unknown "native recursive refutation is uncertified")
  | `Sat _ when not full_equations && not (Map.Poly.is_empty original_fenv) ->
      `Unknown "known-function context has no verified shared model certificate"
  | ret -> ret

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
      (* [max_smt] makes this context for the one question *)
      Some (num_sat, model_of ~query:`Fresh_context ctx dtenv model)
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
  let full_equations = supports_defining_equations fenv in
  if not (Map.Poly.is_empty fenv) && not full_equations then Set.Poly.empty else
  let equations = if full_equations then defining_equations_of fenv else [] in
  let cfg = [ ("unsat_core", "true") ] in
  let instance = get_instance id cfg (Hashtbl.Poly.create ()) in
  let ctx = instance.ctx in
  instance.dtenv <-
    z3_dtenv_of_formula ~init:instance.dtenv ctx @@ Formula.and_of (equations @ phis);
  instance.fenv <-
    Map.Poly.mapi fenv ~f:(fun ~key:var ~data:(params, sret, _, _, _) ->
      Z3.FuncDecl.mk_func_decl_s ctx (Ident.name_of_tvar var)
        (List.map params ~f:(snd >> of_sort ctx instance.dtenv))
        (of_sort ctx instance.dtenv sret));
  let dtenv = instance.dtenv in
  let fenv = instance.fenv in
  let solver = instance.solver in
  let hard = List.map equations ~f:(of_formula_with_z3fenv ~id ctx [] [] fenv dtenv) in
  let tracking_state = create_core_tracking_state () in
  let name_map0 =
    List.map phis ~f:(of_formula_with_z3fenv ~id ctx [] [] fenv dtenv)
    |> List.foldi ~init:Map.Poly.empty ~f:(fun i map phi ->
        let name = "#S_" ^ string_of_int i in
        let label = new_core_tracking_literal tracking_state ctx name in
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
      z3_solver_add solver hard;
      Map.Poly.iteri name_map ~f:(fun ~key ~data ->
          z3_solver_assert_and_track solver data key);
      match z3_check solver [] with
      | Z3.Solver.SATISFIABLE -> (
          match z3_solver_get_model solver with
          | None -> models
          | Some model ->
              let models' =
                Set.add models
                  (model_of ~query:(`Query phis) ctx dtenv model)
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
  (* Private context: never publish its declarations or tracked assertions. *)
  let finally () = z3_solver_reset solver in
  match inner num_ex Set.Poly.empty Set.Poly.empty name_map0 with
  | ret ->
      finally ();
      ret
  | exception e ->
      finally ();
      raise e

let check_opt_z3 ?(timeout = None) ~max ctx dtenv phis obj =
  let optimizer = Z3.Optimize.mk_opt ctx in
  Option.iter timeout ~f:(fun ms ->
      let params = Z3.Params.mk_params ctx in
      Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") ms;
      Z3.Optimize.set_parameters optimizer params);
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
      (* [check_opt] makes this context for the one question *)
      Some (lower, upper, model_of ~query:`Fresh_context ctx dtenv model)
  | _ -> None

(* [check_opt ?timeout ~id fenv phis ~max obj]: [Some (lower, upper, model)]
   with [model] a model of [phis] that Z3's optimiser reports optimal for [obj]
   (maximal when [max], minimal otherwise), and [None] when it reports none --
   [phis] unsatisfiable, the objective unbounded with no model returned, a
   known-function context it cannot state, or the question left undecided
   within [timeout] ms.  So [None] is not a verdict about [phis]: a caller
   that must tell an unsatisfiable [phis] from an undecided one asks
   [check_sat].

   With no [timeout] the optimiser is bounded by what is left of an armed
   [Common.Timer] budget ([armed_budget_ms]), and by nothing when none is
   armed: Z3's optimiser takes no budget of its own, and one check on a
   four-unknown integer system was seen not to return within 600 s. *)
let check_opt ?(timeout = None) ~id fenv phis ~max obj =
  let timeout = timeout_or_armed_budget timeout in
  let full_equations = supports_defining_equations fenv in
  if not (Map.Poly.is_empty fenv) && not full_equations then None else
  let phis = if full_equations then defining_equations_of fenv @ phis else phis in
  let ctx =
    let cfg =
      let cfg = [ ("model", "true") ] in
      if validate then cfg @ validate_cfg else cfg
    in
    Z3.mk_context cfg
  in
  let dtenv = z3_dtenv_of_formula ctx @@ Formula.and_of (Formula.eq obj obj :: phis) in
  let z3fenv =
    Map.Poly.mapi fenv ~f:(fun ~key:var ~data:(params, sret, _, _, _) ->
      Z3.FuncDecl.mk_func_decl_s ctx (Ident.name_of_tvar var)
        (List.map params ~f:(snd >> of_sort ctx dtenv))
        (of_sort ctx dtenv sret))
  in
  debug_print_z3_input phis;
  let phis =
    List.map phis ~f:(of_formula_with_z3fenv ~id ctx [] [] z3fenv dtenv)
  in
  let obj =
    of_term ~id ctx [] [] z3fenv dtenv obj
  in
  check_opt_z3 ~timeout ~max ctx dtenv phis obj

let penv_of phi ctx dtenv =
  Formula.pred_sort_env_of phi
  |> Set.to_list
  |> List.map ~f:(pred_decl_of ctx dtenv)

(* satisfiability of [phis] with their predicate variables as uninterpreted
   functions (declared from [pred_sort_env_of]); used by the witness checker's
   consequence checks "original clauses /\ definitions => preprocessed
   clause" *)
let check_sat_with_preds ?(timeout = None) ~id fenv phis =
  let original_fenv = fenv in
  let full_equations = supports_defining_equations fenv in
  let fenv = if full_equations then fenv else fenv_for_query fenv phis in
  let original = phis in
  let phis = if full_equations then defining_equations_of fenv @ phis else phis in
  let cfg = [ ("model", "true") ] in
  (* Complete equations need ordinary declarations in a private context;
     a pooled native recursive declaration cannot be changed into one. *)
  let instance = get_instance id cfg (Hashtbl.Poly.create ()) in
  let ctx = instance.ctx in
  let phi = Formula.and_of phis in
  instance.dtenv <- z3_dtenv_of_formula ~init:instance.dtenv ctx phi;
  instance.fenv <-
    (if full_equations then
       Map.Poly.mapi fenv ~f:(fun ~key:var ~data:(params, sret, _, _, _) ->
         Z3.FuncDecl.mk_func_decl_s ctx (Ident.name_of_tvar var)
           (List.map params ~f:(snd >> of_sort ctx instance.dtenv))
           (of_sort ctx instance.dtenv sret))
     else z3_fenv_of ~id ~init:instance.fenv ctx [] [] fenv instance.dtenv);
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
  | Z3.Solver.UNSATISFIABLE when full_equations -> `Unsat
  | Z3.Solver.UNSATISFIABLE ->
      (match certify_shared_native_result ~id original_fenv original `Unsat with
       | `Unsat -> `Unsat
       | _ -> `Unknown)
  | Z3.Solver.SATISFIABLE ->
      if full_equations || Map.Poly.is_empty original_fenv then `Sat else `Unknown
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
          (* Without a timeout of its own, the elimination is bounded by what
             is left of an armed [Common.Timer] budget: the tactic runs in
             native code with the runtime released, where the budget's alarm
             cannot raise, so an elimination that does not return would hold
             the run past its budget (measured: a 20 s per-problem budget
             overrun to the 120 s outer kill in 2 of 3 runs, every sampled
             stack inside this tactic).  Cancelled, it declines as below. *)
          let timeout = timeout_or_armed_budget timeout in
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

(** [inc_check_valid solver exprs] asks whether the conjunction of [exprs] is
    unsatisfiable under [solver]'s assertions, and answers [Some true] when Z3
    says unsat, [Some false] when it says sat, and [None] when it decides
    neither (an [unknown], including a timeout set on [solver]).  The caller
    decides what an undecided query means: its only caller, the simplifier,
    keeps the atom it was asking about and asks nothing more about it
    ([decide_atom_by_validity]). *)
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
      Some false
  | UNSATISFIABLE ->
      if false then
        Debug.print @@ lazy (sprintf "checksat valid -> (unsat)valid");
      Some true
  | UNKNOWN -> None

(** [decide_atom_by_validity ~valid_neg ~valid_pos] decides an atom [a] under
    a context [C] from two validity questions, asked lazily and in this order:
    [valid_neg ()] asks whether [C /\ not a] is unsatisfiable, [valid_pos ()]
    whether [C /\ a] is.  It answers [Some true] when [a] is proved true under
    [C] (the first says [Some true]), [Some false] when [a] is proved false
    (the first says [Some false] and the second [Some true]), and [None]
    -- keep [a] -- otherwise.

    The second question is asked only when the first decided [Some false]:
    when the first is undecided ([None], typically a timeout) the atom is kept
    at once.  So an atom costs at most one undecided query, and under a
    per-query timeout at most one timeout; asking the second question too
    would let one hard atom cost two timeouts, for the rare atom whose negated
    query is undecided while the plain one would prove it false.  Keeping the
    atom is always sound: the simplified formula stays equivalent to the
    input. *)
let decide_atom_by_validity ~valid_neg ~valid_pos =
  match valid_neg () with
  | Some true -> Some true
  | None -> None
  | Some false -> (
      match valid_pos () with
      | Some true -> Some false
      | Some false | None -> None)

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
    (* Simplification is optional work, so a query Z3 does not decide (an
       [unknown] or a timeout of the validity query) keeps the atom, and the
       first undecided query ends the work on it: raising instead lost a
       found solution that a printer was simplifying, and asking the second
       query after an undecided first one made one hard atom cost two
       per-query timeouts. *)
    let ask phi () =
      inc_check_valid solver [ expr_of_default_true ~id ctx fenv dtenv phi ]
    in
    match
      decide_atom_by_validity
        ~valid_neg:(ask (Formula.negate phi))
        ~valid_pos:(ask phi)
    with
    | Some true -> (Atom.mk_true (), true)
    | Some false -> (Atom.mk_false (), true)
    | None -> (atom, false)

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

(** [simplify ?timeout ~id fenv phi] returns a formula equivalent to [phi],
    replacing an atom by true or false only when Z3 proves it so under its
    sibling conjuncts or disjuncts.  An atom whose query is undecided is kept,
    so the result never rests on a query that did not decide, and the first
    undecided query about an atom ends the work on it; [timeout], in
    milliseconds, bounds each query separately, not the whole call: an atom
    costs at most one undecided query (so at most one timeout), plus at most
    one query that decided. *)
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
