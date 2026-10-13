open Core
open Ast.LogicOld

(* A validity proof asked of cvc5 as a separate process, for a caller that
   reads only a proof.

   [valid_within ~ms ~id fenv phi] prints the negation of [phi] as SMT-LIB2 in
   Z3's own printing of the assertions ([Z3interface.elimination_query_text]:
   declarations, datatypes and the reached definitions, nothing asked of Z3),
   gives it to cvc5 ([./cvc5] or [cvc5] on PATH) with its own budget
   [--tlimit=ms], and kills the process by the wall clock one second after that
   budget (SIGTERM) and one second later still (SIGKILL), so the call returns
   whatever cvc5 does.  This helper uses the explicit [ms] only; it does not
   read [SolveDeadline].  A caller that honours a cooperative deadline must
   check expiry and cap its budget before asking.  Default options otherwise:
   a form of the zero-unknown
   verdict that Z3 left undecided at 30 s was proved by cvc5 so in 3.5-15 s,
   while [--enum-inst] is the checker's choice for its own constraints.

   Contract: [true] only when cvc5 printed [unsat] first, i.e. no model of its
   theory satisfies the negation, which makes [phi] valid in every model -- a
   read out of range, a division by zero or a selector off its constructor is
   part of the model there, as it is in this tree's reading.  [false] for
   everything else: [sat] (a countermodel from another solver is not checked
   against this tree's reading, so it is never a refutation), [unknown], a
   timeout, a kill, a parse error, a crash, or a text that cannot be printed.
   That rests on the printed text being the same question in cvc5's reading.
   Three adjustments are made and one refusal:
   - Z3 prints an in-range sequence read as [seq.nth_i], which cvc5 does not
     know; it is printed as [seq.nth].  Both are a function of the sequence and
     the index fixed by the sequence in range and left open out of range, so
     the question is the same;
   - a text holding [seq.nth_u] (Z3's read out of range, open even where the
     index is in range) is not asked, since [seq.nth] would fix it there;
   - Z3 prints the conversions between integers and bit-vectors by their
     SMT-LIB 2.7 names [(_ int_to_bv n)] and [ubv_to_int], which cvc5 1.0.4
     does not know; they are printed as cvc5's [(_ int2bv n)] and [bv2nat],
     which denote the same functions (the residue modulo [2^n], the unsigned
     value), so the question is the same.  [sbv_to_int] has no cvc5 1.0.4
     name and is left to fail;
   - a symbol cvc5 does not know is a parse error, which reads as [false]. *)

let file_count = Atomic.make 0

(* Rewrite only operator positions in parsed SMT-LIB. Source spans preserve
   literals, comments, quoted/user names, whitespace and opaque metadata.
   A declared/bound alias or target could shadow the converted builtin;
   decline that query rather than inventing an interpretation. *)
let cvc5_text z3_text =
  let module S = Common.Smtlib in
  let length = String.length z3_text in
  let token = function
    | S.Atom (a, b) -> Some (String.sub z3_text ~pos:a ~len:(b - a))
    | S.List _ -> None
  in
  let is node name = Option.equal String.equal (token node) (Some name) in
  let occupied = ref Set.Poly.empty in
  let add_name node =
    Option.iter (token node) ~f:(fun name ->
        if not (String.is_prefix name ~prefix:"\"") then
          occupied :=
            Set.add !occupied (String.strip ~drop:(Char.equal '|') name))
  in
  let names = function
    | S.List (_, _, entries) ->
        List.iter entries ~f:(function
          | S.List (_, _, name :: _) -> add_name name
          | _ -> ())
    | _ -> ()
  in
  let rec all_names = function
    | S.Atom _ as node -> add_name node
    | S.List (_, _, nodes) -> List.iter nodes ~f:all_names
  in
  let rec declarations = function
    | S.Atom _ -> ()
    | S.List (_, _, head :: name :: args :: rest)
      when is head "define-fun" || is head "define-fun-rec" ->
        add_name name;
        names args;
        List.iter rest ~f:declarations
    | S.List (_, _, head :: name :: _)
      when is head "declare-fun" || is head "declare-const"
           || is head "declare-sort" ->
        add_name name
    | S.List (_, _, head :: rest)
      when is head "declare-datatype" || is head "declare-datatypes" ->
        List.iter rest ~f:all_names
    | S.List (_, _, head :: S.List (_, _, signatures) :: rest)
      when is head "define-funs-rec" ->
        List.iter signatures ~f:(function
          | S.List (_, _, name :: args :: _) ->
              add_name name;
              names args
          | _ -> ());
        List.iter rest ~f:declarations
    | S.List (_, _, nodes) ->
        (match nodes with
        | head :: bindings :: _
          when is head "forall" || is head "exists" || is head "lambda"
               || is head "let" ->
            names bindings
        | _ -> ());
        List.iter nodes ~f:declarations
  in
  let changes = ref [] in
  let refused = ref false in
  let rename node name =
    match node with
    | S.Atom (a, b) ->
        if
          Set.mem !occupied (Option.value_exn (token node))
          || Set.mem !occupied name
        then refused := true
        else changes := (a, b, name) :: !changes
    | _ -> ()
  in
  let rec term = function
    | S.Atom _ -> ()
    | S.List (_, _, [ head; _; body ])
      when is head "forall" || is head "exists" || is head "lambda" ->
        term body
    | S.List (_, _, [ head; S.List (_, _, bindings); body ]) when is head "let"
      ->
        List.iter bindings ~f:(function
          | S.List (_, _, [ _; value ]) -> term value
          | _ -> refused := true);
        term body
    | S.List (_, _, head :: body :: attrs) when is head "!" ->
        term body;
        attributes attrs
    | S.List (_, _, [ head; op; _ ]) when is head "_" && is op "int_to_bv" ->
        rename op "int2bv"
    | S.List (_, _, nodes) ->
        (match nodes with
        | head :: _ when is head "seq.nth_u" -> refused := true
        | head :: _ when is head "seq.nth_i" -> rename head "seq.nth"
        | head :: _ when is head "ubv_to_int" -> rename head "bv2nat"
        | _ -> ());
        List.iter nodes ~f:term
  and attributes = function
    | key :: value :: rest when is key ":pattern" || is key ":no-pattern" ->
        term value;
        attributes rest
    | _ :: _ :: rest -> attributes rest
    | _ -> ()
  in
  let command = function
    | S.List (_, _, [ head; body ]) when is head "assert" -> term body
    | S.List (_, _, [ head; _; _; _; body ])
      when is head "define-fun" || is head "define-fun-rec" ->
        term body
    | S.List (_, _, [ head; _; S.List (_, _, bodies) ])
      when is head "define-funs-rec" ->
        List.iter bodies ~f:term
    | _ -> ()
  in
  try
    let nodes = S.parse z3_text in
    List.iter nodes ~f:declarations;
    List.iter nodes ~f:command;
    if !refused then None
    else
      let buffer = Buffer.create length in
      let pos =
        List.fold
          (List.sort !changes ~compare:(fun (a, _, _) (b, _, _) ->
               Int.compare a b))
          ~init:0
          ~f:(fun pos (a, b, name) ->
            Buffer.add_substring buffer z3_text ~pos ~len:(a - pos);
            Buffer.add_string buffer name;
            b)
      in
      Buffer.add_substring buffer z3_text ~pos ~len:(length - pos);
      Some (Buffer.contents buffer ^ "(check-sat)\n")
  with Invalid_argument _ -> None

(* An optional record of every call, read from the environment per call and off
   unless set; it changes no answer.  [COAR_CVC5_RETRY_LOG=<file>] appends one
   line per call to <file>:
     cvc5-retry site=<s> size=<n> ms=<budget> rlimit=<n|-> outcome=<o>
       wall_ms=<t> ru=<units|->
   where [outcome] is cvc5's first answer line ([unsat], [sat], [unknown]),
   [error] (failure to read an answer, including abnormal termination) or
   [none] (no output), and [ru] is cvc5's own
   count of the resource units it spent ([resource::resourceUnitsUsed], read
   from [--stats --stats-internal], which the record adds to the command line;
   a process killed by the wall clock prints none).  The units are what a
   resource limit ([--rlimit-per]) counts, so the record is what a budget in
   units, rather than in milliseconds, is chosen from.
   The command helper does not expose the termination cause here: elapsed
   time records duration and cannot distinguish a kill from a late error.
   [COAR_CVC5_RETRY_DUMP=<dir>] also writes each text asked to <dir>, so that a
   question can be asked again outside the run.  Both are read at each call
   (one lookup beside starting a process). *)
let log_file () = Sys.getenv "COAR_CVC5_RETRY_LOG"
let dump_dir () = Sys.getenv "COAR_CVC5_RETRY_DUMP"

(* a line of cvc5's statistics, [name = value] with a [::]-qualified name *)
let is_stats_line l =
  String.is_substring l ~substring:"::"
  && String.is_substring l ~substring:" = "

let resource_units lines =
  List.find_map lines ~f:(fun l ->
      String.chop_prefix (String.strip l)
        ~prefix:"resource::resourceUnitsUsed = ")

let append_log line =
  match log_file () with
  | None -> ()
  | Some file -> (
      try
        Out_channel.with_file file ~append:true ~f:(fun oc ->
            Out_channel.output_string oc (line ^ "\n"))
      with e when not (Common.Timer.is_async e) -> ())

(* [true] iff cvc5 run on [text] within [ms] milliseconds prints [unsat]
   first; [trace] is given what it printed first (or why nothing was read).
   [rlimit], when given, is also passed as [--rlimit-per]: cvc5 then stops
   after that many of its resource units and answers [unknown], a count that
   does not depend on the machine's load; [ms] stays as cvc5's time limit and
   the wall-clock kill one second after it.  [site] and [size] only label the
   optional record above. *)
let unsat_within ?(trace = fun _ -> ()) ?rlimit ?(site = "ladder") ?size ~ms
    text =
  let n = Atomic.fetch_and_add file_count 1 in
  let file =
    sprintf "temp_ladder_cvc5_p%d_%d.smt2" (Pid.to_int @@ Core_unix.getpid ()) n
  in
  let logging = Option.is_some (log_file ()) in
  (match dump_dir () with
  | None -> ()
  | Some dir -> (
      try
        Out_channel.write_all
          (sprintf "%s/%s_p%d_%d.smt2" dir site
             (Pid.to_int @@ Core_unix.getpid ())
             n)
          ~data:text
      with e when not (Common.Timer.is_async e) -> ()));
  (* Keep both elapsed-time readings on the process's selected clock. *)
  let started = Common.Clock.now_ns () in
  let record outcome lines =
    if logging then
      append_log
        (sprintf
           "cvc5-retry site=%s size=%s ms=%d rlimit=%s outcome=%s wall_ms=%d \
            ru=%s"
           site
           (Option.value_map size ~default:"-" ~f:Int.to_string)
           ms
           (Option.value_map rlimit ~default:"-" ~f:Int.to_string)
           outcome
           (Float.iround_nearest_exn
              (Time_ns.Span.to_ms (Time_ns.diff (Common.Clock.now_ns ()) started)))
           (Option.value (resource_units lines) ~default:"-"))
  in
  Exn.protect
    ~finally:(fun () ->
      try Core_unix.unlink file
      with e when not (Common.Timer.is_async e) -> ())
    ~f:(fun () ->
      Out_channel.write_all file ~data:text;
      match
        Common.Util.Command.sync_command "timeout"
          ([
             "-k";
             "1";
             Int.to_string (((ms + 999) / 1000) + 1);
             Common.Util.Command.resolve_tool "cvc5";
             sprintf "--tlimit=%d" ms;
           ]
          @ Option.value_map rlimit ~default:[] ~f:(fun r ->
              [ sprintf "--rlimit-per=%d" r ])
          @ (if logging then [ "--stats"; "--stats-internal" ] else [])
          @ [ file ])
          []
      with
      | lines -> (
          (* the statistics, when asked for, go to the same stream and are not
             an answer *)
          match
            List.filter lines ~f:(fun l -> not (logging && is_stats_line l))
          with
          | first :: _ ->
              let first = String.strip first in
              trace (String.prefix first 200);
              record
                (match first with
                | "unsat" | "sat" | "unknown" -> first
                | _ -> "error")
                lines;
              String.equal first "unsat"
          | [] ->
              trace "no output";
              record "none" lines;
              false)
      | exception e when not (Common.Timer.is_interrupt e) ->
          let msg =
            match e with
            | Common.Util.Command.Shell_error out -> out
            | _ -> Exn.to_string e
          in
          trace ("no answer read: " ^ String.prefix (String.strip msg) 200);
          record "error" (String.split_lines msg);
          false)

(* Whether [valid_within] answers a literally [true] formula without
   printing it, and answers a text it has already had a definite answer to
   ([unsat] or [sat]) from that answer instead of starting cvc5 again.  Set by
   the coordinator from its configuration
   ([ladder_proof_shortcuts_no_unknown_query]); process-wide.  [false] asks
   every text.

   Exactness.  [true] is valid in every model, and its negation prints as
   [(assert false)], which cvc5 answers [unsat] whenever it answers.  A
   repeated text gets the same boolean: cvc5 is deterministic for one text
   and one set of options (its resource-unit count for a text was the same in
   every run and replay measured), so a text once answered [unsat] is
   answered [unsat] again whenever cvc5 answers within its budget, and one
   answered [sat] is never answered [unsat] by a sound solver; the budget
   and the resource limit only decide whether an answer comes at all, which
   is why only [unsat] and [sat] are kept and never [unknown], a kill or an
   error (a time limit can cut a question short under one load and not under
   another).

   Scope.  The memo is this process's: a forked copy inherits the entries
   made before it was forked, and what it records is lost with it, so a text
   asked in several forked copies of one run is still asked once in each. *)
let shortcuts = ref false

(* The digest selects a bucket; only the exact text licenses reuse of its
   definite answer. A colliding text replaces the bucket and causes a safe
   miss for the previous text. Guard both lookup and replacement since solver
   domains share this process-wide memo. *)
let memo : (string, string * bool) Hashtbl.t = Hashtbl.create (module String)
let memo_lock = Stdlib.Mutex.create ()

let memo_find ~text key =
  Stdlib.Mutex.protect memo_lock (fun () ->
      match Hashtbl.find memo key with
      | Some (recorded_text, v) when String.equal text recorded_text -> Some v
      | _ -> None)

let memo_add ~text key v =
  Stdlib.Mutex.protect memo_lock (fun () ->
      Hashtbl.set memo ~key ~data:(text, v))

(* how many calls the shortcuts answered without cvc5, in this process: a
   literally [true] formula, and a text answered from [memo]; read by the
   tests *)
let true_shortcuts = Atomic.make 0
let memo_hits = Atomic.make 0

(* [unsat_within] through [memo] when [shortcuts] is set: a recorded answer
   is returned (and noted in the optional record as [memo-unsat] or
   [memo-sat]); otherwise cvc5 is asked and a definite answer recorded *)
let unsat_within_memo ?trace ?rlimit ?site ?size ~ms text =
  if not !shortcuts then unsat_within ?trace ?rlimit ?site ?size ~ms text
  else
    let key = Stdlib.Digest.to_hex (Stdlib.Digest.string text) in
    match memo_find ~text key with
    | Some v ->
        Atomic.incr memo_hits;
        Option.iter trace ~f:(fun t ->
            t (if v then "unsat (recorded)" else "sat (recorded)"));
        append_log
          (sprintf
             "cvc5-retry site=%s size=%s ms=%d rlimit=%s outcome=%s wall_ms=0 \
              ru=-"
             (Option.value site ~default:"ladder")
             (Option.value_map size ~default:"-" ~f:Int.to_string)
             ms
             (Option.value_map rlimit ~default:"-" ~f:Int.to_string)
             (if v then "memo-unsat" else "memo-sat"));
        v
    | None ->
        let first = ref None in
        let trace' l =
          first := Some l;
          Option.iter trace ~f:(fun t -> t l)
        in
        let v = unsat_within ~trace:trace' ?rlimit ?site ?size ~ms text in
        (match !first with
        | Some "unsat" -> memo_add ~text key true
        | Some "sat" -> memo_add ~text key false
        | _ -> ());
        v

let valid_within ?(trace = fun _ -> ()) ?rlimit ?site ~ms ~id fenv phi =
  if !shortcuts && Formula.is_true phi then (
    Atomic.incr true_shortcuts;
    trace "proved without asking: the formula is [true]";
    true)
  else
    match
      Z3Smt.Z3interface.elimination_query_text ~id fenv [ Formula.negate phi ]
    with
    | exception e when not (Common.Timer.is_interrupt e) ->
        trace "not asked: the question could not be printed";
        false
    | z3_text -> (
        match cvc5_text z3_text with
        | None ->
            trace "not asked: the text cannot be translated safely for cvc5";
            false
        | Some text ->
            let size =
              if Option.is_some (log_file ()) then Some (Formula.ast_size phi)
              else None
            in
            unsat_within_memo ~trace ?rlimit ?site ?size ~ms text)
