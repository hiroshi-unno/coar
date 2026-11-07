(* Athena's route from a C program to a problem MuVal solves:

     the program --Ptr2ArrFC--> C --clang 19--> LLVM IR
       --llvm2lts--> an LTS (T2), read by CoAR's LTS frontend
       --or the LLVM frontend--> muCLP

   with every intermediate file in one directory, under the names and with
   the options of the competition script that ran these steps as separate
   programs (script/svcomp/helpers/solver.sh, the llvm2lts and direct
   frontends with the new Ptr2Arr), so that both produce the same files.

   Termination of a memory-safe program ([Termination_memory_safe]) is two
   such routes run side by side, as termCOMP's C_MemorySafety wrapper
   (script/termcomp/solver_llvm2lts.sh) runs them: see [run_term_memsafe].

   Contract: a step that declines the program -- the rewriting finding a
   construct outside its fragment, clang failing, a translation that does
   not support what it reads -- makes the answer [Unknown] with the reason
   (answered MAYBE), as the script answers MAYBE; a step this build lacks is
   refused (an error) before anything runs. *)
open Core

(* the question a run answers: whether no call of reach_error is reachable,
   whether every execution ends, whether no memory-safety violation is
   reachable, or whether every execution of a program without one ends *)
type property =
  | Unreach_call
  | Termination
  | Memory_safety
  | No_overflow
  | Memory_cleanup
  | Termination_memory_safe

(* the question one translated problem states *)
type question =
  | Q_unreach_call
  | Q_termination
  | Q_memory_safety
  | Q_no_overflow
  | Q_memory_cleanup
type data_model = LP64 | ILP32
(* [Holds]: the property holds without a problem to solve *)
type 'p answer = Problem of 'p | Unknown of string | Holds

let string_of_data_model = function LP64 -> "LP64" | ILP32 -> "ILP32"

(* A path the configuration gives, for a step run in the intermediate files'
   directory: a relative one is read from this process's directory, as a
   path in the configuration always is.  A program's name without a slash
   is left to the PATH lookup. *)
let from_here ?(program = false) path =
  if Filename.is_relative path && ((not program) || String.mem path '/') then
    Sys_unix.getcwd () ^/ path
  else path

(* The intermediate files' directory, absolute: [work_dir] kept, or a fresh
   one removed when [f] returns. *)
let with_work_dir (cfg : Config.t) f =
  match cfg.work_dir with
  | Some dir ->
      Core_unix.mkdir_p dir;
      f (Filename_unix.realpath dir)
  | None ->
      let dir = Filename_unix.temp_dir "athena" "" in
      let rec remove path =
        match Sys_unix.is_directory path with
        | `Yes ->
            Array.iter (Sys_unix.readdir path) ~f:(fun name ->
                remove (path ^/ name));
            Core_unix.rmdir path
        | `No | `Unknown -> Sys_unix.remove path
      in
      Exn.protect
        ~f:(fun () -> f dir)
        ~finally:(fun () ->
          (* a directory left behind is litter, not a wrong answer *)
          try remove dir with exn when not (Common.Timer.is_async exn) -> ())

(* The input's name without its directory and without [.c] or [.i]: the
   stem of every intermediate file's name. *)
let base_name src =
  let base = Filename.basename src in
  let base = Option.value (String.chop_suffix base ~suffix:".c") ~default:base in
  Option.value (String.chop_suffix base ~suffix:".i") ~default:base

(* The C-to-C step.  [--scalar-cells]: a one-cell region allocated once and
   never moved from is held in a scalar, so that a bound read through such a
   pointer needs no invariant about an array.  [Modulo] makes the
   wrap-arounds explicit; [Auto] lets the rewriting choose the reading, and
   its value analysis, which has no time bound of its own, is given up after
   [eva_timeout_s] seconds: the program is then rewritten again without it,
   every reduction kept and the reading still chosen.  The question adds its
   own mode: a termination question [--assume-safety] when [assume_safety],
   a memory-safety one [--memory-safety] with every violation a call of
   reach_error, which the translations read as the error location, a
   no-overflow one [--check-overflow] (a signed operation that overflows at
   the data model's widths calls reach_error, the input's own renamed), a
   memory-cleanup one [--memory-cleanup] with each violation a call of a
   marker of its own ([select_marker]). *)
let memtrack (cfg : Config.t) =
  match cfg.memtrack with
  | Not_checked -> [ "--memtrack-check=none" ]
  | Halting -> []
  | Nonterminating_too -> [ "--memtrack-nonterminating" ]

(* The reading of signed overflow of a configuration [normalise]d *)
let signed_overflow (cfg : Config.t) =
  Option.value cfg.signed_overflow ~default:Config.Undefined

(* [cfg] with its integers and signed overflow as [Config.reading] states
   them: never [Wrap_unsigned] nor [Wrap_all], and [signed_overflow] [Some]
   except under [Unbounded]; refused as [Config.reading] refuses.  Every
   step below reads a normalised configuration. *)
let normalise (cfg : Config.t) =
  Or_error.map (Config.reading cfg) ~f:(fun (integers, signed_overflow) ->
      { cfg with integers; signed_overflow })

(* Whether the rewriting makes signed wrap-around explicit
   ([--wrap-integers=all], gcc's -fwrapv): under [Wraps] with [Modulo] or
   [Bit_vector] integers, except for a no-overflow question, whose answer
   is decided at the first overflow and which the rewriting's overflow check
   does not combine with it. *)
let wraps_signed_in_rewriting (cfg : Config.t) ~question =
  match (cfg.integers, signed_overflow cfg, question) with
  | _, _, Q_no_overflow -> false
  | (Modulo | Bit_vector), Wraps, _ -> true
  | _ -> false

let rewrite (cfg : Config.t) ~data_model ~question ~assume_safety ~dir ~src
    ~c_file ~record =
  let open Or_error.Monad_infix in
  let options =
    [ "--data-model=" ^ string_of_data_model data_model; "--scalar-cells" ]
    @ (match (cfg.regions, cfg.integers) with
      | ( Unbounded_regions,
          (Mathematical | Modulo | Auto | Unbounded | Wrapping | Wrap_unsigned | Wrap_all) )
        ->
          [ "--unbounded-regions" ]
      | Unbounded_regions, Bit_vector | Bounded, _ -> [])
    @ (if wraps_signed_in_rewriting cfg ~question then [ "--wrap-integers=all" ]
       else
         match cfg.integers with
         | Modulo -> [ "--wrap-integers" ]
         | Auto -> [ "--integers=auto" ]
         | Mathematical | Bit_vector | Unbounded | Wrapping | Wrap_unsigned | Wrap_all -> [])
    @ (match cfg.preprocessor with
      | Clang -> [ "--clang=" ^ from_here ~program:true cfg.clang ]
      | Gcc -> [ "--gcc" ])
    @
    match question with
    | Q_termination when assume_safety -> [ "--assume-safety" ]
    | Q_termination | Q_unreach_call -> []
    | Q_no_overflow -> [ "--check-overflow" ]
    | Q_memory_safety ->
        [ "--memory-safety"; "--violation-markers=reach-error" ] @ memtrack cfg
    | Q_memory_cleanup ->
        [ "--memory-cleanup"; "--violation-markers=split" ] @ memtrack cfg
  in
  let env =
    match cfg.framac_share with
    | Some share ->
        [| "DUNE_DIR_LOCATIONS=frama-c:share:" ^ from_here share |]
    | None -> [||]
  in
  let p2a ?timeout options =
    P2aEntry.run ~env ?timeout ~cwd:dir
      (options @ [ "-o"; c_file; "--record=" ^ record; src ])
  in
  (match cfg.integers with
  | Auto -> (
      p2a ~timeout:(Float.of_int cfg.eva_timeout_s) options >>= function
      | P2aEntry.Timed_out -> p2a (options @ [ "--integers-eva=off" ])
      | outcome -> Ok outcome)
  | Mathematical | Modulo | Bit_vector | Unbounded | Wrapping | Wrap_unsigned | Wrap_all ->
      p2a options)
  >>| function
  | P2aEntry.Exited 0 -> None
  | P2aEntry.Exited 2 ->
      Some
        "the rewriting (Ptr2ArrFC) declined the program: it has a construct \
         outside the rewriting's fragment (listed above)"
  | P2aEntry.Exited status ->
      Some
        (sprintf
           "the rewriting (Ptr2ArrFC) could not read the program or failed \
            (status %d)"
           status)
  | P2aEntry.Timed_out -> Some "the rewriting (Ptr2ArrFC) timed out"

(* [Auto]: the reading the rewriting chose, from its record *)
let record_reads_bv record =
  match Yojson.Safe.from_file record with
  | json -> (
      match Yojson.Safe.Util.(json |> member "integers" |> member "reading") with
      | `String "bv" -> true
      | _ | (exception Yojson.Safe.Util.Type_error _) -> false)
  | exception (Yojson.Json_error _ | Sys_error _) -> false

(* clang 19 with the flags both translations expect: no optimisation, the
   loops not assumed finite, no floating-point contraction, debug
   information, and the errors a modern clang makes of old C's implicit
   declarations turned back into warnings.  For the direct route also
   clang's trapping check of a signed left shift, which is otherwise an
   [shl] with no flag the translation could read, unless signed arithmetic
   wraps, where such a shift is defined (gcc documents its signed [<<] as
   two's complement) and the caller passes [~shift_check:false]. *)
let compile (cfg : Config.t) ~data_model ~shift_check ~dir ~c_file ~ll =
  let args =
    [ "-S"; "-emit-llvm"; "-O0"; "-Xclang"; "-disable-O0-optnone";
      "-fno-finite-loops"; "-ffp-contract=off" ]
    @ (if shift_check then
         [ "-fsanitize=shift-base"; "-fsanitize-trap=shift-base" ]
       else [])
    @ [ "-Wno-error=int-conversion";
        "-Wno-error=implicit-function-declaration"; "-Wno-error=implicit-int";
        "-Wno-error=incompatible-function-pointer-types" ]
    @ cfg.clang_flags
    @ [ "-g";
        (match data_model with LP64 -> "-m64" | ILP32 -> "-m32");
        c_file; "-o"; ll ]
  in
  match Process.run ~cwd:dir (from_here ~program:true cfg.clang) args with
  | Ok () -> None
  | Error status ->
      Some
        (sprintf "clang (%s) failed on the rewritten program (%s)" cfg.clang
           status)

(* A step this build lacks, refused by the step's stub, which says what is
   missing and how to obtain it. *)
let missing_steps (cfg : Config.t) ~direct_available =
  let open Or_error in
  (if P2aEntry.available then return ()
   else P2aEntry.run ~cwd:"." [] >>= fun _ -> return ())
  >>= fun () ->
  match cfg.route with
  | Llvm2lts when not Llvm2ltsEntry.available ->
      Llvm2ltsEntry.translate ~data_model:LP64 ~mode:Int ~property:Termination
        ""
      >>= fun _ -> return ()
  | Direct when not direct_available ->
      error_string
        "Athena's direct route (route Direct) needs the LLVM frontend, which \
         was not built into this CoAR: LLVM 19's OCaml bindings were absent \
         when it was built"
  | Llvm2lts | Direct -> return ()

(* What the steps before the solver made of the program: a reason it was
   declined, or the problem's file, an LTS in the T2 format or LLVM IR, and
   whether it is read in BV mode. *)
type prepared =
  | Declined of string
  | Holds_unchecked  (** no check of the property was placed: it holds *)
  | Lts_file of { file : string; bv_mode : bool }
  | Ir_file of {
      file : string;
      bv_mode : bool;
      config : string;
      overrides : (string * Yojson.Safe.t) list;
          (** members of the LLVM frontend's configuration that replace the
              file's: the reading of signed overflow and of UB the Athena
              configuration states where it is not the file's default *)
    }

(* The IR [ir] with the memory-cleanup marker as the error event.  The
   translations have one error event, a call of reach_error (or
   __VERIFIER_error); with split markers the rewriting writes each violation
   as a call of a function of its own, __p2a_violation_<property>, defined
   as _Exit, and leaves the input's reach_error an ordinary function.  So the
   input's reach_error and __VERIFIER_error are renamed to
   __p2a_input_reach_error and __p2a_input___VERIFIER_error, which the
   translations read as the end of an execution (they are not the property
   at hand), and the marker to reach_error, so that a deref or free
   violation (undefined behaviour, after which nothing is required) ends the
   execution rather than counting as a leak; a defined reach_error is still
   the error event, its body not followed.  An LLVM global name is matched
   whole: the character after it is not one an unquoted name may hold.
   [`Absent]: no marker, so no check was placed and the property holds;
   [`Conflict]: the input already names a target. *)
let select_marker ir =
  let name_char c = Char.is_alphanum c || String.mem "-$._" c in
  let occurs text name =
    let pat = "@" ^ name and n = String.length text in
    List.exists (String.substr_index_all text ~may_overlap:false ~pattern:pat)
      ~f:(fun i ->
        let j = i + String.length pat in
        j >= n || not (name_char text.[j]))
  in
  let rename text ~from ~into =
    let pat = "@" ^ from and n = String.length text in
    let buf = Buffer.create (n + 64) in
    let rec go pos =
      match String.substr_index text ~pos ~pattern:pat with
      | None -> Buffer.add_substring buf text ~pos ~len:(n - pos)
      | Some i ->
          let j = i + String.length pat in
          Buffer.add_substring buf text ~pos ~len:(i - pos);
          if j >= n || not (name_char text.[j]) then Buffer.add_string buf ("@" ^ into)
          else Buffer.add_string buf pat;
          go j
    in
    go 0;
    Buffer.contents buf
  in
  let marker = "__p2a_violation_valid_memcleanup" in
  if occurs ir "__p2a_input_reach_error" || occurs ir "__p2a_input___VERIFIER_error"
  then `Conflict
  else if not (occurs ir marker) then `Absent
  else
    `Selected
      (ir
      |> rename ~from:"reach_error" ~into:"__p2a_input_reach_error"
      |> rename ~from:"__VERIFIER_error" ~into:"__p2a_input___VERIFIER_error"
      |> rename ~from:marker ~into:"reach_error")

(* The steps before the solver for [question], in [dir], their files named
   after [stem]. *)
let prepare (cfg : Config.t) ~data_model ~question ~assume_safety ~dir ~stem
    ~src =
  let open Or_error.Monad_infix in
  (* relative to [dir], where the steps run, as the script names them *)
  let c_file = stem ^ "_Ptr2ArrFC.c" and record = stem ^ "_Ptr2ArrFC.p2a.json" in
  rewrite cfg ~data_model ~question ~assume_safety ~dir ~src ~c_file ~record
  >>= function
  | Some reason -> Ok (Declined reason)
  | None -> (
      let reads_bv =
        match cfg.integers with
        | Bit_vector -> true
        | Auto -> record_reads_bv (dir ^/ record)
        | Mathematical | Modulo | Unbounded | Wrapping | Wrap_unsigned | Wrap_all -> false
      in
      (* the compiled IR as the translations are to read it *)
      let select ll k =
        match question with
        | Q_memory_cleanup -> (
            match select_marker (In_channel.read_all (dir ^/ ll)) with
            | `Absent -> Ok Holds_unchecked
            | `Conflict ->
                Ok
                  (Declined
                     "the error event cannot be chosen: the input already \
                      names __p2a_input_reach_error or \
                      __p2a_input___VERIFIER_error")
            | `Selected text ->
                let sel = Filename.chop_suffix ll ".ll" ^ "_sel.ll" in
                Out_channel.write_all (dir ^/ sel) ~data:text;
                k sel)
        | Q_unreach_call | Q_termination | Q_memory_safety | Q_no_overflow -> k ll
      in
      match cfg.route with
      | Llvm2lts -> (
          let ll = stem ^ "_llvm2lts.ll" in
          match compile cfg ~data_model ~shift_check:false ~dir ~c_file ~ll with
          | Some reason -> Ok (Declined reason)
          | None ->
              select ll @@ fun ll ->
              (* [Auto] in Int mode reads the reductions the rewriting placed
                 with bitwise operations in infinite two's complement, which
                 do not wrap; [Unbounded] reads them so too, every
                 nondeterministic value unbounded *)
              let mode : Llvm2ltsEntry.mode =
                match cfg.integers with
                | Mathematical | Modulo -> Int
                | Bit_vector -> Bv
                | Auto -> if reads_bv then Bv else Int_bitwise
                | Unbounded -> Int_bitwise
                | Wrapping | Wrap_unsigned | Wrap_all -> (
                    match signed_overflow cfg with
                    | Wraps -> Int_wrap_all
                    | Undefined | Arbitrary_value -> Int_wrap_unsigned)
              in
              Llvm2ltsEntry.translate
                ~unbounded_nondet:
                  (match cfg.integers with Unbounded -> true | _ -> false)
                ~hoist:(match cfg.hoist with Hoisted -> true | Not_hoisted -> false)
                ~accumulator_recursion:
                  (match cfg.tail_recursion with
                  | Accumulated -> true
                  | Returned_as_is -> false)
                ~simplifycfg:
                  (match cfg.control_flow with
                  | Simplified -> true
                  | As_compiled -> false)
                ~data_model:
                  (match data_model with LP64 -> LP64 | ILP32 -> ILP32)
                ~mode
                ~property:
                  (match question with
                  | Q_unreach_call | Q_memory_safety | Q_no_overflow
                  | Q_memory_cleanup ->
                      Unreach_call
                  | Q_termination -> Termination)
                (dir ^/ ll)
              >>| function
              | Failed reason -> Declined reason
              | T2 text ->
                  let t2 = dir ^/ stem ^ ".t2" in
                  Out_channel.write_all t2 ~data:text;
                  Lts_file { file = t2; bv_mode = reads_bv })
      | Direct -> (
          let ll = stem ^ "_direct.ll" in
          let shift_check =
            match signed_overflow cfg with Wraps -> false | Undefined | Arbitrary_value -> true
          in
          match compile cfg ~data_model ~shift_check ~dir ~c_file ~ll with
          | Some reason -> Ok (Declined reason)
          | None ->
              select ll @@ fun ll ->
              let config =
                match (cfg.llvmfront, cfg.integers) with
                | Some file, _ -> file
                | None, Modulo -> "./config/llvmfront/modulo.json"
                | None, Unbounded -> "./config/llvmfront/unbounded.json"
                | None, (Wrapping | Wrap_unsigned | Wrap_all) -> (
                    match signed_overflow cfg with
                    | Wraps -> "./config/llvmfront/wrap_all.json"
                    | Undefined | Arbitrary_value -> "./config/llvmfront/wrap_unsigned.json")
                | None, (Mathematical | Bit_vector | Auto) ->
                    "./config/llvmfront/llvmfront.json"
              in
              (* the file's own setting stands where the Athena
                 configuration states the file's default *)
              let overrides =
                (match (cfg.integers, cfg.signed_overflow) with
                | Unbounded, _ | _, (None | Some (Wraps | Undefined)) -> []
                | _, Some Arbitrary_value ->
                    [ ("signed_overflow", `List [ `String "Arbitrary_value" ]) ])
                @
                match cfg.undefined_behaviour with
                | Path_stops -> []
                | Is_violation -> [ ("ub_reading", `List [ `String "Literal_c" ]) ]
              in
              Ok (Ir_file { file = dir ^/ ll; bv_mode = reads_bv; config; overrides })))

let question_of = function
  | Unreach_call -> Q_unreach_call
  | Termination -> Q_termination
  | Memory_safety -> Q_memory_safety
  | No_overflow -> Q_no_overflow
  | Memory_cleanup -> Q_memory_cleanup
  | Termination_memory_safe ->
      invalid_arg "Pipeline: Termination_memory_safe is two questions"

(* Whether a translation's refusal is one of a bit operation only
   bit-vectors translate, in an Int reading: llvm2lts's reason, or the direct
   translation's, which names Int mode too *)
let int_refusal reason =
  List.exists
    [ "a bitwise operation between two variables in Int mode";
      "a shift by a variable amount in Int mode" ]
    ~f:(fun substring -> String.is_substring reason ~substring)

(* One question answered in this process: [lts] and [direct] read the
   problem's file and return how to solve it ([direct] given the LLVM
   frontend's configuration file and the members that replace the file's).
   The configuration is [normalise]d first, so a combination
   [Config.reading] refuses is an error before any step runs.  With [Bit_vector_fallback],
   a question an Int reading's translation refuses for a bit operation is
   prepared again with [Bit_vector] integers (the direct route's
   configuration then every field's default), its files named [<stem>_bv]. *)
let run (cfg : Config.t) ~data_model ~property ~direct_available ~direct ~lts
    src =
  let open Or_error.Monad_infix in
  normalise cfg >>= fun cfg ->
  missing_steps cfg ~direct_available >>= fun () ->
  with_work_dir cfg @@ fun dir ->
  let base = base_name src in
  let src = Filename_unix.realpath src in
  let question = question_of property in
  let assume_safety =
    match cfg.memory with Assumed_safe -> true | Unchecked -> false
  in
  let can_fall_back (cfg : Config.t) =
    match (cfg.bv_fallback, cfg.integers) with
    | ( Bit_vector_fallback,
        (Mathematical | Modulo | Unbounded | Wrapping | Wrap_unsigned | Wrap_all) ) ->
        true
    | No_fallback, _ | _, (Bit_vector | Auto) -> false
  in
  (* the reading of signed overflow is kept; unbounded integers become
     bit-vectors whose overflow is undefined *)
  let as_bv (cfg : Config.t) =
    {
      cfg with
      integers = Bit_vector;
      llvmfront = None;
      signed_overflow = Some (signed_overflow cfg);
    }
  in
  let rec attempt (cfg : Config.t) ~stem =
    prepare cfg ~data_model ~question ~assume_safety ~dir ~stem ~src
    >>= function
    | Declined reason when can_fall_back cfg && int_refusal reason ->
        attempt (as_bv cfg) ~stem:(stem ^ "_bv")
    | Declined reason -> Ok (Unknown reason)
    | Holds_unchecked -> Ok Holds
    | Lts_file { file; bv_mode } -> lts ~bv_mode file
    | Ir_file { file; bv_mode; config; overrides } -> (
        direct ~bv_mode ~config ~overrides file >>= function
        (* [Auto] in Int mode: a form Int mode cannot write that the
           rewriting's scan missed is translated again in BV mode, where the
           reductions are the identity *)
        | Unknown reason
          when (match cfg.integers with Auto -> true | _ -> false)
               && (not bv_mode)
               && String.is_substring reason ~substring:"in Int mode" ->
            direct ~bv_mode:true ~config ~overrides file
        | Unknown reason
          when can_fall_back cfg
               && String.is_substring reason ~substring:"in Int mode" ->
            attempt (as_bv cfg) ~stem:(stem ^ "_bv")
        | answer -> Ok answer)
  in
  attempt cfg ~stem:base

(* when this process started, near enough: the module is initialised before
   [main] reads its command line *)
let started = Core_unix.gettimeofday ()

(* The last line of [file] with any carriage return removed, empty when
   there is none *)
let last_line file =
  match In_channel.read_lines file with
  | lines -> (
      match List.last lines with
      | Some line -> String.strip ~drop:(Char.equal '\r') line
      | None -> "")
  | exception Sys_error _ -> ""

(* Termination of a program with no reachable memory-safety violation,
   answered as termCOMP's C_MemorySafety wrapper answers it: the
   termination question with every violation ending the execution
   ([--assume-safety]: sound here, since a program with a reachable violation
   has no correct answer and on a safe one no execution is ended) and, side by
   side, the memory-safety question.  Each is solved by a run of this
   executable under the solver configuration [solver_config] ([-p ltsterm],
   [-p ltssafe], or their BV forms), in a session of its own.

   The answer: [UNSAFE] when the safety side answers NO -- a reachable
   violation, which decides the answer whatever the termination side says,
   so that side is stopped at once; else the termination side's YES or NO,
   and MAYBE for anything else.  A termination side that has ended without
   YES or NO leaves nothing for the safety side to decide, so that side is
   stopped.  A termination YES or NO waits for the safety side only until
   [safety_wait_s] seconds after this process started, and is the answer
   when that side has not answered NO by then: waiting longer lost the
   answer whenever proving safety took the whole budget, as on string
   scans.  A termination question the steps decline is MAYBE before the
   safety side runs; a safety question they decline only means that no
   violation is reported.  The llvm2lts route only. *)
let run_term_memsafe (cfg : Config.t) ~data_model ~solver_config src =
  let open Or_error.Monad_infix in
  (match cfg.route with
  | Llvm2lts -> Ok ()
  | Direct ->
      Or_error.error_string
        "Athena: -p ctermmemsafe takes the llvm2lts route only (route \
         Llvm2lts)")
  >>= fun () ->
  normalise cfg >>= fun cfg ->
  missing_steps cfg ~direct_available:false >>= fun () ->
  with_work_dir cfg @@ fun dir ->
  let base = base_name src in
  let src = Filename_unix.realpath src in
  let side ~question ~stem =
    prepare cfg ~data_model ~question ~assume_safety:true ~dir ~stem ~src
  in
  side ~question:Q_termination ~stem:(base ^ "_term") >>= function
  | Declined reason | Ir_file { file = reason; _ } -> Ok (`Unknown reason)
  | Holds_unchecked -> Ok (`Unknown "no check was placed")
  | Lts_file term -> (
      side ~question:Q_memory_safety ~stem:(base ^ "_safety") >>= fun safety ->
      let start problem (file, bv_mode) ~out =
        Process.spawn_session Sys_unix.executable_name
          [ "-c"; solver_config; "-p";
            (if bv_mode then problem ^ "bv" else problem); file ]
          ~stdout:out
      in
      let term_out = dir ^/ "ltsterm.out" and safe_out = dir ^/ "ltssafe.out" in
      let term_pid = start "ltsterm" (term.file, term.bv_mode) ~out:term_out in
      let safe_pid =
        match safety with
        | Lts_file { file; bv_mode } ->
            Some (start "ltssafe" (file, bv_mode) ~out:safe_out)
        | Declined reason | Ir_file { file = reason; _ } ->
            prerr_endline
              ("the safety side was not translated, so no violation is \
                reported: " ^ reason);
            None
        | Holds_unchecked -> None
      in
      let live = ref (term_pid :: Option.to_list safe_pid) in
      let stop pid =
        Process.stop pid;
        live := List.filter !live ~f:(fun p -> p <> pid)
      in
      let ended pid =
        Process.ended pid
        && (live := List.filter !live ~f:(fun p -> p <> pid);
            true)
      in
      let decided term = String.equal term "YES" || String.equal term "NO" in
      let deadline =
        Option.map cfg.safety_wait_s ~f:(fun s -> started +. Float.of_int s)
      in
      Exn.protect
        ~finally:(fun () -> List.iter !live ~f:Process.stop)
        ~f:(fun () ->
          let rec loop ~term_done ~safe_done ~safe_result =
            let safe_done, safe_result =
              match safe_pid with
              | Some pid when (not safe_done) && ended pid ->
                  ( true,
                    List.hd (String.split (last_line safe_out) ~on:',')
                    |> Option.value ~default:"" )
              | _ -> (safe_done, safe_result)
            in
            if String.equal safe_result "NO" then (
              if not term_done then stop term_pid;
              `Unsafe)
            else
              let term_done = term_done || ended term_pid in
              let safe_done =
                if term_done && (not safe_done) && not (decided (last_line term_out))
                then (
                  Option.iter safe_pid ~f:stop;
                  true)
                else safe_done
              in
              if term_done && safe_done then `Term
              else if
                term_done
                && Option.exists deadline ~f:(fun d ->
                       Float.(Core_unix.gettimeofday () >= d))
              then (
                prerr_endline
                  "the safety side has no answer by the deadline; giving the \
                   termination answer";
                Option.iter safe_pid ~f:stop;
                `Term)
              else (
                Caml_unix.sleepf 0.2;
                loop ~term_done ~safe_done ~safe_result)
          in
          match
            loop ~term_done:false ~safe_done:(Option.is_none safe_pid)
              ~safe_result:""
          with
          | `Unsafe ->
              prerr_endline
                "MAYBE: a memory-safety violation is reachable (ltssafe \
                 answered NO)";
              Ok `Unsafe
          | `Term ->
              let term = last_line term_out in
              Ok (if decided term then `Answer term else `Answer "MAYBE")))
