(* Command-line options of the Ptr2Arr plugin.

   The plugin is run either as [frama-c -ptr2arr ...] or through the standalone
   [ptr2arr] executable, which translates its own command line into these
   options (see bin/ptr2arr.ml).

   Which options may be combined is decided by what the user wrote (see
   [Driver.check_options]): an option given its default value still counts as
   given ([is_set]), and an option given twice with different values is an
   error rather than the last one silently winning ([command_line_values]). *)

include Plugin.Register (struct
  let name = "Ptr2Arr"
  let shortname = "ptr2arr"
  let help = "replace pointers by indices into per-region arrays (C to C)"
end)

(* The arguments of a -commands-file, read as Frama-C 33 reads them
   (Cmdline.expand_commands_file): one per line, a line starting with # left
   out, a line ending with a backslash joined to the next, and each line an
   option name followed, after a space or '=', by its value, which loses its
   surrounding quotes; the option is rewritten -name=value. A file that cannot
   be read gives nothing (Frama-C then stops on it itself). *)
let commands_file path =
  let module S = Stdlib.String in
  match Arg.read_arg path with
  | exception Sys_error _ -> []
  | lines ->
      let comment l =
        let l = S.trim l in
        S.length l > 0 && S.get l 0 = '#'
      in
      let joined =
        Array.fold_right
          (fun l acc ->
            if comment l then acc
            else
              let n = S.length l in
              if n > 0 && S.get l (n - 1) = '\\' then
                let l = S.sub l 0 (n - 1) in
                match acc with hd :: tl -> (l ^ hd) :: tl | [] -> [ l ]
              else l :: acc)
          lines []
      in
      List.filter_map
        (fun l ->
          let l = S.trim l in
          let n = S.length l in
          let rec name_end i =
            if i < n && S.get l i <> ' ' && S.get l i <> '=' then name_end (i + 1) else i
          in
          let e = name_end 0 in
          if e = 0 then None
          else
            let value =
              if e >= n then ""
              else
                let v = S.sub l (e + 1) (n - e - 1) in
                let m = S.length v in
                let v =
                  if m >= 2 && S.get v 0 = '"' && S.contains (S.sub v 1 (m - 1)) '"' then
                    S.sub v 1 (S.rindex v '"' - 1)
                  else v
                in
                S.trim v
            in
            let name = S.sub l 0 e in
            Some (if value = "" then name else name ^ "=" ^ value))
        joined

(* The command line of each run of the plugins: the arguments after the
   program name, with every -commands-file replaced by its arguments, cut at
   each -then, -then-last, -then-replace and -then-on PROJECT, each of which
   starts the next run. *)
let runs () =
  let starts_with p s =
    Stdlib.String.length s >= Stdlib.String.length p
    && Stdlib.String.sub s 0 (Stdlib.String.length p) = p
  in
  let rec expand = function
    | [] -> []
    | "-commands-file" :: f :: rest -> expand (commands_file f @ rest)
    | a :: rest when starts_with "-commands-file=" a ->
        let n = Stdlib.String.length "-commands-file=" in
        expand (commands_file (Stdlib.String.sub a n (Stdlib.String.length a - n)) @ rest)
    | a :: rest -> a :: expand rest
  in
  let rec cut cur acc = function
    | [] -> List.rev (List.rev cur :: acc)
    | "-then-on" :: _ :: rest -> cut [] (List.rev cur :: acc) rest
    | a :: rest when a = "-then" || a = "-then-last" || a = "-then-replace" || starts_with "-then-on=" a ->
        cut [] (List.rev cur :: acc) rest
    | a :: rest -> cut (a :: cur) acc rest
  in
  cut [] [] (expand (List.tl (Array.to_list Sys.argv)))

(* The values the option [name] is given in run [run] (0 for the first, one
   more after each -then), in order and each once: a boolean option's
   occurrences read as "true", its opposite's ([-ptr2arr-no-...], or
   [-no-ptr2arr]) as "false". The parameters do not keep this: setting one to
   the value it already has calls no hook, so the option given first its
   default and then another value would look given once. Values are compared
   as written: the same file under two spellings is two values. *)
let command_line_values ~run ~bool name =
  let prefix = "-ptr2arr-" in
  let negation =
    if name = "-ptr2arr" then "-no-ptr2arr"
    else
      let n = Stdlib.String.length prefix in
      prefix ^ "no-" ^ Stdlib.String.sub name n (Stdlib.String.length name - n)
  in
  let starts_with p s =
    Stdlib.String.length s >= Stdlib.String.length p
    && Stdlib.String.sub s 0 (Stdlib.String.length p) = p
  in
  let rec go acc = function
    | [] -> acc
    | a :: rest when bool && a = name -> go ("true" :: acc) rest
    | a :: rest when bool && a = negation -> go ("false" :: acc) rest
    | a :: v :: rest when (not bool) && a = name -> go (v :: acc) rest
    | a :: rest when (not bool) && starts_with (name ^ "=") a ->
        let n = Stdlib.String.length name + 1 in
        go (Stdlib.String.sub a n (Stdlib.String.length a - n) :: acc) rest
    | _ :: rest -> go acc rest
  in
  let args = match List.nth_opt (runs ()) run with Some a -> a | None -> [] in
  List.fold_left
    (fun acc v -> if List.mem v acc then acc else acc @ [ v ])
    [] (List.rev (go [] args))

(* How the user wrote a boolean option in run [run]: its opposite's name
   when only the opposite was given, so that a message names what was
   written. *)
let spelling ~run ~bool name =
  if bool && command_line_values ~run ~bool name = [ "false" ] then
    if name = "-ptr2arr" then "-no-ptr2arr"
    else "-ptr2arr-no-" ^ Stdlib.String.sub name 9 (Stdlib.String.length name - 9)
  else name

module Enabled = False (struct
  let option_name = "-ptr2arr"
  let help = "run the transformation on the input files"
end)

module Mode = String (struct
  let option_name = "-ptr2arr-mode"
  let arg_name = "normal|memory-safety|memory-cleanup|assume-safety"
  let default = "normal"
  let help =
    "normal: no checks; memory-safety: a violation of valid-deref, valid-free \
     or valid-memtrack (checked at the ends of the execution) calls the \
     marker of its property (see -ptr2arr-violation-markers); \
     memory-cleanup: the same for valid-deref and valid-free, and a heap \
     block left allocated at an end of the execution calls the marker of \
     valid-memcleanup; assume-safety: execution stops at the first \
     violation of valid-deref or valid-free"
end)

module Violation_markers = String (struct
  let option_name = "-ptr2arr-violation-markers"
  let arg_name = "split|reach-error"
  let default = "split"
  let help =
    "with -ptr2arr-mode memory-safety or memory-cleanup: split: a violation \
     of valid-deref, valid-free, valid-memtrack and valid-memcleanup calls \
     __p2a_violation_valid_deref(), __p2a_violation_valid_free(), \
     __p2a_violation_valid_memtrack() and \
     __p2a_violation_valid_memcleanup(), defined in the output as _Exit(77) \
     to _Exit(80), and the input's own reach_error is an ordinary function; \
     reach-error: every violation calls reach_error() (the properties are \
     not told apart) and the input's own reach_error is renamed"
end)

module Memtrack_check = String (struct
  let option_name = "-ptr2arr-memtrack-check"
  let arg_name = "guess|fixpoint|none"
  let default = "guess"
  let help =
    "with -ptr2arr-mode memory-safety (or memory-cleanup with \
     -ptr2arr-memtrack-nonterminating), how valid-memtrack is checked: guess: a set of heap blocks is chosen \
     nondeterministically (the weak function __p2a_guess) and checked in one \
     pass to be unreachable from the roots; fixpoint: the blocks reachable \
     from the roots are computed (deterministic, for testing); none: \
     valid-memtrack is not checked (memory-safety then checks valid-deref and \
     valid-free only, for a downstream to which a leak does not matter)"
end)

module Data_model = String (struct
  let option_name = "-ptr2arr-data-model"
  let arg_name = "LP64|ILP32"
  let default = "LP64"
  let help =
    "the data model the input is read in: LP64 reads it with -machdep \
     gcc_x86_64 and the preprocessor's -m64, ILP32 with -machdep gcc_x86_32 \
     and -m32 (without -m32 the system headers would be read as 64-bit \
     ones); when the option is not given the front end's settings are kept"
end)

module Memtrack_nonterminating = False (struct
  let option_name = "-ptr2arr-memtrack-nonterminating"
  let help =
    "with -ptr2arr-mode memory-safety or memory-cleanup: also check \
     valid-memtrack where an execution that does not halt passes (every \
     function's entry and every loop's head), when a nondeterministic choice \
     (the weak function __p2a_probe) says so; the execution then stops \
     (__p2a_stop, _Exit(0)) unless the check reports a violation (in \
     memory-cleanup, of valid-memcleanup)"
end)

module Output = Empty_string (struct
  let option_name = "-ptr2arr-output"
  let arg_name = "file"
  let help = "where to write the transformed C (default: <stem>_Ptr2Arr.c)"
end)

module Record = Empty_string (struct
  let option_name = "-ptr2arr-record"
  let arg_name = "file"
  let help =
    "where to write the transformation record (default: <output stem>.p2a.json)"
end)

module Input_name = Empty_string (struct
  let option_name = "-ptr2arr-input-name"
  let arg_name = "file"
  let help =
    "the input's name for the record and the source map, when the file read is \
     a copy of it (the standalone executable reads a copy of an ILP32 \
     preprocessed input without its unused max_align_t)"
end)

module Unsupported = String (struct
  let option_name = "-ptr2arr-unsupported"
  let arg_name = "error|warn"
  let default = "error"
  let help =
    "error: on an unsupported construct write nothing and fail; warn: write \
     what can be transformed (for investigation only, no correctness claim)"
end)

module Region_size = Int (struct
  let option_name = "-ptr2arr-region-size"
  let arg_name = "N"
  let default = 100000
  let help = "length of each region array"
end)

module Scalar_cells = False (struct
  let option_name = "-ptr2arr-scalar-cells"
  let help =
    "hold in one scalar each region whose only object is one alloca cell of \
     an integer type that main allocates outside every loop and no pointer \
     moves away from or out of: a consumer then needs no invariant about \
     an array for it"
end)

module Unbounded_regions = False (struct
  let option_name = "-ptr2arr-unbounded-regions"
  let help =
    "read every region array as having no length: no index is compared with \
     it, so no allocation exhausts a region and no check fails on a block \
     past its end. For a consumer whose arrays have no length (llvm2lts); \
     the output is not meant to be run as C"
end)

module Points_to = String (struct
  let option_name = "-ptr2arr-points-to"
  let arg_name = "steens|alias|eva"
  let default = "steens"
  let help = "points-to analysis used to build the region partition"
end)

module Wrap_integers = False (struct
  let option_name = "-ptr2arr-wrap-integers"
  let help =
    "make fixed-width integer wrap-around explicit for a consumer that reads \
     integers as mathematical integers"
end)

module Wrap_integers_kind = String (struct
  let option_name = "-ptr2arr-wrap-integers-kind"
  let arg_name = "unsigned|all"
  let default = "unsigned"
  let help =
    "with -ptr2arr-wrap-integers: unsigned: the unsigned operations wrap and \
     a signed one is assumed not to overflow; all: the signed +, - and * \
     wrap too (two's complement, as gcc -fwrapv), computed in the unsigned \
     type of the same width and converted back"
end)

module Integers = String (struct
  let option_name = "-ptr2arr-integers"
  let arg_name = "auto"
  let default = ""
  let help =
    "auto: scan the program first and choose how its integers are read: at \
     fixed width when it has a bitwise operation a mathematical reading cannot \
     write exactly, otherwise as mathematical integers, with the reductions of \
     -ptr2arr-wrap-integers placed only where the value analysis (Eva) cannot \
     show the exact value in range"
end)

module Integers_eva = String (struct
  let option_name = "-ptr2arr-integers-eva"
  let arg_name = "on|off"
  let default = "on"
  let help =
    "with -ptr2arr-integers auto: off: no value analysis, every reduction is \
     kept and bitwise operations are judged by their syntax alone"
end)

module Check_overflow = False (struct
  let option_name = "-ptr2arr-check-overflow"
  let help =
    "call reach_error() right before a signed integer operation whose \
     result is outside the range of its type (SV-COMP's no-overflow); the \
     input's own reach_error is renamed"
end)

module Uninit = String (struct
  let option_name = "-ptr2arr-uninit"
  let arg_name = "keep|check|nondet"
  let default = "keep"
  let help =
    "what an uninitialised automatic local variable means in the output: \
     keep: as in the input (the output declares it without an initialiser); \
     check: reading one whose address is never taken (an element of an \
     array or a field of a structure too) before it is written, which C11 \
     leaves undefined, calls reach_error() (the input's own reach_error \
     renamed), or in a safety mode __p2a_violation_uninit_read() (status 82) \
     or reach_error() as -ptr2arr-violation-markers says, and ends an \
     --assume-safety execution; nondet: each one starts with a \
     nondeterministic value of its type (a pointer NULL), drawn from weak \
     functions __p2a_uninit_<type>() that return __VERIFIER_nondet_<type>()"
end)

module Line_directives = False (struct
  let option_name = "-ptr2arr-line-directives"
  let help =
    "precede every statement of the printed program with a #line line: the \
     line of the input statement it comes from, in the input file, or the \
     next line of the output itself for a statement that comes from none \
     (the record's source map counts physical lines either way)"
end)

module Identity = False (struct
  let option_name = "-ptr2arr-identity"
  let help =
    "do not replace pointers: print the normalised program only (used to test \
     the checking tools on a transformation that is trivially correct)"
end)

(* Exit statuses of the plugin. Frama-C itself uses 1 (user error), 2
   (interrupted), 3 (unsupported feature), 4 (fatal) and 125 (internal error),
   so the plugin reports its own outcomes with codes Frama-C never uses; the
   standalone executable maps them back to the documented statuses 2 and 3. *)
let exit_unsupported = 64
let exit_unsupported_written = 65

module Check = False (struct
  let option_name = "-ptr2arr-check"
  let help =
    "instead of transforming, check that the input is a well-formed output \
     (readable, self-contained, no pointer left)"
end)

module Check_allow_pointers = False (struct
  let option_name = "-ptr2arr-check-allow-pointers"
  let help = "with -ptr2arr-check: do not report pointers (for identity outputs)"
end)

let exit_check_failed = 66

module Monitor = False (struct
  let option_name = "-ptr2arr-monitor"
  let help =
    "instead of transforming, write the input instrumented to check at run \
     time that every dereferenced pointer reaches an object of the region the \
     analysis gives it"
end)

module Z_reading = False (struct
  let option_name = "-ptr2arr-z-reading"
  let help =
    "instead of transforming, write the input (an output of \
     -ptr2arr-wrap-integers) with its integers widened to 128 bits, its \
     integer conversions dropped and its reductions computed: a test of the \
     reading where integers are mathematical"
end)

