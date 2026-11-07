(* The [ptr2arr] command line, shared by the standalone executable (bin/) and
   by any program that links the transformation in (CoAR's main.exe, which
   runs it on its way from a C program to a verdict).

   usage: ptr2arr [--memory-safety | --memory-cleanup | --assume-safety] [-o OUT.c]
                  [options] IN.c
          ptr2arr --check [--allow-pointers] OUT.c

   An option may be given only with an action that uses it (see [allowed]),
   and only once or with the same value again; anything else is an error
   (status 1), so that no option is silently ignored or overridden.

   Frama-C reads its command line once, when its kernel is initialised, so a
   program cannot hand it a rewritten command line in the same process.
   Instead [run] starts the program a second time with PTR2ARR_FRAMAC_CHILD
   set: that child is the Frama-C kernel with the plugin linked in
   ([boot_child]), given the plugin's options and the front-end settings
   below. [run] maps the child's exit status to the documented one:
     0  the output and the record were written
     1  the input cannot be read, an option is invalid, or an internal error
     2  the input has an unsupported construct; nothing was written
     3  --unsupported=warn wrote the output despite unsupported constructs
     4  (--check) the file is readable but violates an output property
   The child's standard output (Frama-C's progress messages) goes to standard
   error, so that the transformation prints nothing on standard output. *)

(* Raised once a usage message or the reason an option is refused has been
   printed on standard error; the status to end with. *)
exception Exit_with of int

let child_var = "PTR2ARR_FRAMAC_CHILD"

(* Front-end settings: the system's headers rather than Frama-C's libc, so that
   macros such as assert expand as the compiler expands them; a GCC machine
   description, which those headers need for their GCC extensions, chosen by
   the data model (gcc_x86_64 for LP64, gcc_x86_32 for ILP32); an assert
   declared by the program itself is a warning rather than an error; variadic
   calls are kept as written; and no other plugin is loaded. Frama-C
   preprocesses in strict C11, where glibc's headers hide their GNU
   declarations (stdlib.h then does not declare alloca, and a call to it is
   read as an implicitly declared function returning int); the compilers
   default to the GNU dialect, so the preprocessor is asked for it too. The
   preprocessor is also given the data model's word size (-m64 or -m32):
   Frama-C does not derive it from the machine description, and without it
   the system headers are read as 64-bit ones under gcc_x86_32 (int64_t of
   the wrong width, size_t unsigned long). Under ILP32 the preprocessor also
   defines _GCC_MAX_ALIGN_T, the guard of gcc's stddef.h around max_align_t:
   for -m32 that structure has a __float128 member, a type the front end
   cannot read, so any input including stddef.h would be unreadable. With the
   guard max_align_t is left undefined, and an input that uses it is refused
   as unreadable rather than read with another layout (the plugin does the
   same, see -ptr2arr-data-model).

   The preprocessor is clang ([`Clang program]), so that the route from a C
   program to its LLVM IR runs one compiler, the clang that compiles the
   output; [`Gcc] keeps Frama-C's own default, gcc. A clang calls itself GCC
   4.2.1 by default, and glibc's headers then declare
   _Float32 and its siblings as typedefs, which the front end reads as
   keywords, so no program including them can be read; it is told instead
   the GCC version that both machine descriptions above describe (14.2.1 in
   Frama-C 33), so that the headers take the branches they take for the
   machine Frama-C models. For the same reason it does not say it is clang:
   __clang__ and the __clang_major__/__clang_minor__/__clang_patchlevel__
   version are left undefined. glibc 2.42 (Ubuntu 25.10) chooses a header's
   branch by them as well -- under __clang__ bits/floatn.h declares a
   _Complex typedef, which the front end refuses, and under a clang version
   it declares _Float128 as a typedef of __float128 -- so with them every
   program including stdlib.h was unreadable there, while glibc 2.39 read
   the same way with or without them. Its own headers (limits.h,
   stddef.h, ...) then stand for gcc's: the values are the same, the spelling
   of a constant may differ (2147483647 for 0x7fffffff). *)
let frontend_args ~cpp model =
  let machdep, cpp_args =
    if model = "ILP32" then ("gcc_x86_32", "-m32,-D_GCC_MAX_ALIGN_T")
    else ("gcc_x86_64", "-m64")
  in
  [ "-machdep"; machdep; "-no-frama-c-stdlib";
    "-kernel-warn-key"; "CERT:MSC:38=active"; "-no-variadic-translation";
    "-no-autoload-plugins"; "-cpp-extra-args=-std=gnu11," ^ cpp_args ]
  @
  match cpp with
  | `Gcc -> []
  | `Clang clang ->
      [ "-cpp-command";
        Filename.quote clang
        ^ " -C -E -I. -fgnuc-version=14.2.1 -U__clang__ -U__clang_major__ \
           -U__clang_minor__ -U__clang_patchlevel__";
        "-cpp-frama-c-compliant" ]

(* An ILP32 input that is already preprocessed (.i) holds the max_align_t
   of gcc's stddef.h for -m32, with a __float128 member the front end cannot
   read, and _GCC_MAX_ALIGN_T (see frontend_args) cannot keep it out of text
   that is not preprocessed again. When nothing else in the file names
   max_align_t, the child reads a copy with that typedef blanked out, every
   other character, newline and column kept: the result is what the input
   would have been with _GCC_MAX_ALIGN_T, so the two kinds of input are read
   alike (an input that uses max_align_t stays unreadable). The copy is in a
   temporary directory, removed when the child ends; the record and the
   source map name the input. *)
let temp_dir = ref None

let occurrences text word =
  let n = String.length word and m = String.length text in
  let rec go i acc =
    if i + n > m then acc
    else if String.sub text i n = word then go (i + n) (acc + 1)
    else go (i + 1) acc
  in
  go 0 0

let find_from text sub i =
  let n = String.length sub and m = String.length text in
  let rec go i = if i + n > m then None else if String.sub text i n = sub then Some i else go (i + 1) in
  go i

let rfind_before text sub stop =
  let n = String.length sub in
  let rec go i = if i < 0 then None else if i + n <= stop && String.sub text i n = sub then Some i else go (i - 1) in
  go (stop - n)

let without_max_align_t model input =
  if model <> "ILP32" || not (Filename.check_suffix input ".i") then input
  else
    match In_channel.with_open_bin input In_channel.input_all with
    | exception Sys_error _ -> input
    | text -> (
        let close = "} max_align_t;" in
        match find_from text close 0 with
        | Some j when occurrences text "max_align_t" = 1 -> (
            match rfind_before text "typedef struct" j with
            | Some i
              when (match find_from text "__float128" i with Some k -> k < j | None -> false)
                   && not (String.contains (String.sub text (i + 1) (j - i - 1)) '}') ->
                let stop = j + String.length close in
                let b = Bytes.of_string text in
                for k = i to stop - 1 do
                  if Bytes.get b k <> '\n' then Bytes.set b k ' '
                done;
                let dir = Filename.temp_dir "ptr2arr" "" in
                temp_dir := Some dir;
                let copy = Filename.concat dir (Filename.basename input) in
                Out_channel.with_open_bin copy (fun oc -> Out_channel.output_bytes oc b);
                copy
            | _ -> input)
        | _ -> input)

let remove_temp_dir () =
  match !temp_dir with
  | None -> ()
  | Some dir ->
      (* a program may run the transformation more than once *)
      temp_dir := None;
      (try
         Array.iter
           (fun f -> try Sys.remove (Filename.concat dir f) with Sys_error _ -> ())
           (Sys.readdir dir)
       with Sys_error _ -> ());
      (try Sys.rmdir dir with Sys_error _ -> ())

let usage () =
  prerr_string
    "usage: ptr2arr [--memory-safety | --memory-cleanup | --assume-safety] [-o OUT.c]\n\
    \               [options] IN.c\n\
     options:\n\
    \  --record=FILE          where to write the transformation record\n\
    \  --unsupported=error|warn\n\
    \  --region-size=N        length of each region array (default 100000)\n\
    \  --unbounded-regions    read the region arrays as having no length (no\n\
    \                         exhaustion, no comparison with it), for a\n\
    \                         consumer whose arrays have none (llvm2lts)\n\
    \  --scalar-cells         hold a region of one alloca cell main allocates\n\
    \                         once in a scalar instead of an array\n\
    \  --points-to=steens|alias|eva\n\
    \  --wrap-integers[=unsigned|all]\n\
    \                         make integer wrap-around explicit: unsigned\n\
    \                         operations only (default), or signed ones too\n\
    \  --integers=auto        choose the integer reading per input: fixed width\n\
    \                         if a bitwise operation needs it, else wrap-around\n\
    \                         made explicit where Eva cannot show it absent\n\
    \  --integers-eva=on|off  with --integers=auto: use the value analysis (on)\n\
    \  --check-overflow       call reach_error() right before a signed\n\
    \                         operation that overflows (normal mode only)\n\
    \  --violation-markers=split|reach-error\n\
    \                         with --memory-safety or --memory-cleanup: one\n\
    \                         marker per property (default), or reach_error()\n\
    \                         for every violation\n\
    \  --memtrack-check=guess|fixpoint|none\n\
    \                         how valid-memtrack is checked (default guess;\n\
    \                         fixpoint is deterministic, for testing; none:\n\
    \                         not at all, valid-deref and valid-free only)\n\
    \  --memtrack-nonterminating\n\
    \                         also check valid-memtrack where an execution\n\
    \                         that does not halt passes\n\
    \  --uninit=keep|check|nondet\n\
    \                         uninitialised local variables: as in the input\n\
    \                         (default), a read of one whose address is not\n\
    \                         taken reaches a marker, or each starts with a\n\
    \                         nondeterministic value of its type\n\
    \  --line-directives      precede every printed statement with a #line line\n\
    \                         naming its input line (or the output's own line)\n\
    \  --data-model=LP64|ILP32\n\
    \                         the data model the input is read in (default LP64)\n\
    \  --identity             print the normalised program only (testing)\n\
    \  --monitor              write the input instrumented with the region monitor\n\
    \  --z-reading            write an output of --wrap-integers as run with\n\
    \                         mathematical integers (128-bit), for testing\n\
    \  --clang=PROGRAM        the clang that preprocesses the input (default clang-19)\n\
    \  --gcc                  preprocess the input with gcc instead of clang\n\
    \  --frama-c=ARGS         extra arguments for the Frama-C kernel\n\
     ptr2arr --check [--allow-pointers] OUT.c checks an output instead\n";
  raise (Exit_with 1)

let split_words s =
  List.filter (fun w -> w <> "") (String.split_on_char ' ' s)

let value_of prefix arg =
  let n = String.length prefix in
  if String.length arg > n && String.sub arg 0 n = prefix then
    Some (String.sub arg n (String.length arg - n))
  else None

let fail fmt =
  Printf.ksprintf (fun s -> prerr_endline ("ptr2arr: " ^ s); raise (Exit_with 1)) fmt

(* The options of the command line that take a value, under their own names,
   with the plugin option each becomes. *)
let valued =
  [ ("-o", "-ptr2arr-output"); ("--record", "-ptr2arr-record");
    ("--unsupported", "-ptr2arr-unsupported"); ("--region-size", "-ptr2arr-region-size");
    ("--points-to", "-ptr2arr-points-to");
    ("--violation-markers", "-ptr2arr-violation-markers");
    ("--memtrack-check", "-ptr2arr-memtrack-check");
    ("--data-model", "-ptr2arr-data-model"); ("--wrap-integers", "-ptr2arr-wrap-integers");
    ("--uninit", "-ptr2arr-uninit"); ("--integers", "-ptr2arr-integers");
    ("--integers-eva", "-ptr2arr-integers-eva");
    ("--frama-c", ""); ("--clang", "") ]

(* The flags, with the plugin option each becomes. *)
let flags =
  [ ("--wrap-integers", "-ptr2arr-wrap-integers"); ("--check", "-ptr2arr-check");
    ("--check-overflow", "-ptr2arr-check-overflow");
    ("--unbounded-regions", "-ptr2arr-unbounded-regions");
    ("--scalar-cells", "-ptr2arr-scalar-cells");
    ("--memtrack-nonterminating", "-ptr2arr-memtrack-nonterminating");
    ("--allow-pointers", "-ptr2arr-check-allow-pointers");
    ("--line-directives", "-ptr2arr-line-directives");
    ("--identity", "-ptr2arr-identity"); ("--monitor", "-ptr2arr-monitor");
    ("--z-reading", "-ptr2arr-z-reading"); ("--gcc", "") ]

(* What each action accepts besides itself; any other option given with it is
   an error, so that no option is silently ignored. The plugin checks the same
   combinations under its own names (src/driver.ml). --uninit goes with every
   action, but only the transformation takes a value other than keep. Every
   action that prints a program takes --line-directives. *)
let allowed = function
  | "transform" ->
      [ "--memory-safety"; "--memory-cleanup"; "--assume-safety"; "--violation-markers";
        "--memtrack-check"; "--memtrack-nonterminating"; "--wrap-integers"; "--check-overflow";
        "--integers"; "--integers-eva"; "-o"; "--record"; "--unsupported"; "--region-size"; "--unbounded-regions"; "--scalar-cells"; "--points-to"; "--frama-c"; "--clang"; "--gcc";
        "--data-model"; "--uninit"; "--line-directives" ]
  | "--check" -> [ "--allow-pointers"; "--frama-c"; "--clang"; "--gcc"; "--data-model"; "--uninit" ]
  | "--monitor" ->
      [ "-o"; "--record"; "--unsupported"; "--frama-c"; "--clang"; "--gcc"; "--data-model"; "--points-to"; "--uninit";
        "--line-directives" ]
  | _ (* --identity, --z-reading *) ->
      [ "-o"; "--record"; "--unsupported"; "--frama-c"; "--clang"; "--gcc"; "--data-model"; "--uninit";
        "--line-directives" ]

let parse args =
  (* option -> value, in the order first given; a flag's value is "" *)
  let given = ref [] and input = ref None in
  let set name v =
    (* an integer is one value however it is written *)
    let same a b =
      a = b
      || name = "--region-size"
         && int_of_string_opt a <> None
         && int_of_string_opt a = int_of_string_opt b
    in
    match List.assoc_opt name !given with
    | Some v' when not (same v' v) ->
        fail "%s given twice with different values (%s, %s)" name v' v
    | Some _ -> ()
    | None -> given := !given @ [ (name, v) ]
  in
  let modes = [ "--memory-safety"; "--memory-cleanup"; "--assume-safety" ] in
  let set_mode m =
    List.iter
      (fun other ->
        if other <> m && List.mem_assoc other !given then
          fail "%s and %s exclude each other" other m)
      modes;
    set m ""
  in
  let rec go = function
    | [] -> ()
    | m :: r when List.mem m modes -> set_mode m; go r
    | "-o" :: o :: r -> set "-o" o; go r
    | ("-h" | "--help") :: _ -> usage ()
    | "--wrap-integers" :: r -> set "--wrap-integers" "unsigned"; go r
    | a :: r when List.mem_assoc a flags -> set a ""; go r
    | a :: r -> (
        match
          List.find_map
            (fun (name, _) ->
              if name = "-o" then None
              else Option.map (fun v -> (name, v)) (value_of (name ^ "=") a))
            valued
        with
        | Some (name, v) -> set name v; go r
        | None ->
            if String.length a > 0 && a.[0] = '-' then begin
              Printf.eprintf "ptr2arr: unknown option %s\n" a;
              usage ()
            end
            else if !input <> None then fail "exactly one input file is expected"
            else begin
              input := Some a;
              go r
            end)
  in
  go args;
  let given = !given in
  let has name = List.mem_assoc name given in
  let value name = List.assoc_opt name given in
  let input = match !input with Some i -> i | None -> usage () in
  (match value "--violation-markers" with
   | None | Some ("split" | "reach-error") -> ()
   | Some v -> fail "invalid --violation-markers=%s (expected split or reach-error)" v);
  (match value "--unsupported" with
   | None | Some ("error" | "warn") -> ()
   | Some v -> fail "invalid --unsupported=%s (expected error or warn)" v);
  (match value "--points-to" with
   | None | Some ("steens" | "alias" | "eva") -> ()
   | Some v -> fail "invalid --points-to=%s (expected steens, alias or eva)" v);
  (match value "--region-size" with
   | None -> ()
   | Some v -> (
       match int_of_string_opt v with
       | None -> fail "invalid --region-size=%s (expected an integer)" v
       | Some n when n < 2 -> fail "--region-size must be at least 2 (index 0 is NULL)"
       | Some _ -> ()));
  let model =
    match value "--data-model" with
    | None -> "LP64"
    | Some (("LP64" | "ILP32") as m) -> m
    | Some v -> fail "invalid --data-model=%s (expected LP64 or ILP32)" v
  in
  let action =
    match List.filter has [ "--check"; "--identity"; "--monitor"; "--z-reading" ] with
    | [] -> "transform"
    | [ a ] -> a
    | l -> fail "%s exclude each other" (String.concat " and " l)
  in
  List.iter
    (fun (name, _) ->
      if name <> action && not (List.mem name (allowed action)) then
        fail "%s is not used with %s" name
          (if action = "transform" then "the transformation" else action))
    given;
  if has "--violation-markers" && not (has "--memory-safety" || has "--memory-cleanup") then
    fail "--violation-markers is used only with --memory-safety or --memory-cleanup";
  (match value "--wrap-integers" with
   | None | Some ("unsigned" | "all") -> ()
   | Some v -> fail "invalid --wrap-integers=%s (expected unsigned or all)" v);
  (match value "--integers" with
   | None | Some "auto" -> ()
   | Some v -> fail "invalid --integers=%s (expected auto)" v);
  (match value "--integers-eva" with
   | None | Some ("on" | "off") -> ()
   | Some v -> fail "invalid --integers-eva=%s (expected on or off)" v);
  if has "--integers" && has "--wrap-integers" then
    fail "--integers and --wrap-integers exclude each other";
  if has "--integers-eva" && not (has "--integers") then
    fail "--integers-eva is used only with --integers=auto";
  if has "--check-overflow" then begin
    List.iter
      (fun m -> if has m then fail "--check-overflow and %s exclude each other" m)
      [ "--memory-safety"; "--memory-cleanup"; "--assume-safety" ];
    if value "--wrap-integers" = Some "all" then
      fail "--check-overflow and --wrap-integers=all exclude each other"
  end;
  (match value "--uninit" with
   | None | Some ("keep" | "check" | "nondet") -> ()
   | Some v -> fail "invalid --uninit=%s (expected keep, check or nondet)" v);
  (match value "--uninit" with
   | Some (("check" | "nondet") as v) when action <> "transform" ->
       fail "--uninit=%s is not used with %s" v action
   | Some "check" when has "--check-overflow" ->
       fail "--uninit=check and --check-overflow exclude each other"
   | _ -> ());
  (match value "--memtrack-check" with
   | None | Some ("guess" | "fixpoint") -> ()
   | Some "none" when has "--memory-safety" && not (has "--memtrack-nonterminating") -> ()
   | Some "none" ->
       fail "--memtrack-check=none is used only with --memory-safety and without --memtrack-nonterminating"
   | Some v -> fail "invalid --memtrack-check=%s (expected guess, fixpoint or none)" v);
  if has "--memtrack-nonterminating" && not (has "--memory-safety" || has "--memory-cleanup") then
    fail "--memtrack-nonterminating is used only with --memory-safety or --memory-cleanup";
  if has "--memtrack-check"
     && not (has "--memory-safety" || (has "--memory-cleanup" && has "--memtrack-nonterminating"))
  then
    fail "--memtrack-check is used only with --memory-safety, or --memory-cleanup and --memtrack-nonterminating";
  let extra = match value "--frama-c" with Some v -> split_words v | None -> [] in
  (* The plugin is always told the data model, the default included, so
     that it refuses a -machdep or a word size given through --frama-c that
     disagrees with it rather than read the input in a mixed model. *)
  let given =
    if has "--data-model" then given else given @ [ ("--data-model", model) ]
  in
  let plugin =
    List.concat_map
      (fun (name, v) ->
        match (List.assoc_opt name valued, List.assoc_opt name flags) with
        | _ when name = "--wrap-integers" ->
            "-ptr2arr-wrap-integers"
            :: (if v = "all" then [ "-ptr2arr-wrap-integers-kind"; "all" ] else [])
        | Some "", _ -> [] (* --frama-c, --clang *)
        | None, Some "" -> [] (* --gcc *)
        | Some opt, _ -> [ opt; v ]
        | None, Some opt -> [ opt ]
        | None, None ->
            (* the mode *)
            [ "-ptr2arr-mode"; String.sub name 2 (String.length name - 2) ])
      given
  in
  let read = if action = "--check" then input else without_max_align_t model input in
  let cpp =
    match (value "--clang", has "--gcc") with
    | Some _, true -> fail "--clang and --gcc exclude each other"
    | _, true -> `Gcc
    | Some clang, false -> `Clang clang
    | None, false -> `Clang "clang-19"
  in
  frontend_args ~cpp model @ extra @ [ read ]
  @ (if action = "--check" then [] else [ "-ptr2arr" ])
  @ plugin
  @ (if read <> input then [ "-ptr2arr-input-name"; input ] else [])


let status_of_child = function
  | Unix.WEXITED 0 -> 0
  | Unix.WEXITED 64 -> 2
  | Unix.WEXITED 65 -> 3
  | Unix.WEXITED 66 -> 4
  | Unix.WEXITED _ | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> 1

type outcome = Exited of int | Timed_out

(* The default way to start the child: [prog] with [args] (its own name
   first) in environment [env], reading this process's standard input and
   writing both its outputs to this process's standard error. *)
let create_process prog args env =
  Unix.create_process_env prog args env Unix.stdin Unix.stderr Unix.stderr

let rec waitpid flags pid =
  try Unix.waitpid flags pid
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid flags pid

(* The child's status, or [None] when [timeout] seconds passed first: the
   child is then sent SIGTERM, as timeout(1) sends it, and reaped. *)
let wait_child ?timeout pid =
  match timeout with
  | None -> Some (snd (waitpid [] pid))
  | Some seconds ->
      let deadline = Unix.gettimeofday () +. seconds in
      let rec poll () =
        match waitpid [ Unix.WNOHANG ] pid with
        | 0, _ when Unix.gettimeofday () < deadline ->
            (try Unix.sleepf 0.05 with Unix.Unix_error (Unix.EINTR, _, _) -> ());
            poll ()
        | 0, _ ->
            (try Unix.kill pid Sys.sigterm with Unix.Unix_error _ -> ());
            ignore (waitpid [] pid);
            None
        | _, status -> Some status
      in
      poll ()

let run ?(spawn = create_process) ?(env = [||]) ?timeout ~exe args =
  let child_args = parse args in
  let env = Array.concat [ [| child_var ^ "=1" |]; env; Unix.environment () ] in
  let status =
    Fun.protect ~finally:remove_temp_dir (fun () ->
        wait_child ?timeout (spawn exe (Array.of_list (exe :: child_args)) env))
  in
  match status with Some s -> Exited (status_of_child s) | None -> Timed_out

let is_child () = Sys.getenv_opt child_var = Some "1"

(* The program must link the kernel, Eva and the plugin whole, as -linkall
   links them: the kernel and the plugin register options, hooks and builtins
   as their modules are initialised, and a module nothing names would
   otherwise be left out. The standalone executable is linked with -linkall,
   and so is any executable that depends on dune-site's plugins, as the
   kernel does. The collector settings and the recording of backtraces are
   the ones the library frama-c.init makes when Frama-C's own executables
   start: made again here, for a program that has undone them for its own
   runs (CoAR's main.exe). *)
let boot_child () =
  Gc.set
    { (Gc.get ()) with Gc.minor_heap_size = 1 lsl 18; major_heap_increment = 1 lsl 22 };
  Printexc.record_backtrace true;
  Boot.boot ()
