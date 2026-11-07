(* The plugin's entry point: check the options, read, check the fragment,
   transform, write.

   Outcome (exit status of the Frama-C process):
   - 0: the output and the record were written;
   - Options.exit_unsupported: the input has an unsupported construct (one line
     per construct on stderr) and nothing was written;
   - Options.exit_unsupported_written: as above, but -ptr2arr-unsupported=warn
     wrote the output anyway; it carries no correctness claim;
   - Frama-C's own statuses for everything else (1 for an input it cannot read,
     an invalid option or a combination of options [check_options] refuses). *)

let valid_modes = [ "normal"; "memory-safety"; "memory-cleanup"; "assume-safety" ]

type action = Transform | Check | Identity | Monitor | Z_reading

let action_name = function
  | Transform -> "the transformation"
  | Check -> Options.Check.option_name
  | Identity -> Options.Identity.option_name
  | Monitor -> Options.Monitor.option_name
  | Z_reading -> Options.Z_reading.option_name

type kind = Bool | Int | Text

(* Every option of the plugin: its name, whether it has been given on the
   command line (with any value, its default included) and its kind. *)
let all_options =
  Options.
    [ (Enabled.option_name, Enabled.is_set, Bool);
      (Mode.option_name, Mode.is_set, Text);
      (Violation_markers.option_name, Violation_markers.is_set, Text);
      (Memtrack_check.option_name, Memtrack_check.is_set, Text);
      (Memtrack_nonterminating.option_name, Memtrack_nonterminating.is_set, Bool);
      (Data_model.option_name, Data_model.is_set, Text);
      (Output.option_name, Output.is_set, Text);
      (Record.option_name, Record.is_set, Text);
      (Unsupported.option_name, Unsupported.is_set, Text);
      (Region_size.option_name, Region_size.is_set, Int);
      (Unbounded_regions.option_name, Unbounded_regions.is_set, Bool);
      (Scalar_cells.option_name, Scalar_cells.is_set, Bool);
      (Points_to.option_name, Points_to.is_set, Text);
      (Wrap_integers.option_name, Wrap_integers.is_set, Bool);
      (Wrap_integers_kind.option_name, Wrap_integers_kind.is_set, Text);
      (Check_overflow.option_name, Check_overflow.is_set, Bool);
      (Integers.option_name, Integers.is_set, Text);
      (Integers_eva.option_name, Integers_eva.is_set, Text);
      (Uninit.option_name, Uninit.is_set, Text);
      (Line_directives.option_name, Line_directives.is_set, Bool);
      (Identity.option_name, Identity.is_set, Bool);
      (Check.option_name, Check.is_set, Bool);
      (Check_allow_pointers.option_name, Check_allow_pointers.is_set, Bool);
      (Monitor.option_name, Monitor.is_set, Bool);
      (Z_reading.option_name, Z_reading.is_set, Bool) ]

let given name =
  List.exists (fun (n, is_set, _) -> n = name && is_set ()) all_options

(* The distinct values the option is given in run [run]: an integer option's
   by their value, so that 100 and 0100 are one value. *)
let distinct_values ~run (name, _, kind) =
  let vs = Options.command_line_values ~run ~bool:(kind = Bool) name in
  match kind with
  | Int ->
      List.fold_left
        (fun acc v ->
          let same w = int_of_string_opt w = int_of_string_opt v && int_of_string_opt v <> None in
          if List.exists same acc then acc else acc @ [ v ])
        [] vs
  | Bool | Text -> vs

(* The options that may be given with each action; giving any other is an
   error, so that an option is never silently ignored. These are the
   combinations the standalone executable accepts (bin/ptr2arr.ml), under the
   plugin's names: the transformation takes a mode and what shapes its
   output; the check reads an output and writes nothing; the identity, the
   monitor and the mathematical reading print a program without replacing its
   pointers, and only the monitor runs the points-to analysis. The data model
   goes with every action, and so does -ptr2arr-uninit, whose value other
   than keep only the transformation accepts ([check_options]); the #line
   lines go with every action that prints. *)
let allowed action =
  let open Options in
  Data_model.option_name :: Uninit.option_name
  ::
  (match action with
   | Transform ->
       [ Enabled.option_name; Mode.option_name; Violation_markers.option_name;
         Memtrack_check.option_name; Memtrack_nonterminating.option_name;
         Wrap_integers.option_name; Wrap_integers_kind.option_name;
         Integers.option_name; Integers_eva.option_name;
         Check_overflow.option_name; Output.option_name; Record.option_name;
         Unsupported.option_name; Region_size.option_name; Unbounded_regions.option_name;
         Scalar_cells.option_name;
         Points_to.option_name; Line_directives.option_name ]
   | Check -> [ Check.option_name; Check_allow_pointers.option_name ]
   | Identity ->
       [ Enabled.option_name; Identity.option_name; Output.option_name;
         Record.option_name; Unsupported.option_name; Line_directives.option_name ]
   | Monitor ->
       [ Enabled.option_name; Monitor.option_name; Output.option_name;
         Record.option_name; Unsupported.option_name; Points_to.option_name;
         Line_directives.option_name ]
   | Z_reading ->
       [ Enabled.option_name; Z_reading.option_name; Output.option_name;
         Record.option_name; Unsupported.option_name; Line_directives.option_name ])

(* Aborts (exit status 1) on an option given twice with different values in
   run [run], a value outside an option's range, two actions, or an option
   given with an action that does not use it. *)
let check_options ~run =
  List.iter
    (fun ((name, _, _) as o) ->
      match distinct_values ~run o with
      | _ :: _ :: _ as vs ->
          Options.abort "%s given twice with different values (%s)" name
            (String.concat ", " vs)
      | _ -> ())
    all_options;
  let mode = Options.Mode.get () in
  if not (List.mem mode valid_modes) then
    Options.abort "invalid -ptr2arr-mode %s (expected one of %s)" mode
      (String.concat ", " valid_modes);
  (match Options.Violation_markers.get () with
   | "split" | "reach-error" -> ()
   | s ->
       Options.abort "invalid -ptr2arr-violation-markers %s (expected split or reach-error)" s);
  (match Options.Memtrack_check.get () with
   | "guess" | "fixpoint" | "none" -> ()
   | s -> Options.abort "invalid -ptr2arr-memtrack-check %s (expected guess, fixpoint or none)" s);
  (match Options.Wrap_integers_kind.get () with
   | "unsigned" | "all" -> ()
   | s -> Options.abort "invalid -ptr2arr-wrap-integers-kind %s (expected unsigned or all)" s);
  (match Options.Uninit.get () with
   | "keep" | "check" | "nondet" -> ()
   | s -> Options.abort "invalid -ptr2arr-uninit %s (expected keep, check or nondet)" s);
  (match Options.Data_model.get () with
   | "LP64" | "ILP32" -> ()
   | s -> Options.abort "invalid -ptr2arr-data-model %s (expected LP64 or ILP32)" s);
  (match Options.Unsupported.get () with
   | "error" | "warn" -> ()
   | s -> Options.abort "invalid -ptr2arr-unsupported %s (expected error or warn)" s);
  (match Options.Points_to.get () with
   | "steens" | "alias" | "eva" -> ()
   | s -> Options.abort "invalid -ptr2arr-points-to %s" s);
  if Options.Region_size.get () <= 1 then
    Options.abort "-ptr2arr-region-size must be at least 2 (index 0 is NULL)";
  let action =
    match
      List.filter
        (fun (_, get) -> get ())
        [ (Check, Options.Check.get); (Identity, Options.Identity.get);
          (Monitor, Options.Monitor.get); (Z_reading, Options.Z_reading.get) ]
    with
    | [] -> Transform
    | [ (a, _) ] -> a
    | l ->
        Options.abort "%s exclude each other"
          (String.concat " and " (List.map (fun (a, _) -> action_name a) l))
  in
  List.iter
    (fun (name, is_set, kind) ->
      if is_set () && not (List.mem name (allowed action)) then
        Options.abort "%s is not used with %s"
          (Options.spelling ~run ~bool:(kind = Bool) name)
          (action_name action))
    all_options;
  (* the other actions print no transformed program, so they have no
     uninitialised variables to treat otherwise *)
  if Options.Uninit.get () <> "keep" && action <> Transform then
    Options.abort "%s %s is not used with %s" Options.Uninit.option_name
      (Options.Uninit.get ()) (action_name action);
  (* one property per run, as for the overflow check in a safety mode *)
  if Options.Uninit.get () = "check" && Options.Check_overflow.get () then
    Options.abort "%s check and %s exclude each other" Options.Uninit.option_name
      Options.Check_overflow.option_name;
  if given Options.Violation_markers.option_name
     && not (List.mem mode [ "memory-safety"; "memory-cleanup" ])
  then
    Options.abort "%s is used only with %s memory-safety or memory-cleanup"
      Options.Violation_markers.option_name Options.Mode.option_name;
  if given Options.Wrap_integers_kind.option_name && not (Options.Wrap_integers.get ()) then
    Options.abort "%s is used only with %s" Options.Wrap_integers_kind.option_name
      Options.Wrap_integers.option_name;
  (* the overflow check reports what --wrap-integers-kind all defines as
     wrapping, and SV-COMP checks one property per run: no safety mode *)
  (match Options.Integers.get () with
   | "" | "auto" -> ()
   | v -> Options.abort "invalid %s %s (expected auto)" Options.Integers.option_name v);
  (match Options.Integers_eva.get () with
   | "on" | "off" -> ()
   | v -> Options.abort "invalid %s %s (expected on or off)" Options.Integers_eva.option_name v);
  if Options.Integers.get () = "auto" && Options.Wrap_integers.get () then
    Options.abort "%s and %s exclude each other" Options.Integers.option_name
      Options.Wrap_integers.option_name;
  if given Options.Integers_eva.option_name && Options.Integers.get () <> "auto" then
    Options.abort "%s is used only with %s auto" Options.Integers_eva.option_name
      Options.Integers.option_name;
  if Options.Check_overflow.get () then begin
    if mode <> "normal" then
      Options.abort "%s is used only with %s normal" Options.Check_overflow.option_name
        Options.Mode.option_name;
    if Options.Wrap_integers.get () && Options.Wrap_integers_kind.get () = "all" then
      Options.abort "%s and %s all exclude each other" Options.Check_overflow.option_name
        Options.Wrap_integers_kind.option_name
  end;
  if given Options.Memtrack_nonterminating.option_name
     && not (List.mem mode [ "memory-safety"; "memory-cleanup" ])
  then
    Options.abort "%s is used only with %s memory-safety or memory-cleanup"
      (Options.spelling ~run ~bool:true Options.Memtrack_nonterminating.option_name)
      Options.Mode.option_name;
  (* memory-cleanup checks no memtrack at an end of the execution (a block
     lost there is found as memcleanup, since it is never released), only
     with the checks where an execution that does not halt passes *)
  if given Options.Memtrack_check.option_name
     && not
          (mode = "memory-safety"
          || (mode = "memory-cleanup" && Options.Memtrack_nonterminating.get ()))
  then
    Options.abort "%s is used only with %s memory-safety, or memory-cleanup and %s"
      Options.Memtrack_check.option_name Options.Mode.option_name
      Options.Memtrack_nonterminating.option_name;
  (* none leaves valid-memtrack unchecked, which only memory-safety checks at
     the ends; with the checks where an execution does not halt there would be
     nothing left to check *)
  if Options.Memtrack_check.get () = "none"
     && (mode <> "memory-safety" || Options.Memtrack_nonterminating.get ())
  then
    Options.abort "%s none is used only with %s memory-safety and without %s"
      Options.Memtrack_check.option_name Options.Mode.option_name
      Options.Memtrack_nonterminating.option_name

(* The data model, when -ptr2arr-data-model is given: the machine
   description, which fixes the width of every integer type, and the word
   size of the preprocessor, without which the system headers would be read
   as those of the other model (int64_t of the wrong width, size_t unsigned
   long under ILP32). Under ILP32 the preprocessor also defines
   _GCC_MAX_ALIGN_T, which keeps gcc's stddef.h from defining max_align_t:
   for -m32 it has a __float128 member, a type the front end cannot read (an
   input that uses max_align_t is then unreadable, never read with another
   layout). A -machdep or a preprocessor word size given explicitly that
   disagrees is an error. Must run before the input is parsed, which Frama-C
   does before any plugin's main function. *)
let apply_data_model () =
  if given Options.Data_model.option_name then begin
    let model = Options.Data_model.get () in
    let machdep, flag, other =
      if model = "ILP32" then ("gcc_x86_32", "-m32", "-m64")
      else ("gcc_x86_64", "-m64", "-m32")
    in
    if Kernel.Machdep.get () <> machdep then begin
      if Kernel.Machdep.is_set () then
        Options.abort "-ptr2arr-data-model %s reads the input with -machdep %s, not %s"
          model machdep (Kernel.Machdep.get ());
      Kernel.Machdep.set machdep
    end;
    let args = Kernel.CppExtraArgs.get () in
    let words = List.concat_map (String.split_on_char ' ') args in
    if List.mem other words then
      Options.abort "-ptr2arr-data-model %s preprocesses with %s, not %s" model flag other;
    let extra = if model = "ILP32" then [ flag; "-D_GCC_MAX_ALIGN_T" ] else [ flag ] in
    let missing = List.filter (fun w -> not (List.mem w words)) extra in
    if missing <> [] then Kernel.CppExtraArgs.set (args @ missing)
  end

let input_file () =
  match Kernel.Files.get () with
  | [ f ] -> f
  | [] -> Options.abort "no input file"
  | _ -> Options.abort "exactly one input file is expected"

let chop_c name =
  if Filename.check_suffix name ".c" || Filename.check_suffix name ".i" then
    Filename.chop_extension name
  else name

let output_paths input =
  let out =
    match Options.Output.get () with
    | "" -> Filename.concat "." (chop_c (Filename.basename input) ^ "_Ptr2Arr.c")
    | o -> o
  in
  let record =
    match Options.Record.get () with "" -> chop_c out ^ ".p2a.json" | r -> r
  in
  (out, record)

let exit_with code =
  Format.pp_print_flush Format.std_formatter ();
  Format.pp_print_flush Format.err_formatter ();
  Stdlib.exit code

let run_check () =
  let _ast = Ast.get () in
  let errs = Check.run ~allow_pointers:(Options.Check_allow_pointers.get ()) in
  List.iter (fun e -> Format.eprintf "ptr2arr: check: %s@." e) errs;
  if errs <> [] then exit_with Options.exit_check_failed
  else Options.feedback "check passed"

(* The plugin is asked for when -ptr2arr or -ptr2arr-check is given, with
   any value: given twice with different values, the last one false, it is
   still checked, and refused. *)
let asked () = Options.Enabled.is_set () || Options.Check.is_set ()

(* Runs of the plugins started so far: Frama-C reads the command line up to
   the next -then and runs the configuring hooks once per run. *)
let runs_configured = ref 0

(* Once a run's command line is read and before the input is parsed: the
   options are checked and the data model applied. *)
let () =
  Cmdline.run_after_configuring_stage (fun () ->
      let run = !runs_configured in
      incr runs_configured;
      if asked () then begin
        check_options ~run;
        apply_data_model ()
      end)

(* The declarations of GCC's builtin library functions called before they
   are declared are placed before the call when the plugin transforms or
   prints its input (the front end applies the pass while parsing). *)
let () = ImplicitBuiltins.enabled := fun () -> Options.Enabled.get ()

(* Once the input files are known and before they are parsed: exactly one. *)
let () =
  Cmdline.run_after_setting_files (fun files ->
      if asked () && List.length files > 1 then
        Options.abort "exactly one input file is expected")

let wrap_integers () =
  if not (Options.Wrap_integers.get ()) then None
  else if Options.Wrap_integers_kind.get () = "all" then Some Wrap.All
  else Some Wrap.Unsigned

(* What the source map needs to know of the transformation: the names'
   roles, where the checks call a marker, and whether the input's
   reach_error calls are unreach-call targets (the normal mode without the
   overflow checks, which rename it; the actions that only print a program
   are read in the normal mode). *)
let source_facts transform =
  let unreach_call = Options.Mode.get () = "normal" && not (Options.Check_overflow.get ()) in
  match transform with
  | None -> Srcmap.no_facts ~unreach_call
  | Some (_, (ctx : Transform.ctx), _) ->
      { Srcmap.roles = ctx.roles;
        violation_calls =
          List.map (fun (i, p) -> (i, Transform.property_name p)) ctx.violation_calls;
        overflow_marker = ctx.overflow_marker;
        unreach_call;
        main_return =
          List.filter_map
            (fun (sid, k) -> if k = Transform.Main_return then Some sid else None)
            ctx.end_points }

let main () =
  if Options.Check.get () then run_check ()
  else if Options.Enabled.get () then begin
    let input_path = input_file () in
    let input =
      match Options.Input_name.get () with "" -> Filepath.to_string input_path | n -> n
    in
    let _ast = Ast.get () in
    let machdep = Kernel.Machdep.get () in
    let dropped =
      if Options.Identity.get () || Options.Monitor.get () || Options.Z_reading.get () then []
      else Fragment.drop_unused_function_tables ()
    in
    List.iter (fun n -> Options.feedback "dropped the unused function table %s" n) dropped;
    (* the functions main cannot reach, dropped before anything reads the
       program (not in the actions that print their input as it is), so that
       a construct outside the fragment in one of them does not refuse it *)
    if not (Options.Identity.get () || Options.Z_reading.get ()) then
      List.iter
        (fun n -> Options.feedback "dropped the unreachable function %s" n)
        (Reach.drop_unreachable ());
    (* qsort and bsearch, which call a comparison function the program gives
       them, replaced by added functions that call it through its pointer,
       before function pointers become numbers (not in the actions that
       print their input as it is, nor in the monitor, which instruments the
       input) *)
    if not (Options.Identity.get () || Options.Monitor.get () || Options.Z_reading.get ())
    then begin
      let n = CallbackModels.run () in
      if n > 0 then Options.feedback "replaced %d calls of qsort and bsearch by their models" n
    end;
    (* function pointers, made function numbers before anything else reads
       the program (not in the identity transformation and the z-reading,
       which print their input as it is); the monitor runs on the program
       the transformation sees, so that its regions are the same *)
    let defunc_issues, defunc =
      if Options.Identity.get () || Options.Z_reading.get () then ([], Defunc.none)
      else
        match Defunc.check () with
        | [] -> ([], Defunc.run ())
        | issues -> (issues, Defunc.none)
    in
    List.iter
      (fun (n, k, _) -> Options.feedback "function %s is function number %d" n k)
      defunc.function_ids;
    (* the front end's artefacts that make the printed program one clang
       rejects, removed in every action that prints a program of its own (the
       monitor prints the input as instrumented for gcc) *)
    if not (Options.Monitor.get ()) then begin
      let folded, builtins = FrontendFixes.run () in
      if folded > 0 then
        Options.feedback "folded %d constant ifs whose dead branch reads an undeclared temporary" folded;
      if builtins > 0 then
        Options.feedback "dropped %d prototype-less builtin declarations" builtins
    end;
    (* offsetof written as the address of a member of a null pointer, made
       its translated offset before the fragment check, which would read it
       as a pointer cast to an integer (not in the printing actions, which
       print their input as it is) *)
    if not (Options.Identity.get () || Options.Monitor.get () || Options.Z_reading.get ())
    then begin
      let n = UnionFold.run () in
      if n > 0 then
        Options.feedback "made %d unions whose accessed members share one type structures" n;
      let n = Offsetof.run () in
      if n > 0 then Options.feedback "replaced %d offsetof expressions by their offsets" n;
      if Reach.drop_unused_main_params () then
        Options.feedback "dropped the parameters of main, which it does not read";
      let n = LiteralLocals.run () in
      if n > 0 then
        Options.feedback "passed %d string literals held in local variables to external functions directly" n;
      let n = VarargsDrop.run () in
      if n > 0 then
        Options.feedback "dropped the variable arguments of %d variadic functions that never read them" n;
      let n = LibModels.run () in
      if n > 0 then Options.feedback "replaced %d calls of input functions by their models" n;
      let n = PrintfStr.run () in
      if n > 0 then Options.feedback "split %d printf calls at their %%s of a program string" n;
      let n = Ptrdiff.run () in
      if n > 0 then
        Options.feedback "read %d differences of pointers converted to integers as pointer differences" n;
      let n = PtrEqual.run () in
      if n > 0 then
        Options.feedback "read %d comparisons of pointers converted to integers (and null pointers converted to integers) as pointer comparisons" n;
      let n = MainReturnCast.run () in
      if n > 0 then
        Options.feedback "made %d pointers converted to main's exit status nondeterministic integers" n;
      let n = NondetPointer.run () in
      if n > 0 then
        Options.feedback "made %d pointers converted from nondeterministic integers point to no object" n;
      let n = SetjmpDesugar.run () in
      if n > 0 then Options.feedback "wrote %d setjmp and longjmp calls and the calls between them as jumps" n
    end;
    let issues =
      let rest = ImplicitBuiltins.check () @ Fragment.check ~uninit:(Options.Uninit.get ()) () in
      if defunc_issues = [] then rest
      else
        (* the forms found are the reasons; the generic reports of the same
           function pointers add nothing *)
        defunc_issues
        @ List.filter (fun (i : Fragment.issue) -> i.kind <> "function-pointer") rest
    in
    List.iter
      (fun i -> Format.eprintf "ptr2arr: unsupported: %a@." Fragment.pretty_issue i)
      issues;
    let warn = Options.Unsupported.get () = "warn" in
    if issues <> [] && not warn then exit_with Options.exit_unsupported;
    let out, record = output_paths input in
    let size = Options.Region_size.get () in
    let prj, pairs, transform =
      let plain (prj, pairs) = (prj, pairs, None) in
      if Options.Z_reading.get () then plain (Rewrite.zreading ())
      else if Options.Monitor.get () then plain (Rewrite.monitor ())
      else if Options.Identity.get () then plain (Rewrite.identity ())
      else
        try
          let safety =
            match Options.Mode.get () with
            | "memory-safety" -> Some Transform.Memory_safety
            | "memory-cleanup" -> Some Transform.Memory_cleanup
            | "assume-safety" -> Some Transform.Assume_safety
            | _ -> None
          in
          let memtrack_check =
            match Options.Memtrack_check.get () with
            | "fixpoint" -> Transform.Fixpoint
            | _ -> Transform.Guess
          in
          let check_memtrack = Options.Memtrack_check.get () <> "none" in
          let markers =
            match Options.Violation_markers.get () with
            | "reach-error" -> Transform.Reach_error
            | _ -> Transform.Split
          in
          let prj, pairs, ctx =
            Rewrite.transform ~defunc ~size ~unbounded:(Options.Unbounded_regions.get ())
              ~scalar_cells:(Options.Scalar_cells.get ()) ~safety ~markers ~memtrack_check ~check_memtrack
              ~nonterminating:(Options.Memtrack_nonterminating.get ())
              ~wrap:(wrap_integers ()) ~check_overflow:(Options.Check_overflow.get ())
              ?integers_auto:
                (if Options.Integers.get () = "auto" then Some (Options.Integers_eva.get () = "on")
                 else None)
              ~uninit:(Options.Uninit.get ()) ()
          in
          (prj, pairs, Some (size, ctx, pairs))
        with
        | Transform.Unsupported msg ->
            Format.eprintf "ptr2arr: unsupported: %s@." msg;
            exit_with Options.exit_unsupported
        | Transform.Not_implemented msg ->
            Options.abort "not implemented yet: %s" msg
        | e when issues <> [] ->
            (* -ptr2arr-unsupported=warn: the transformation is not defined on
               the constructs reported above, and may stop on one *)
            Format.eprintf
              "ptr2arr: unsupported: the transformation stopped at an \
               unsupported construct (%s)@."
              (Printexc.to_string e);
            exit_with Options.exit_unsupported
    in
    (* the infinite constants of the program printed, which the printer
       would write as identifiers, given texts; a NaN constant is refused
       (its sign is not the one GCC gives it) *)
    let infinities = Project.on prj FrontendFixes.infinity_texts () in
    if infinities > 0 then
      Options.feedback "wrote %d infinite constants as divisions by zero" infinities;
    let nans = FrontendFixes.nan_issues () in
    List.iter (fun i -> Format.eprintf "ptr2arr: unsupported: %a@." Fragment.pretty_issue i) nans;
    if nans <> [] && not warn then exit_with Options.exit_unsupported;
    let entries =
      Srcmap.analyse ~input:input_path ~prj ~pairs (source_facts transform)
    in
    let directives = if Options.Line_directives.get () then Some (input, entries) else None in
    let printed = Srcmap.print ?directives prj out in
    Record.write record
      (Record.make ?transform ~input ~machdep
         ~source_map:(Srcmap.to_json ~input_file:input entries printed)
         ~args:(Array.to_list Sys.argv)
         ~mode:(Options.Mode.get ())
         ~wrap_integers:
           (match !IntScan.last with
            | Some { reading = Int; _ } -> Some "unsigned"
            | Some { reading = Bv; _ } -> None
            | None ->
                Option.map
                  (function Wrap.Unsigned -> "unsigned" | Wrap.All -> "all")
                  (wrap_integers ()))
         ?integers:!IntScan.last
         ~check_overflow:(Options.Check_overflow.get ())
         ~unbounded_regions:(Options.Unbounded_regions.get ()) ~dropped_globals:dropped
         ~function_ids:defunc.function_ids ~uninit:(Options.Uninit.get ()) ~output_prj:prj ~rejected:issues ());
    Options.feedback "wrote %s and %s" out record;
    if issues <> [] || nans <> [] then exit_with Options.exit_unsupported_written
  end

let () = Boot.Main.extend main
