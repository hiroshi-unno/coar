type data_model = ILP32 | LP64

let string_of_data_model = function ILP32 -> "ILP32" | LP64 -> "LP64"

type input = { llmodule : Llvm.llmodule; data_model : data_model }

(* True while an input is being parsed.  A module carrying the current
   debug-info version is verified as part of parsing, and LLVM reports a
   module that fails verification through its fatal-error handler rather than
   as a parse error. *)
let reading = ref false

let install_fatal_error_handler () =
  Llvm.install_fatal_error_handler (fun message ->
      let failure : Outcome.failure =
        if !reading then Input_error message else Internal_error message
      in
      (* CoAR's own form for a failure it reports in words: one [error: ] line
         and status 1 (main.ml) *)
      prerr_endline ("error: " ^ Outcome.to_string failure);
      Common.ProcessExit.exit 1)

let input_error fmt =
  Printf.ksprintf (fun reason -> Outcome.stop (Input_error reason)) fmt

let reject llmodule failure =
  Llvm.dispose_module llmodule;
  Outcome.stop failure

let parse ctx path =
  let buffer =
    try Llvm.MemoryBuffer.of_file path
    with Llvm.IoError message -> input_error "%s: %s" path message
  in
  (* [parse_ir] takes ownership of the buffer whether or not it succeeds. *)
  try Llvm_irreader.parse_ir ctx buffer
  with Llvm_irreader.Error message -> input_error "%s" (String.trim message)

(* The diagnostics LLVM raises while parsing.  A [Diagnostic.t] is valid only
   during the callback, so its severity and text are copied out there. *)
let parse_collecting_diagnostics ctx path =
  let diagnostics = ref [] in
  Llvm.set_diagnostic_handler ctx
    (Some
       (fun d ->
         diagnostics :=
           (Llvm.Diagnostic.severity d, Llvm.Diagnostic.description d)
           :: !diagnostics));
  reading := true;
  let llmodule =
    Fun.protect
      ~finally:(fun () ->
        reading := false;
        Llvm.set_diagnostic_handler ctx None)
      (fun () -> parse ctx path)
  in
  (llmodule, List.rev !diagnostics)

(* Errors and warnings both reject the input: the warning LLVM gives while
   parsing is that it dropped the module's debug information as invalid, and
   every input must keep it. *)
let check_diagnostics llmodule diagnostics =
  match
    List.find_opt
      (fun (severity, _) ->
        match (severity : Llvm.DiagnosticSeverity.t) with
        | Error | Warning -> true
        | Remark | Note -> false)
      diagnostics
  with
  | Some (_, message) -> reject llmodule (Input_error message)
  | None -> ()

let check_debug_info llmodule =
  if Llvm_debuginfo.get_module_debug_metadata_version llmodule = 0 then
    reject llmodule
      (Input_error
         "the module has no \"Debug Info Version\" flag; compile with -g")

(* The data model a target triple implies, for the targets the translation
   models: x86-64 and i386-i686, each on Linux. *)
let data_model_of_triple triple =
  match String.split_on_char '-' triple with
  | arch :: rest when List.exists (String.starts_with ~prefix:"linux") rest -> (
      match arch with
      | "x86_64" -> Some LP64
      | "i386" | "i486" | "i586" | "i686" -> Some ILP32
      | _ -> None)
  | _ -> None

(* A data layout string is a '-'-separated list of specifications.  "E" makes
   the target big-endian; without it LLVM assumes little-endian.  "p:<size>:..."
   gives the width of pointers in address space 0, 64 bits when absent. *)
let layout_specs layout = String.split_on_char '-' layout

let little_endian layout = not (List.mem "E" (layout_specs layout))

let pointer_bits layout =
  List.find_map
    (fun spec ->
      match String.split_on_char ':' spec with
      | "p" :: size :: _ -> int_of_string_opt size
      | _ -> None)
    (layout_specs layout)
  |> Option.value ~default:64

let check_target ?expected llmodule =
  let triple = Llvm.target_triple llmodule in
  let layout = Llvm.data_layout llmodule in
  let fail fmt =
    Printf.ksprintf (fun reason -> reject llmodule (Input_error reason)) fmt
  in
  let model =
    match data_model_of_triple triple with
    | Some model -> model
    | None -> fail "target %S is not x86-64 or i386-i686 Linux" triple
  in
  if not (little_endian layout) then
    fail "data layout %S is big-endian" layout;
  let expected_bits = match model with ILP32 -> 32 | LP64 -> 64 in
  if pointer_bits layout <> expected_bits then
    fail "data layout %S has %d-bit pointers, but target %S has %d-bit ones"
      layout (pointer_bits layout) triple expected_bits;
  (match expected with
  | Some expected when expected <> model ->
      fail "the input is compiled for %s, but %s was asked for"
        (string_of_data_model model)
        (string_of_data_model expected)
  | _ -> ());
  model

let read ?data_model ctx path =
  let llmodule, diagnostics = parse_collecting_diagnostics ctx path in
  check_diagnostics llmodule diagnostics;
  check_debug_info llmodule;
  let data_model = check_target ?expected:data_model llmodule in
  (* LLVM 19 keeps parsed debug information as records attached to
     instructions rather than as instructions, and its C API, which the OCaml
     bindings wrap, has no way to walk those records.  In the older intrinsic
     form a declaration's position is an ordinary [llvm.dbg.declare] call. *)
  Llvm_debuginfo.set_is_new_dbg_info_format llmodule false;
  { llmodule; data_model }
