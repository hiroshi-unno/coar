(* athena-witness: writes the SV-COMP witness for a result of athena on one
   input file, from the input, its property file and Ptr2ArrFC's
   transformation record of that input.

   Exit status: 0 the witness was written; 2 this result gets no witness (the
   reason on one stderr line, no file written); 1 an error (unreadable or
   inconsistent inputs, an invalid option; no file written). *)

open Athena_witness

let error fmt = Printf.ksprintf (fun s -> prerr_endline ("athena-witness: error: " ^ s); 1) fmt

(* RFC 4122 version 4: random, with the version and variant bits set. *)
let uuid4 () =
  let b =
    match In_channel.with_open_bin "/dev/urandom" (fun ic -> really_input_string ic 16) with
    | s -> Bytes.of_string s
    | exception Sys_error _ ->
        Random.self_init ();
        Bytes.init 16 (fun _ -> Char.chr (Random.int 256))
  in
  Bytes.set b 6 (Char.chr (Char.code (Bytes.get b 6) land 0x0f lor 0x40));
  Bytes.set b 8 (Char.chr (Char.code (Bytes.get b 8) land 0x3f lor 0x80));
  let h i = Printf.sprintf "%02x" (Char.code (Bytes.get b i)) in
  let hex a z = String.concat "" (List.init (z - a) (fun i -> h (a + i))) in
  String.concat "-" [ hex 0 4; hex 4 6; hex 6 8; hex 8 10; hex 10 16 ]

let now_utc () =
  let t = Unix.gmtime (Unix.time ()) in
  Printf.sprintf "%04d-%02d-%02dT%02d:%02d:%02dZ" (t.tm_year + 1900) (t.tm_mon + 1) t.tm_mday t.tm_hour
    t.tm_min t.tm_sec

(* The data model: the task's, else --data-model's; never a default. When both
   are given they must agree. *)
let data_model ~task ~option =
  let from_task =
    match task with
    | None -> Ok None
    | Some path -> Task.read_data_model path
  in
  match (from_task, option) with
  | Error e, _ -> Error e
  | Ok (Some t), Some o when t <> o ->
      Error
        (Printf.sprintf "the task's data model %s disagrees with --data-model %s"
           (Witness.string_of_data_model t) (Witness.string_of_data_model o))
  | Ok (Some t), _ -> Ok t
  | Ok None, Some o -> Ok o
  | Ok None, None ->
      Error
        (match task with
        | Some p -> p ^ " states no options.data_model, and no --data-model was given"
        | None -> "no data model: give --task or --data-model")

let run input record_path prp result task dm violated invariants producer_version producer_name
    format_version output =
  let ( let* ) r f = match r with Ok x -> f x | Error code -> code in
  let or_error = function Ok x -> Ok x | Error e -> Error (error "%s" e) in
  let* () =
    if format_version = "2.1" then Ok ()
    else Error (error "--format-version %s: only 2.1 is supported" format_version)
  in
  let* properties = or_error (Result.map_error (fun e -> prp ^ ": " ^ e) (Property.read prp)) in
  let* record = or_error (Record.read record_path) in
  let* input_sha256 =
    match Sha256.file input with h -> Ok h | exception Sys_error e -> Error (error "%s" e)
  in
  let* () =
    if input_sha256 = record.sha256 then Ok ()
    else
      Error
        (error "%s has SHA-256 %s, but the record %s was made from an input with %s" input input_sha256
           record_path record.sha256)
  in
  let* invariant_lines =
    match invariants with
    | None -> Ok []
    | Some path -> or_error (Invariants.read path)
  in
  let* data_model = or_error (data_model ~task ~option:dm) in
  let* () =
    match Record.data_model_of_machdep record.machdep with
    | Some m when m = data_model -> Ok ()
    | Some m ->
        Error
          (error "the data model is %s, but the record was read with machdep %s (%s)"
             (Witness.string_of_data_model data_model) record.machdep (Witness.string_of_data_model m))
    | None -> Error (error "the record's machdep %s has no known data model" record.machdep)
  in
  let request =
    {
      Compose.input_file = input;
      input_sha256;
      record;
      properties;
      result;
      violated;
      data_model;
      producer =
        { name = producer_name; version = producer_version; configuration = None; command_line = None;
          description = None };
      format_version;
      uuid = uuid4 ();
      creation_time = now_utc ();
      invariant_lines;
    }
  in
  let outcome, notes = Compose.compose request in
  List.iter (fun n -> prerr_endline ("athena-witness: " ^ n)) notes;
  match outcome with
  | Invalid e -> error "%s" e
  | No_witness why ->
      prerr_endline ("athena-witness: no witness: " ^ why);
      2
  | Write w -> (
      match Out_channel.with_open_bin output (fun oc -> output_string oc (Witness.to_string w)) with
      | () -> 0
      | exception Sys_error e -> error "%s" e)

open Cmdliner

let file_arg name doc = Arg.(required & opt (some file) None & info [ name ] ~docv:"FILE" ~doc)

let input = file_arg "input" "The input C file, named as the verifier was given it."
let record = file_arg "record" "Ptr2ArrFC's transformation record (.p2a.json) of the input."
let prp = file_arg "property" "The SV-COMP property file (.prp)."

let result =
  Arg.(
    required
    & opt (some (enum [ ("true", true); ("false", false) ])) None
    & info [ "result" ] ~docv:"true|false" ~doc:"The verification result.")

let task =
  Arg.(
    value & opt (some file) None
    & info [ "task" ] ~docv:"TASK.yml" ~doc:"The task definition; its options.data_model is read.")

let dm =
  Arg.(
    value
    & opt (some (enum [ ("ILP32", Witness.ILP32); ("LP64", Witness.LP64) ])) None
    & info [ "data-model" ] ~docv:"ILP32|LP64" ~doc:"The data model, when no task file states it.")

let violated =
  Arg.(
    value
    & opt
        (some
           (enum
              [ ("valid-deref", Property.Valid_deref);
                ("valid-free", Property.Valid_free);
                ("valid-memtrack", Property.Valid_memtrack);
                ("valid-memcleanup", Property.Valid_memcleanup) ]))
        None
    & info [ "violated" ] ~docv:"PROPERTY"
        ~doc:"With --result false: the memory-safety sub-property found violated.")

let invariants =
  Arg.(
    value & opt (some file) None
    & info [ "invariants" ] ~docv:"FILE"
        ~doc:
          "The lines CoAR printed after its verdict on the direct LLVM route, about the loop heads of \
           Ptr2ArrFC's output: with --result true, (invariant ...), (transition ...) and (skipped ...); with \
           --result false, (state ...), the loop-head visits of the violating execution.")

let producer_version =
  Arg.(required & opt (some string) None & info [ "producer-version" ] ~docv:"V" ~doc:"The producer's version.")

let producer_name =
  Arg.(value & opt string "MuVal" & info [ "producer-name" ] ~docv:"NAME" ~doc:"The producer's name.")

let format_version =
  Arg.(
    value & opt string "2.1"
    & info [ "format-version" ] ~docv:"V" ~doc:"The witness format version; only 2.1 is supported.")

let output = Arg.(required & opt (some string) None & info [ "o" ] ~docv:"WITNESS.yml" ~doc:"The witness file.")

let cmd =
  let exits =
    [ Cmd.Exit.info 0 ~doc:"the witness was written.";
      Cmd.Exit.info 2 ~doc:"this result gets no witness; the reason is on stderr.";
      Cmd.Exit.info 1 ~doc:"an error; nothing was written." ]
  in
  Cmd.v
    (Cmd.info "athena-witness" ~exits ~doc:"write the SV-COMP witness of a result of athena")
    Term.(
      const run $ input $ record $ prp $ result $ task $ dm $ violated $ invariants $ producer_version
      $ producer_name $ format_version $ output)

let () =
  match Cmd.eval_value cmd with
  | Ok (`Ok code) -> exit code
  | Ok (`Version | `Help) -> exit 0
  | Error _ -> exit 1
