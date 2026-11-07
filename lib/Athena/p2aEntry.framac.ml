(* The rewriting step with Frama-C linked in (see p2aEntry.mli). *)

let available = true

(* The value the OCaml runtime gave option [letter] of OCAMLRUNPARAM
   (CAMLRUNPARAM when that is unset), read as the runtime reads it: options
   separated by commas, each a letter followed by "=N" or "=0xN" with an
   optional k, M or G multiplier, a letter alone meaning 1, a later option
   overriding an earlier one; [None] when the option is not given. *)
let runtime_param letter =
  let value item =
    let n = String.length item in
    let hex = n >= 4 && String.sub item 1 3 = "=0x" in
    let start = if hex then 4 else 2 in
    let digit c =
      match c with
      | '0' .. '9' -> Some (Char.code c - Char.code '0')
      | 'a' .. 'f' when hex -> Some (Char.code c - Char.code 'a' + 10)
      | 'A' .. 'F' when hex -> Some (Char.code c - Char.code 'A' + 10)
      | _ -> None
    in
    let rec number i v =
      match if i < n then digit item.[i] else None with
      | Some d -> number (i + 1) ((v * if hex then 16 else 10) + d)
      | None -> (i, v)
    in
    if n < 2 || item.[1] <> '=' then 1
    else
      let stop, v = number start 0 in
      if stop = start then if hex then 0 else 1
      else
        match if stop < n then item.[stop] else ' ' with
        | 'k' -> v * 1024
        | 'M' -> v * 1024 * 1024
        | 'G' -> v * 1024 * 1024 * 1024
        | _ -> v
  in
  let text =
    match Sys.getenv_opt "OCAMLRUNPARAM" with
    | Some text -> Some text
    | None -> Sys.getenv_opt "CAMLRUNPARAM"
  in
  Option.bind text (fun text ->
      List.fold_left
        (fun found item ->
          if String.length item > 0 && item.[0] = letter then Some (value item)
          else found)
        None
        (String.split_on_char ',' text))

(* Frama-C's kernel brings the library frama-c.init, which this executable
   links whole (it is linked with -linkall, as an executable depending on
   dune-site's plugins is) and which, when the program starts, sets the
   minor heap to 256k words and turns the recording of backtraces on, for
   Frama-C's sake.  Every other run of this executable is to run as it does
   in a build without Frama-C: both are put back here (frama-c.init is a
   dependency of this library, so its settings are made before this).  The
   minor heap is the runtime's reading of OCAMLRUNPARAM.  The recording is
   Base's rule, which runs whenever the program starts: on, unless an option
   of OCAMLRUNPARAM starts with "b", and then the runtime's reading of it.
   The copy that runs Frama-C makes Frama-C's settings again
   ([Ptr2arr_cli.boot_child]). *)
let () =
  let mentions_b =
    match Sys.getenv_opt "OCAMLRUNPARAM" with
    | None -> false
    | Some text ->
        List.exists
          (fun item -> String.length item > 0 && item.[0] = 'b')
          (String.split_on_char ',' text)
  in
  Printexc.record_backtrace
    ((not mentions_b)
    || match runtime_param 'b' with Some v -> v <> 0 | None -> false);
  Gc.set
    {
      (Gc.get ()) with
      Gc.minor_heap_size =
        (match runtime_param 's' with Some v -> v | None -> 262144);
    }

let run_child_if_asked () =
  if Ptr2arr_cli.is_child () then (
    Ptr2arr_cli.boot_child ();
    (* what the standalone ptr2arr does when Frama-C returns: end there *)
    Common.ProcessExit.exit 0)

type outcome = Exited of int | Timed_out

let run ?env ?timeout ~cwd args =
  match
    Ptr2arr_cli.run ~spawn:(Process.spawn ~cwd) ?env ?timeout
      ~exe:Sys.executable_name args
  with
  | Ptr2arr_cli.Exited status -> Ok (Exited status)
  | Ptr2arr_cli.Timed_out -> Ok Timed_out
  | exception Ptr2arr_cli.Exit_with status ->
      Core.Or_error.error_string
        (Printf.sprintf "ptr2arr refused its command line (status %d): %s"
           status (String.concat " " args))
