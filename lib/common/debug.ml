(* Per-module tracing.  [Make (val Config.enable)] or [(val Config.disable)]
   gives a module its own [print], which forces the lazy message and writes
   it to stderr only while tracing is on; [set_enable] switches it at run
   time, and an [id] (the parallel domain's, by default the one set with
   [set_id]) prefixes every line.  [print_stdout] writes unconditionally to
   stdout and is for output that is part of a result, not tracing.  The
   switches are atomics so that domains may read them concurrently. *)
open Core

module Config = struct
  type t = { dbg_mode : bool; [@default false] exec_time : bool [@default false] } [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let disable =
    (module struct
      let config = { dbg_mode = false; exec_time = false }
    end : ConfigType)

  let enable =
    (module struct
      let config = { dbg_mode = true; exec_time = false }
    end : ConfigType)
end

module Make (Config : Config.ConfigType) = struct
  let dbg_id = Atomic.make None
  let module_name = Atomic.make ""
  let set_id = Atomic.set dbg_id
  let set_module_name = Atomic.set module_name
  let enable = Atomic.make Config.config.dbg_mode

  let print ?(id = Atomic.get dbg_id) str =
    if Atomic.get enable then (
      (match id with
      | None -> Out_channel.prerr_endline (Lazy.force str)
      | Some id ->
          let str = Lazy.force str in
          let lines =
            List.map ~f:(sprintf "[#%d] %s" id) @@ String.split ~on:'\n' str
          in
          Out_channel.prerr_endline @@ String.concat ~sep:"\n" lines);
      Out_channel.flush stderr)

  let print_stdout ?(id = Atomic.get dbg_id) str =
    match id with
    | None -> Out_channel.print_endline (Lazy.force str)
    | Some id ->
        let str = Lazy.force str in
        let lines =
          List.map ~f:(sprintf "[#%d] %s" id) @@ String.split ~on:'\n' str
        in
        Out_channel.print_endline @@ String.concat ~sep:"\n" lines

  let print_exec_time label fapp () =
    let st = Clock.now_float () in
    let res = Lazy.force fapp in
    let diff =
      Time_float.diff (Clock.now_float ()) st |> Time_float.Span.to_sec
    in
    print @@ lazy (sprintf "**** call %s (time: %f)" label diff);
    res

  let log_str ?(tag = "") msg =
    if Stdlib.(Atomic.get module_name = "") then msg
    else if Stdlib.(tag = "") then
      sprintf "[%s] " (Atomic.get module_name) ^ msg
    else sprintf "[%s: %s] " (Atomic.get module_name) tag ^ msg

  let print_log ?(tag = "") str =
    if Atomic.get enable then
      let str = Lazy.force str in
      print @@ lazy (log_str ~tag str)

  let set_enable switch = Atomic.set enable switch
end
