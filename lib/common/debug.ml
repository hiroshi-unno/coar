open Core

module Config = struct
  type t = { dbg_mode : bool; exec_time : bool } [@@deriving yojson]

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
    let st = Time_float.now () in
    let res = Lazy.force fapp in
    let diff =
      Time_float.diff (Time_float.now ()) st |> Time_float.Span.to_sec
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
