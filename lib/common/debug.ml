open Core

module Config = struct
  type t = { dbg_mode : bool; exec_time : bool } [@@ deriving yojson]
  module type ConfigType = sig val config : t end
  let disable =
    (module struct let config =
                     { dbg_mode = false; exec_time = false } end : ConfigType)
  let enable =
    (module struct let config =
                     { dbg_mode = true; exec_time = false } end : ConfigType)
end

module Make (Config : Config.ConfigType) = struct

  let print str =
    if Config.config.dbg_mode then Out_channel.prerr_endline (Lazy.force str);
    Out_channel.flush stderr

  let print_exec_time label fapp =
    fun () ->
    let st = Time.now () in
    let res = Lazy.force fapp in
    let diff = Time.diff (Time.now ()) st |> Time.Span.to_sec in
    print @@
    lazy (Printf.sprintf "**** call %s (time: %f)" label diff);
    res

end
