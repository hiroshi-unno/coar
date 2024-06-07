open Core

(** {6 Timer} *)

let timers = ref []

let make () =
  let st = Core_unix.times () in
  fun () ->
    let en = Core_unix.times () in
    en.Core_unix.tms_utime -. st.Core_unix.tms_utime
    +. (en.Core_unix.tms_cutime -. st.Core_unix.tms_cutime)

let start () = timers := make () :: !timers

let stop () =
  match !timers with
  | [] -> assert false
  | tm :: tms ->
      timers := tms;
      tm ()

let get_user_time () =
  let en = Core_unix.times () in
  en.Core_unix.tms_utime +. en.Core_unix.tms_cutime

(** {6 Interval Timer} *)
let start_time = ref (Core_unix.times ()) (*dummy*)

let start_interval () = start_time := Core_unix.times ()

let stop_interval () =
  let en = Core_unix.times () in
  en.Core_unix.tms_utime -. !start_time.Core_unix.tms_utime
  +. (en.Core_unix.tms_cutime -. !start_time.Core_unix.tms_cutime)

exception Timeout

let sigalrm_catched = ref false

let disable_timeout f arg =
  sigalrm_catched := false;
  let reset_sigalrm_handler =
    let old_handler =
      let sigalrm_delayed_handler =
        Stdlib.Sys.Signal_handle
          (fun _ -> (* Format.printf "Timeout!@,"; *) sigalrm_catched := true)
      in
      Stdlib.Sys.signal Stdlib.Sys.sigalrm sigalrm_delayed_handler
    in
    fun () -> Stdlib.Sys.set_signal Stdlib.Sys.sigalrm old_handler
  in
  try
    let ret = f arg in
    reset_sigalrm_handler ();
    if !sigalrm_catched then
      raise Timeout (* @todo may differ from the behavior of [old_handler] *)
    else ret
  with exc ->
    reset_sigalrm_handler ();
    raise exc

(** Set timeout for a function.
    E.g. Set 1 second time out to [hoge ()]
    {[ enable_timeout 1 ident ident
        (fun () -> hoge ())
        (fun time ret -> Format.printf "Fast (time = %f)" time)
        (fun time ret -> Format.printf "Too slow (time = %f)" time)
    ]}
    Setting timeout to 0 ignore timeout.
    Please note some counterintuitive points:
    {ul
      {- If the function call is nested, the previous timeout is masked }
      {- [Unix.sleep] do not tick [Unix.times] }
      {- The signal is delayed if [hoge ()] do not allocate memory (True?) }
    } *)
let already_set = ref false
(* if enable_timer is invoked from the call to main, it is just ignored *)

let enable_timeout timeout before after main normal_handler exc_handler =
  (* Reset to restart the previous counter *)
  Combinator.hook true before after (fun () ->
      if !already_set then main ()
      else
        let finish =
          let old_handler =
            let sigalrm_handler =
              Stdlib.Sys.Signal_handle
                (fun _ -> (* Format.printf "Timeout!@,";  *) raise Timeout)
            in
            Stdlib.Sys.signal Stdlib.Sys.sigalrm sigalrm_handler
          in
          fun () ->
            ignore @@ Core_unix.alarm 0;
            already_set := false;
            Stdlib.Sys.set_signal Stdlib.Sys.sigalrm old_handler
        in
        start ();
        already_set := true;
        ignore @@ Core_unix.alarm timeout;
        (*print_endline (string_of_float timeout);*)
        match main () with
        | ret ->
            finish ();
            normal_handler (stop ()) ret
        | exception exc ->
            finish ();
            exc_handler (stop ()) exc)

(*(** Set timeout for a function.
      E.g. Set 1 second time out to [hoge ()]
    {[ Timer.block ~timeout:1 id id
        (fun () -> hoge ())
        (fun time ret -> Format.printf "Fast (time = %f)" time)
        (fun time ret -> Format.printf "Too slow (time = %f)" time)
  ]}
          Setting timeout to 0. ignore timeout.
          Please note some counterintuitive points:
          {ul
          {- If the block is nested, the previous timeout is masked }
          {- [Unix.sleep] do not tick [Unix.times] }
          {- The signal is delayed if [hoge ()] do not allocate memory (True?) }
          } *)
     let block ?(timeout = 0.) before after main normal_handler exc_handler =
     (* Reset to restart the previous counter *)
     let reset_to_previous_timer prev elapsed =
     let prev = {
     Unix.it_interval = 0.0;
     Unix.it_value =
      if prev.Unix.it_value = 0.0
      then prev.Unix.it_value (* Time was not set *)
      else
        let tmp = prev.Unix.it_value -. elapsed in
        if tmp <= 0.0 then 0.0 else tmp }
     in
     let _ = Unix.setitimer Unix.ITIMER_VIRTUAL prev in
     ()
     in
     hook true before after
     (fun () ->
     let t = Unix.ITIMER_VIRTUAL in
     let s = {
       Unix.it_interval = 0.0; (* Disable after its next expiration *)
       Unix.it_value = timeout;
     } in
     let prev = Unix.setitimer t s in
     Sys.set_signal Sys.sigvtalrm sigalrm_handler;
     start ();
     match main () with
     | ret ->
       let elapsed = stop () in
       reset_to_previous_timer prev elapsed;
       normal_handler elapsed ret
     | exception exc ->
       let elapsed = stop () in
       reset_to_previous_timer prev elapsed;
       exc_handler elapsed exc)*)
