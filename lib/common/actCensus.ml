(* An act census (instrument only): with [COAR_ACT_CENSUS] set in the
   environment, a switch that is off still computes, at the point where it
   would act, what it would have done, and when that differs from what the
   off switch does, [note name] reports it once per process on stderr as
   [[act-census] name].  Nothing that is computed for the census is used, so
   the run answers as it would without the variable; without it [note] is
   one boolean read and the callers skip the computation.  A forked copy
   inherits what its parent has already reported and so reports only names
   new to it.  What it is for: before a switch is made a default, telling
   from runs of the default configuration which inputs the switch would act
   on at all. *)

(* read once at start-up, not lazily: a [Lazy.t] forced from two domains at
   once raises *)
let enabled = Option.is_some (Stdlib.Sys.getenv_opt "COAR_ACT_CENSUS")
let on () = enabled
let seen : (string, unit) Stdlib.Hashtbl.t = Stdlib.Hashtbl.create 16
let lock = Stdlib.Mutex.create ()

let note name =
  if on () then (
    Stdlib.Mutex.lock lock;
    let fresh = not (Stdlib.Hashtbl.mem seen name) in
    if fresh then Stdlib.Hashtbl.replace seen name ();
    Stdlib.Mutex.unlock lock;
    if fresh then (
      Stdlib.prerr_endline ("[act-census] " ^ name);
      Stdlib.flush Stdlib.stderr))
