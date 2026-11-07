(** The rewriting step of Athena's route: Ptr2ArrFC, the C-to-C rewriting on
    Frama-C (athena/Ptr2ArrFC), linked into this executable.  Frama-C reads
    its command line once, when its kernel is initialised, so the rewriting
    runs in a copy of this executable started for it, which [main] hands over
    to Frama-C before anything else ([run_child_if_asked]).  A build of CoAR
    without Frama-C has the stub (p2aEntry.none.ml): [available] is false,
    [run] refuses and the copy is never started. *)

val available : bool

val run_child_if_asked : unit -> unit
(** When this process is the copy started by [run], runs Frama-C on its
    command line and ends the process; otherwise returns at once.  The
    executable calls it before reading its own command line. *)

type outcome =
  | Exited of int
      (** ptr2arr's status: 0 written, 1 unreadable input or internal error,
          2 a construct outside its fragment (listed on standard error) *)
  | Timed_out

val run :
  ?env:string array ->
  ?timeout:float ->
  cwd:string ->
  string list ->
  outcome Core.Or_error.t
(** [run ~cwd args] runs ptr2arr with the arguments [args] (its own command
    line, see athena/Ptr2ArrFC/README.md) in directory [cwd]; [env] is added
    to the environment; past [timeout] seconds the copy is sent SIGTERM.
    An error is a command line ptr2arr refuses, or the stub. *)
