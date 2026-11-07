(** The [ptr2arr] command line, shared by the standalone executable and by any
    program that links the transformation in. The transformation runs in a
    copy of the program started with [PTR2ARR_FRAMAC_CHILD=1] (Frama-C reads
    its command line once, when its kernel is initialised); such a program
    calls [boot_child] first thing when [is_child] holds. *)

exception Exit_with of int
(** Raised once a usage message or the reason an option is refused has been
    printed on standard error; the status to end with (1). *)

val child_var : string
(** the environment variable that marks the Frama-C child *)

val parse : string list -> string list
(** [parse args] is the child's Frama-C command line for [ptr2arr]'s
    arguments [args] (the program's name not included). Raises [Exit_with]
    for a refused command line. An ILP32 [.i] input whose [max_align_t] the
    front end cannot read is replaced by a copy in a temporary directory,
    removed by [run]. *)

type outcome =
  | Exited of int  (** the documented status, 0 to 4 *)
  | Timed_out  (** the child was stopped after [timeout] seconds *)

val run :
  ?spawn:(string -> string array -> string array -> int) ->
  ?env:string array ->
  ?timeout:float ->
  exe:string ->
  string list ->
  outcome
(** [run ~exe args] runs [ptr2arr] with arguments [args] in a child [exe],
    which must be a program that boots the child ([boot_child]) when it sees
    [child_var] set. [spawn prog argv env] starts the child and returns its
    process id; by default with [Unix.create_process_env], its standard output
    and error going to this process's standard error. [env] is added to this
    process's environment. Past [timeout] seconds the child is sent SIGTERM and
    [Timed_out] is the outcome. Raises [Exit_with] for a refused command line,
    before anything is started. *)

val is_child : unit -> bool
(** this process is a child started by [run] *)

val boot_child : unit -> unit
(** runs the Frama-C kernel, with the plugin, on this process's command line;
    returns when Frama-C returns (it may also exit by itself). *)
