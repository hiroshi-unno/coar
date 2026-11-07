(** Reading the input: an LLVM IR module ([.ll] or [.bc]) checked against what
    every input must satisfy, with its debug information put into the form the
    later stages walk.

    An input must be clang's output for x86-64 or i386-i686 Linux, compiled
    with [-g]: the C positions in its debug information are what witnesses and
    the position of each declaration are read from, and a module that carries
    them is verified while it is parsed. *)

(** The C data model of the target: 32-bit [int], [long] and pointers, or
    64-bit [long] and pointers. *)
type data_model = ILP32 | LP64

val string_of_data_model : data_model -> string

type input = { llmodule : Llvm.llmodule; data_model : data_model }

val install_fatal_error_handler : unit -> unit
(** Routes LLVM's fatal errors to an exit with the code of
    {!Outcome.Input_error} while an input is being read (the verifier
    rejecting the module is reported that way) and of
    {!Outcome.Internal_error} otherwise.  LLVM exits the process after a fatal
    error, so these cannot be caught as exceptions.  Call it once, before
    {!read}. *)

val read : ?data_model:data_model -> Llvm.llcontext -> string -> input
(** [read ?data_model ctx path] parses [path] into [ctx] and checks it.
    Raises [Outcome.Stop (Input_error _)] when the file cannot be read or
    parsed, when parsing reports an error or a warning (LLVM drops invalid
    debug information with a warning), when the module has no
    ["Debug Info Version"] flag, when the target triple is not x86-64 or
    i386-i686 Linux, when the data layout is not little-endian or its pointer
    width disagrees with the triple, and when [data_model] is given and differs
    from the triple's.  On success the module's debug information is in the
    intrinsic form, so [llvm.dbg.declare] and its siblings are ordinary call
    instructions. *)
