(** The entry to the direct LLVM IR frontend (lib/LLVMFront) for [-p llvm*].
    A build of CoAR without the LLVM 19 OCaml bindings has the stub
    (llvmEntry.none.ml), which refuses every input with that reason. *)

type property = Unreach_call | Termination

type answer =
  | Problem of MuCLP.Problem.t * LLVMWitness.Cmap.t option
      (** with the map from the loop heads to the C program when the
          configuration's [witness] is set *)
  | Unknown of string
      (** the input is outside what the translation supports: an ordinary
          answer, MAYBE, with the reason *)

val available : bool

val translate :
  ?witness:bool ->
  ?overrides:(string * Yojson.Safe.t) list ->
  bv_mode:bool ->
  property:property ->
  config:string option ->
  string ->
  answer Core.Or_error.t
(** [translate ~bv_mode ~property ~config path] reads the [.ll] or [.bc] file
    [path]; [config] is the frontend's JSON configuration file (the
    readings and encodings that are a choice, LLVMFront.Config), the defaults
    when [None].  [~witness:true] builds the map from the loop heads to the C
    program whatever the configuration says, for a caller that writes
    witnesses but takes its configuration from elsewhere.  [overrides]
    (default none): members of the configuration's JSON object, in its own
    spelling, that replace the file's members of the same name (or are the
    whole object when [config] is [None]), for a caller that chooses a
    reading the file does not state; the result is validated as a file is. *)
