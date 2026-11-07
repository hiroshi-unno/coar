(** The LTS translation of Athena's route: llvm2lts (athena/llvm2lts), which
    translates LLVM IR to a labelled transition system in the T2 format,
    linked into this executable.  A build of CoAR without LLVM 19's OCaml
    bindings has the stub (llvm2ltsEntry.none.ml): [available] is false and
    [translate] refuses. *)

val available : bool

(** how the IR's integers are read: as bit-vectors, as mathematical
    integers without bitwise operations, with bitwise operations in infinite
    two's complement, or as C reads them (every value its unsigned
    representative, unsigned arithmetic wrapping, a signed overflow stopping
    the execution: llvm2lts's int-wrap-unsigned), or so with signed
    arithmetic wrapping too (llvm2lts's int-wrap-all, gcc's -fwrapv) *)
type mode = Bv | Int | Int_bitwise | Int_wrap_unsigned | Int_wrap_all

type property = Unreach_call | Termination
type data_model = LP64 | ILP32

type answer =
  | T2 of string  (** the translation, as the text of a T2 file *)
  | Failed of string
      (** the input is outside what the translation supports, is not a
          valid input, or the translation failed: an ordinary answer, MAYBE,
          with the reason *)

val translate :
  ?unbounded_nondet:bool ->
  ?hoist:bool ->
  ?accumulator_recursion:bool ->
  ?simplifycfg:bool ->
  data_model:data_model ->
  mode:mode ->
  property:property ->
  string ->
  answer Core.Or_error.t
(** [translate ~data_model ~mode ~property path] translates the [.ll] or
    [.bc] file [path], which must have been compiled for [data_model], with
    the standalone llvm2lts's defaults for every other choice but two:
    [unbounded_nondet] (default false) reads a [__VERIFIER_nondet_T] as any
    integer rather than one of T's range, in an Int mode only (llvm2lts's
    [--unbounded-nondet]); [hoist] (default false) reads a loop's reads of an
    array cell the loop never writes once before it ([--hoist=yes]);
    [accumulator_recursion] (default false) also turns [return n + f(x);]
    and [return n * f(x);] into loops, admitted with [unbounded_nondet] in
    an Int mode only ([--tailcallelim-accumulator=yes]); [simplifycfg]
    (default false) runs LLVM's simplifycfg, without speculation, before
    mem2reg ([--simplifycfg=yes]). *)
