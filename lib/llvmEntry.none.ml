(* The stub selected when the optional library CoAR.LLVMFront is not built,
   that is, when the LLVM 19 OCaml bindings (opam package [llvm], version 19)
   were not installed at build time.  Every [-p llvm*] input is refused with
   a message that says why and how to obtain a build that has the frontend. *)

type property = Unreach_call | Termination
type answer = Problem of MuCLP.Problem.t * LLVMWitness.Cmap.t option | Unknown of string

let available = false

let translate ?witness:_ ?overrides:_ ~bv_mode:_ ~property:_ ~config:_ _ =
  Core.Or_error.error_string
    "the direct LLVM frontend (-p llvmsafe, llvmsafebv, llvmterm, llvmtermbv) \
     was not built into this CoAR: LLVM 19's OCaml bindings were absent when \
     it was built. Install them with opam, either llvm.19-shared together with \
     the system's LLVM 19 development package (e.g. llvm-19-dev), or \
     llvm.19-static for a self-contained build, then rebuild CoAR (dune build \
     main.exe)."
