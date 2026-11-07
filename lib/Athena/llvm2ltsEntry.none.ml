(* The stub selected when the optional library llvm2lts is not built, that
   is, when LLVM 19's OCaml bindings (opam package llvm, version 19) were not
   installed at build time. *)

let available = false

type mode = Bv | Int | Int_bitwise | Int_wrap_unsigned | Int_wrap_all
type property = Unreach_call | Termination
type data_model = LP64 | ILP32
type answer = T2 of string | Failed of string

let translate ?unbounded_nondet:_ ?hoist:_ ?accumulator_recursion:_ ?simplifycfg:_ ~data_model:_ ~mode:_ ~property:_ _ =
  Core.Or_error.error_string
    "Athena's LTS translation (llvm2lts, route Llvm2lts) was not built into \
     this CoAR: LLVM 19's OCaml bindings were absent when it was built. \
     Install them with opam, either llvm.19-shared together with the \
     system's LLVM 19 development package (e.g. llvm-19-dev), or \
     llvm.19-static for a self-contained build, then rebuild CoAR (dune \
     build main.exe)."
