(* The stub selected when the optional library frama-c-ptr2arr.cli is not
   built, that is, when Frama-C (opam package frama-c, version 33) was not
   installed at build time. *)

let available = false
let run_child_if_asked () = ()

type outcome = Exited of int | Timed_out

let run ?env:_ ?timeout:_ ~cwd:_ _ =
  Core.Or_error.error_string
    "Athena's rewriting step (Ptr2ArrFC) was not built into this CoAR: \
     Frama-C 33 was absent when it was built. Install it with opam (frama-c), \
     then rebuild CoAR (dune build main.exe)."
