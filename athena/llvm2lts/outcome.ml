(* The ways llvm2lts can stop short of a translation, and the exit code each
   gives the standalone tool.

   UNKNOWN means the input is well formed but outside what the translation
   supports (a construct not on the allow-list, recursion left over); it is an
   ordinary answer, not an error.  INPUT_ERROR means the input itself is not
   usable as given: it does not parse or verify, lacks the debug information
   every input must carry, or targets a machine the translation does not
   model.  INTERNAL_ERROR is a defect of llvm2lts or of LLVM. *)

type failure =
  | Unknown of string
  | Input_error of string
  | Internal_error of string

exception Stop of failure

let stop failure = raise (Stop failure)

(* 0 is success.  Each failure kind has its own code so that a caller can tell
   "outside the supported language" from "not a valid input" without reading
   the message. *)
let exit_code = function
  | Unknown _ -> 1
  | Input_error _ -> 2
  | Internal_error _ -> 3

let to_string = function
  | Unknown reason -> "UNKNOWN: " ^ reason
  | Input_error reason -> "INPUT_ERROR: " ^ reason
  | Internal_error reason -> "INTERNAL_ERROR: " ^ reason
