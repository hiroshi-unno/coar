(* The ways the frontend can stop short of a translation.

   UNKNOWN means the input is well formed but outside what the translation
   supports (a construct not on the allow-list, recursion left over); it is an
   ordinary answer, not an error.  INPUT_ERROR means the input itself is not
   usable as given: it does not parse or verify, lacks the debug information
   every input must carry, or targets a machine the translation does not
   model.  INTERNAL_ERROR is a defect of the frontend or of LLVM. *)

type failure =
  | Unknown of string
  | Input_error of string
  | Internal_error of string

exception Stop of failure

let stop failure = raise (Stop failure)

let to_string = function
  | Unknown reason -> "UNKNOWN: " ^ reason
  | Input_error reason -> "INPUT_ERROR: " ^ reason
  | Internal_error reason -> "INTERNAL_ERROR: " ^ reason
