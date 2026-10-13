(** A deliberate refusal: an input, a query or a configuration this tool does
    not handle, stated in one sentence that names what is missing.

    Most refusals travel as an [Or_error] value, which the command-line entry
    prints as one line with a non-zero status.  This exception is for a site
    that has no error channel to return through -- a solver whose result type
    is a verdict, or a check deep inside a translation -- and the entry catches
    exactly this one and prints it the same way.  Raising [Failure] there
    instead is indistinguishable from an internal error: it reaches the user as
    an OCaml backtrace, which every harness in this tree reads as a crash.

    It is not asynchronous (a timeout handler must not catch it as one), and a
    catch-all [with _ ->] between the raise and the entry will swallow it like
    any other exception, so raise it only where no such handler intervenes or
    where the handler re-raises what it does not own. *)

exception Refused of string

let refuse fmt = Printf.ksprintf (fun msg -> raise (Refused msg)) fmt
