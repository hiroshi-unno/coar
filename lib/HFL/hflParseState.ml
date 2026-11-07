(* The constructs met while one file is lexed and parsed, by the name a
   dialect refusal gives them.  Global because menhir's semantic actions and
   ocamllex's rules take no extra argument; [HflReader.parse] resets it before
   each file and reads it once the file is parsed, so it is never shared
   between two files (parsing is not done from parallel domains). *)

let seen : string list ref = ref []
let saw s = if not (List.mem s !seen) then seen := s :: !seen
let reset () = seen := []
