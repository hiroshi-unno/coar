(* Reader of a Buchi automaton in the never-claim format LTL3BA prints, for the
   C frontend's LTL path.  A state named [accept_*] is accepting and the one
   named [*_init] is initial; an input with no initial state, or more than
   one, is refused.  Errors are returned as [Error], never raised. *)

open Core
open Common.Util
open Common.Combinator
open CSyntax

exception Err of string

let parse_from_lexbuf lexbuf =
  try
    let graph = BaParsing.toplevel BaLexer.main lexbuf in
    let strid_to_intid_buf = Hashtbl.Poly.create ~size:123456 () in
    let initial_state = ref (-1) in
    let final_states = ref [] in
    let states = ref 0 in
    let register strid =
      let intid = !states in
      states := !states + 1;
      if String.is_prefix strid ~prefix:"accept_" then
        final_states := intid :: !final_states;
      if String.is_suffix strid ~suffix:"_init" then (
        if !initial_state >= 0 then raise (Err "initial state is anbiguous");
        initial_state := intid);
      Hashtbl.Poly.add_exn strid_to_intid_buf ~key:strid ~data:intid
    in
    let strid_to_intid strid =
      if not (Hashtbl.Poly.mem strid_to_intid_buf strid) then register strid;
      Hashtbl.find_exn strid_to_intid_buf strid
    in
    let transition =
      List.map graph ~f:(fun (from_strid, to_strid, cond) ->
          (strid_to_intid from_strid, strid_to_intid to_strid, cond))
    in
    if !initial_state < 0 then raise (Err "can't find an initial state");
    Ok
      (BuchiAutomaton.init_ba ~states:!states ~initial_state:!initial_state
         ~final_states:!final_states ~transition)
  with
  | CSyntax.SemanticError error -> Error (sprintf "semantic error: %s" error)
  | CSyntax.SyntaxError error ->
      Error
        (sprintf "%s: syntax error: %s"
           (LexingHelper.get_position_string lexbuf)
           error)
  | BaParsing.Error ->
      Error
        (sprintf "%s: syntax error" (LexingHelper.get_position_string lexbuf))
  | BaLexer.ErrorFormatted error -> Error error
  | BaLexer.SyntaxError error ->
      Error
        (sprintf "%s: syntax error: %s"
           (LexingHelper.get_position_string lexbuf)
           error)
  | Err error -> Error error

let from_file filename =
  In_channel.with_file filename ~f:(fun channel ->
      parse_from_lexbuf (Lexing.from_channel channel))

let from_string = Lexing.from_string >> parse_from_lexbuf
