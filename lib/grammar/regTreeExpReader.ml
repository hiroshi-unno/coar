open Core

(* The reader of regular tree expression type definitions ([.xt] files), the
   input language of the XML-type front end of the EHMTT verifier, which turns
   an XML schema into the input or output tree automaton of a tree transducer:

     type Doc = doc[Preface, (Div|P|Note)*]

   An upper-case identifier names a type, a lower-case one followed by
   brackets is an element label with its content, [,] is concatenation of
   sibling sequences, [|] alternation, [*] and [?] repetition and option, and
   [()] the empty sequence.  The first definition is the start type: the
   automaton [RegTreeExp.tta_of] builds accepts the trees of that type, in the
   binary first-child/next-sibling encoding where [leaf] ends a sequence. *)

type defs = (string * (string, string) RegTreeExp.t) list

(* [check ~name defs] returns [defs] unchanged when the definitions can be
   translated, and otherwise an error naming the file [name] and the defect:
   no definition at all (there is no start type), a type defined twice (the
   translation would silently use the first), or a reference to a type that
   is not defined (the translation would fail on the lookup). *)
let check ~name (defs : defs) : defs Or_error.t =
  let defined = List.map defs ~f:fst in
  match defs with
  | [] ->
      Or_error.errorf "%s: no type definition (the first one is the start type)"
        name
  | _ -> (
      match List.find_a_dup defined ~compare:String.compare with
      | Some id ->
          Or_error.errorf "%s: type %s is defined more than once" name id
      | None -> (
          match
            List.find_map defs ~f:(fun (id, t) ->
                List.find (RegTreeExp.symbols t) ~f:(fun s ->
                    not (List.mem defined s ~equal:String.equal))
                |> Option.map ~f:(fun s -> (id, s)))
          with
          | Some (id, s) ->
              Or_error.errorf "%s: type %s refers to %s, which is not defined"
                name id s
          | None -> Ok defs))

(* Parse and check the definitions [lexbuf] holds, naming the input [name] in
   messages.  A lexical or syntax error is returned as an error carrying
   [name:line:column] of the offending token, the line and column being those
   of [lexbuf]'s positions, never raised. *)
let from_lexbuf ~name lexbuf : defs Or_error.t =
  let position () =
    let p = Lexing.lexeme_start_p lexbuf in
    sprintf "%s:%d:%d" name p.pos_lnum (p.pos_cnum - p.pos_bol + 1)
  in
  match RegTreeExpParser.regtreeexpdefs RegTreeExpLexer.token lexbuf with
  | defs -> check ~name defs
  | exception RegTreeExpParser.Error ->
      Or_error.errorf "%s: syntax error at %S" (position ())
        (Lexing.lexeme lexbuf)
  | exception RegTreeExpLexer.SyntaxError msg ->
      Or_error.errorf "%s: %s" (position ()) msg

(* Parse and check the definitions read from [ic], naming the input [name] in
   positions and messages.  [ic] is the caller's: it is neither closed nor
   read past what the lexer consumes. *)
let from_channel ~name ic : defs Or_error.t =
  let lexbuf = Lexing.from_channel ic in
  Lexing.set_filename lexbuf name;
  from_lexbuf ~name lexbuf

(* Parse and check definitions cut out of a larger file: [text] begins at
   [pos] of the file [name], so an error reports the file's own line and
   column (a reader that cuts out a section must keep every newline and every
   byte offset of it in [text] for this to hold). *)
let from_string ~name ~(pos : Lexing.position) text : defs Or_error.t =
  let lexbuf = Lexing.from_string text in
  Lexing.set_position lexbuf pos;
  Lexing.set_filename lexbuf name;
  from_lexbuf ~name lexbuf

(* The file reader owns the channel it opens and closes it on every exit. *)
let from_file filename : defs Or_error.t =
  In_channel.with_file filename
    ~f:(from_channel ~name:(Filename.basename filename))
