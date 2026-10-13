(* Z3's serializers emit SMT-LIB annotations.  Remove the annotation wrapper,
   not text which merely resembles it inside a quoted symbol or a string.
   Keeping source spans preserves all text outside the removed wrappers.
   An optional temporary nullary relation is removed by exact syntax/symbol
   identity, never by replacing substrings in identifiers or string values. *)
type node = Atom of int * int | List of int * int * node list

let parse text =
  let length = String.length text in
  let rec whitespace pos =
    if pos >= length then pos
    else
      match text.[pos] with
      | ' ' | '\t' | '\r' | '\n' -> whitespace (pos + 1)
      | ';' -> comment (pos + 1)
      | _ -> pos
  and comment pos =
    if pos >= length then pos
    else if text.[pos] = '\n' then whitespace (pos + 1)
    else comment (pos + 1)
  in
  let rec quoted delimiter pos =
    if pos >= length then invalid_arg "unterminated SMT-LIB quoted token"
    else if text.[pos] <> delimiter then quoted delimiter (pos + 1)
    else if delimiter = '"' && pos + 1 < length && text.[pos + 1] = '"' then
      quoted delimiter (pos + 2)
    else pos + 1
  in
  let rec atom_end pos =
    if pos >= length then pos
    else
      match text.[pos] with
      | ' ' | '\t' | '\r' | '\n' | '(' | ')' | ';' -> pos
      | _ -> atom_end (pos + 1)
  in
  let rec parse start =
    if start >= length then invalid_arg "missing SMT-LIB expression"
    else
      match text.[start] with
      | '(' ->
          let rec children pos acc =
            let pos = whitespace pos in
            if pos >= length then invalid_arg "unclosed SMT-LIB expression"
            else if text.[pos] = ')' then
              (List (start, pos + 1, List.rev acc), pos + 1)
            else
              let child, stop = parse pos in
              children stop (child :: acc)
          in
          children (start + 1) []
      | ')' -> invalid_arg "unexpected SMT-LIB closing parenthesis"
      | ('|' | '"') as delimiter ->
          let stop = quoted delimiter (start + 1) in
          (Atom (start, stop), stop)
      | _ ->
          let stop = atom_end start in
          (Atom (start, stop), stop)
  in
  let rec roots pos acc =
    let start = whitespace pos in
    if start = length then List.rev acc
    else
      let node, stop = parse start in
      roots stop (node :: acc)
  in
  roots 0 []

let cleanup ?query text =
  let length = String.length text in
  let slice start stop = String.sub text start (stop - start) in
  let bounds = function Atom (a, b) | List (a, b, _) -> (a, b) in
  let is_query = function
    | Atom (a, b) -> (
        match query with
        | None -> false
        | Some name ->
            let token = slice a b in
            text.[a] <> '"' && (token = name || token = "|" ^ name ^ "|"))
    | List _ -> false
  in
  let buffer = Buffer.create length in
  let copy start stop = Buffer.add_substring buffer text start (stop - start) in
  let rec render = function
    | Atom _ as atom when is_query atom -> Buffer.add_string buffer "false"
    | Atom (start, stop) -> copy start stop
    | List (_, _, [ Atom (a, b); name; List (_, _, []); Atom (c, d) ])
      when slice a b = "declare-fun" && is_query name && slice c d = "Bool" ->
        ()
    | List (_, _, Atom (a, b) :: body :: _) when slice a b = "!" -> render body
    | List (start, stop, children) -> render_between start stop children
  and render_between start stop children =
    let pos =
      List.fold_left
        (fun pos child ->
          let child_start, child_stop = bounds child in
          copy pos child_start;
          render child;
          child_stop)
        start children
    in
    copy pos stop
  in
  render_between 0 length (parse text);
  Buffer.contents buffer

let strip_annotations text = cleanup text
let eliminate_query ~name text = cleanup ~query:name text
