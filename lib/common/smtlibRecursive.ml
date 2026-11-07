(* Z3's indexed spelling of a recursive function's application, and the
   standard one.  Z3 prints a solver's assertions with every application of a
   function it holds by [define-funs-rec] spelled as an indexed identifier,
   [((_ f 0) x)], because the declaration carries one integer flag and its
   printer spells any declaration with parameters as [(_ name p)].  SMT-LIB 2.6
   applies a function defined by [define-fun-rec] or [define-funs-rec] by its
   plain symbol, [(f x)]; cvc5 refuses the indexed spelling ("Unknown indexed
   function"), while Z3 reads both. *)
open Core

(* [unindex_recursive_text text] rewrites every [(_ f k)] of [text] to [f]
   when [f] is a function the text defines by [define-funs-rec] or
   [define-fun-rec] and [k] is 0 or 1.

   Why.  Z3 prints an application of a recursive function as an indexed
   identifier, [((_ len 0) x)]: its declaration carries one integer
   parameter, 1 when Z3 generated the definition itself and 0 otherwise, and
   its printer spells any declaration with parameters as [(_ name p)].  No
   cvc5 reads that ("Unknown indexed function"; 1.0.4 and 1.4.2 alike), so
   without the rewrite no question that mentions a recursive function gets an
   answer.  The parameter is a flag of the declaration, not part of which
   function is meant: the definition the text gives under the name [f] is the
   one applied, so writing the plain [f] asks the same question.

   Contract.  [Some t]: [t] is [text] with exactly those spans replaced by
   the symbol's own token (quoting kept), every other byte unchanged; a text
   with no such occurrence is returned byte-identical, and a text that spells
   neither [define-fun-rec] nor [define-funs-rec] is not even parsed.  [None]
   (a caller asking another solver does not ask the question) when the rewrite could change the meaning: an [f] spelled
   with both indices (two declarations Z3 kept apart would become one), or an
   [f] the text also binds or declares in any other way (a parameter, a
   quantified or [let] variable, another declaration, a datatype symbol),
   which the plain [f] could denote instead; and when the text does not
   parse.  An indexed symbol with another index, or whose name no recursive
   definition gives, is left as it is. *)
let unindex_recursive_text text =
  let module S = Smtlib in
  let token = function
    | S.Atom (a, b) -> Some (String.sub text ~pos:a ~len:(b - a))
    | S.List _ -> None
  in
  let is node name = Option.equal String.equal (token node) (Some name) in
  let bare name = String.strip ~drop:(Char.equal '|') name in
  (* every name the text binds or declares, with multiplicity, and the
     recursive definitions among them *)
  let bound = Hashtbl.create (module String) in
  let recursive = ref [] in
  let add node =
    Option.iter (token node) ~f:(fun name ->
        if not (String.is_prefix name ~prefix:"\"") then
          Hashtbl.incr bound (bare name))
  in
  let add_rec node =
    add node;
    Option.iter (token node) ~f:(fun name ->
        recursive := bare name :: !recursive)
  in
  let firsts = function
    | S.List (_, _, entries) ->
        List.iter entries ~f:(function
          | S.List (_, _, name :: _) -> add name
          | _ -> ())
    | _ -> ()
  in
  let rec all = function
    | S.Atom _ as node -> add node
    | S.List (_, _, nodes) -> List.iter nodes ~f:all
  in
  let rec declarations = function
    | S.Atom _ -> ()
    | S.List (_, _, head :: name :: args :: rest) when is head "define-fun-rec"
      ->
        add_rec name;
        firsts args;
        List.iter rest ~f:declarations
    | S.List (_, _, head :: name :: args :: rest) when is head "define-fun" ->
        add name;
        firsts args;
        List.iter rest ~f:declarations
    | S.List (_, _, head :: name :: _)
      when is head "declare-fun" || is head "declare-const"
           || is head "declare-sort" || is head "define-sort" ->
        add name
    | S.List (_, _, head :: rest)
      when is head "declare-datatype" || is head "declare-datatypes" ->
        List.iter rest ~f:all
    | S.List (_, _, head :: S.List (_, _, signatures) :: rest)
      when is head "define-funs-rec" ->
        List.iter signatures ~f:(function
          | S.List (_, _, name :: args :: _) ->
              add_rec name;
              firsts args
          | _ -> ());
        List.iter rest ~f:declarations
    | S.List (_, _, nodes) ->
        (match nodes with
        | head :: bindings :: _
          when is head "forall" || is head "exists" || is head "lambda"
               || is head "let" ->
            firsts bindings
        | _ -> ());
        List.iter nodes ~f:declarations
  in
  if
    not
      (String.is_substring text ~substring:"define-fun-rec"
      || String.is_substring text ~substring:"define-funs-rec")
  then Some text
  else
    match S.parse text with
    | exception Invalid_argument _ -> None
    | nodes ->
        List.iter nodes ~f:declarations;
        let recursive = Set.of_list (module String) !recursive in
        (* the indexed occurrences: span, the symbol's token, its index *)
        let rec occurrences acc = function
          | S.Atom _ -> acc
          | S.List (a, b, [ head; name; index ])
            when is head "_"
                 && Option.exists (token name) ~f:(fun n ->
                     Set.mem recursive (bare n))
                 && (is index "0" || is index "1") ->
              ( a,
                b,
                Option.value_exn (token name),
                Option.value_exn (token index) )
              :: acc
          | S.List (_, _, nodes) -> List.fold nodes ~init:acc ~f:occurrences
        in
        let found =
          if Set.is_empty recursive then []
          else List.fold nodes ~init:[] ~f:occurrences
        in
        let indices =
          List.fold found
            ~init:(Map.empty (module String))
            ~f:(fun m (_, _, name, index) ->
              Map.add_multi m ~key:(bare name) ~data:index)
        in
        if
          Map.existsi indices ~f:(fun ~key ~data ->
              Option.value (Hashtbl.find bound key) ~default:0 > 1
              || List.length (List.dedup_and_sort data ~compare:String.compare)
                 > 1)
        then None
        else if List.is_empty found then Some text
        else
          let buffer = Buffer.create (String.length text) in
          let pos =
            List.fold
              (List.sort found ~compare:(fun (a, _, _, _) (b, _, _, _) ->
                   Int.compare a b))
              ~init:0
              ~f:(fun pos (a, b, name, _) ->
                Buffer.add_substring buffer text ~pos ~len:(a - pos);
                Buffer.add_string buffer name;
                b)
          in
          Buffer.add_substring buffer text ~pos ~len:(String.length text - pos);
          Some (Buffer.contents buffer)

(* [standard_text text]: [text] in the standard spelling when
   [unindex_recursive_text] gives one, and otherwise [text] itself headed by a
   comment line saying that its recursive applications keep Z3's spelling.
   For a text written out to be read again (a dump, a replay); every byte
   beyond the rewritten spans is [text]'s. *)
let standard_text text =
  match unindex_recursive_text text with
  | Some t -> t
  | None ->
      "; recursive applications kept in Z3's indexed spelling: the plain name \
       could denote another symbol here, or the text does not parse\n" ^ text
