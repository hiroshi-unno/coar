(* A reader for DIMACS CNF and its quantified extensions QDIMACS ([a]/[e]
   blocks) and DQDIMACS ([d x deps] blocks, a Henkin existential with an
   explicit dependency set).

   [parse] pulls lines from [inp] until [End_of_file] and returns the
   quantifier prefix in file order and the clauses, each as its negative and
   positive variable names (signs stripped).  A clause is closed only by the
   token [0], whatever the line layout; a prefix line must precede every
   clause ([no_quant] refuses quantifiers once a clause has been read, or from
   the start for plain CNF), a variable is quantified at most once, and a
   dependency set may name only universals declared before it.  The header's
   counts are checked and only reported.

   Every variable name returned is the canonical decimal spelling of a positive
   integer (no sign, no leading zero), and a literal or a prefix entry that is
   not a decimal integer is refused, so two names are the same variable exactly
   when they denote the same number. *)
open Core
open Common.Ext

type quant = (string list, string list * string list option) Either.t

let rec exhaust inp =
  try
    ignore @@ inp ();
    exhaust inp
  with End_of_file -> ()

(* A DIMACS literal is a decimal integer, and its variable is the number, not
   the spelling: [01] and [1] are one variable.  Keeping the token as the name
   made [01 0 -1 0] two unit clauses over two variables, answered sat where
   z3's own DIMACS reader says unsatisfiable.  So a token is checked to be an
   optional minus followed by decimal digits and returned with its leading
   zeros removed; [0] (however spelled) is returned as ["0"] and [-0] as
   ["-0"], for the caller to read as a terminator or refuse.  OCaml's
   [int_of_string] is not used to check it, since it also accepts [0x1], [0b1],
   [1_0] and [+1], none of which is DIMACS. *)
let canonical_literal line token =
  let negative = String.is_prefix token ~prefix:"-" in
  let digits = if negative then String.drop_prefix token 1 else token in
  if String.is_empty digits || not (String.for_all digits ~f:Char.is_digit) then
    failwith @@ "not a DIMACS literal: " ^ token ^ " in " ^ line
  else
    let digits =
      match String.lstrip digits ~drop:(Char.equal '0') with
      | "" -> "0"
      | digits -> digits
    in
    if negative then "-" ^ digits else digits

(* The variables of a prefix line, which is its tokens closed by one [0]: each
   must be a positive integer, so a sign, an interior [0] or a missing final
   [0] is refused rather than read as a variable named [0] or [-1]. *)
let prefix_vars cl line =
  match List.rest_last_opt @@ List.map cl ~f:(canonical_literal line) with
  | Some (vars, "0") ->
      if
        List.exists vars ~f:(fun v ->
            String.(v = "0") || String.is_prefix v ~prefix:"-")
      then failwith @@ "illegal quantification: " ^ line
      else vars
  | _ -> failwith @@ "each line must end with 0: " ^ line

(* QDIMACS and DQDIMACS quantify a variable at most once.  Accepting a second
   binding gave the file a meaning of its own -- [a 1 0] then [e 1 0] read as
   a universal immediately shadowed by an existential, a [d] line overriding
   an [e] -- where the format has none, so it is refused.  [bound] holds every
   variable quantified so far. *)
let bind_fresh bound vars line =
  List.iter vars ~f:(fun v ->
      if Hash_set.mem bound v then
        failwith @@ "variable " ^ v ^ " is quantified twice: " ^ line
      else Hash_set.add bound v)

(* The negative literals and the positive ones, from the tokens of one clause.
   A token is a canonical variable name with an optional leading minus; [0]
   never reaches here, because it is what ended the clause. *)
let clause_of tokens =
  List.partition_tf tokens ~f:(fun literal ->
      Stdlib.(String.get literal 0 = '-'))
  |> fun (negatives, positives) ->
  ( List.map negatives ~f:(fun literal ->
        String.sub literal ~pos:1 ~len:(String.length literal - 1)),
    positives )

(* DIMACS ends a clause with [0] and separates its numbers with whitespace, so
   one line may hold several clauses and one clause may span several lines --
   the layout carries no meaning.  Reading a line as a clause instead made
   [1 0 -1 0] a single clause of three literals [1], [-1] and a variable named
   [0] that the file never declares: a tautology, so [x1 and not x1] answered
   sat on all three backends where z3's own reader says unsatisfiable, and
   [0 1 0] lost the empty clause in front.  A clause split over two lines was
   rejected outright.  So the tokens are consumed one at a time and [0] is the
   only thing that closes a clause; [pending] carries an unfinished one to the
   next line.

   The quantifier prefix keeps its line discipline, which is the format's:
   each [a]/[e]/[d] block is a line of its own ending in 0.

   A comment is a line whose first character is [c], whatever follows it: the
   format does not ask for a blank after the [c], and matching the token ["c"]
   instead read [c-----] or [cthis] as the first literals of a clause, so a
   comment between [1 0] and [-1 0] became part of a satisfiable clause and the
   file answered sat where it is unsatisfiable.  Leading blanks are tolerated,
   as before. *)
let rec parse ?(no_quant = false) ?(pending = []) ?(header = None)
    ?(bound = Hash_set.Poly.create ()) ?(print = fun (_ : string lazy_t) -> ())
    uqbs quants clauses inp =
  let finish () =
    if not (List.is_empty pending) then
      failwith @@ "the last clause is not terminated by 0: "
      ^ String.concat ~sep:" " (List.rev pending);
    let clauses = List.rev clauses in
    (* The header is advisory: it is not needed to read the file, and z3's own
       reader accepts a file whose counts are wrong, so disagreeing with it is
       reported and not refused.  Three of the DIMACS files in this repository
       disagree with their own headers. *)
    (match header with
    | Some (nvars, nclauses) ->
        let count = List.length clauses in
        if count <> nclauses then
          print
          @@ lazy
               (Printf.sprintf
                  "the header declares %d clauses and the file has %d" nclauses
                  count);
        let max_var =
          List.fold clauses ~init:0 ~f:(fun acc (ns, ps) ->
              List.fold (ns @ ps) ~init:acc ~f:(fun acc v ->
                  match int_of_string_opt v with
                  | Some n -> max acc (abs n)
                  | None -> acc))
        in
        if max_var > nvars then
          print
          @@ lazy
               (Printf.sprintf
                  "the header declares %d variables and the file uses %d" nvars
                  max_var)
    | None -> ());
    (List.rev quants, clauses)
  in
  try
    match inp () with
    | line -> (
        String.split_on_chars line ~on:[ ' '; '\t'; '\r'; '\011'; '\012' ]
        |> List.filter ~f:(Stdlib.( <> ) "")
        |> function
        | [] ->
            parse ~no_quant ~pending ~header ~bound ~print uqbs quants clauses
              inp
        | first :: _ when Char.equal (String.get first 0) 'c' ->
            parse ~no_quant ~pending ~header ~bound ~print uqbs quants clauses
              inp
        | "p" :: _ :: nv :: nc :: _ ->
            let header =
              match (int_of_string_opt nv, int_of_string_opt nc) with
              | Some nv, Some nc -> Some (nv, nc)
              | _ -> header
            in
            parse ~no_quant ~pending ~header ~bound ~print uqbs quants clauses
              inp
        | "p" :: _ ->
            parse ~no_quant ~pending ~header ~bound ~print uqbs quants clauses
              inp
        | first :: _ when Char.equal (String.get first 0) '%' ->
            exhaust inp;
            raise End_of_file
        | "a" :: ns ->
            if no_quant then failwith @@ "quantifiers not allowed: " ^ line
            else
              let ns = prefix_vars ns line in
              bind_fresh bound ns line;
              parse ~no_quant ~pending ~header ~bound ~print (ns @ uqbs)
                (First ns :: quants) clauses inp
        | "e" :: ns ->
            if no_quant then failwith @@ "quantifiers not allowed: " ^ line
            else
              let ns = prefix_vars ns line in
              bind_fresh bound ns line;
              parse ~no_quant ~pending ~header ~bound ~print uqbs
                (Second (ns, None (*Some uqbs*)) :: quants)
                clauses inp
        | "d" :: ns -> (
            if no_quant then failwith @@ "quantifiers not allowed: " ^ line
            else
              match prefix_vars ns line with
              | n :: ns when List.is_empty @@ List.diff ns uqbs ->
                  bind_fresh bound [ n ] line;
                  parse ~no_quant ~pending ~header ~bound ~print uqbs
                    (Second ([ n ], Some ns) :: quants)
                    clauses inp
              | _ ->
                  failwith @@ "illegal dependency quantification: " ^ line)
        | ns ->
            (* [acc] holds the literals of the clause being read, reversed *)
            let rec consume acc clauses = function
              | [] -> (acc, clauses)
              | token :: rest -> (
                  match canonical_literal line token with
                  | "0" -> consume [] (clause_of (List.rev acc) :: clauses) rest
                  | "-0" -> failwith @@ "-0 is not a literal: " ^ line
                  | literal -> consume (literal :: acc) clauses rest)
            in
            let pending, clauses = consume pending clauses ns in
            parse ~no_quant:true ~pending ~header ~bound ~print uqbs quants
              clauses inp
        )
  with End_of_file -> finish ()
