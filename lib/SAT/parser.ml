(* A reader for DIMACS CNF and its quantified extensions QDIMACS ([a]/[e]
   blocks) and DQDIMACS ([d x deps] blocks, a Henkin existential with an
   explicit dependency set).

   [parse] pulls lines from [inp] until [End_of_file] and returns the
   quantifier prefix in file order and the clauses, each as its negative and
   positive variable names (signs stripped).  A clause is closed only by the
   token [0], whatever the line layout; a prefix line must precede every
   clause ([no_quant] refuses quantifiers once a clause has been read, or from
   the start for plain CNF), and a dependency set may name only universals
   declared before it.  The header's counts are checked and only reported. *)
open Core
open Common.Ext

type quant = (string list, string list * string list option) Either.t

let rec exhaust inp =
  try
    ignore @@ inp ();
    exhaust inp
  with End_of_file -> ()

let elim_last_zero cl line =
  match List.rest_last_opt cl with
  | None -> failwith @@ "each line must end with 0: " ^ line
  | Some (literals, last) ->
      if String.(last = "0") then literals
      else failwith @@ "each line must end with 0: " ^ line

(* The negative literals and the positive ones, from the tokens of one clause.
   A token is a variable name with an optional leading minus; [0] never reaches
   here, because it is what ended the clause. *)
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
   each [a]/[e]/[d] block is a line of its own ending in 0. *)
let rec parse ?(no_quant = false) ?(pending = []) ?(header = None)
    ?(print = fun (_ : string lazy_t) -> ()) uqbs quants clauses inp =
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
        String.split_on_chars line ~on:[ ' '; '\t'; '\r' ]
        |> List.filter ~f:(Stdlib.( <> ) "")
        |> function
        | [] | "c" :: _ ->
            parse ~no_quant ~pending ~header ~print uqbs quants clauses inp
        | "p" :: _ :: nv :: nc :: _ ->
            let header =
              match (int_of_string_opt nv, int_of_string_opt nc) with
              | Some nv, Some nc -> Some (nv, nc)
              | _ -> header
            in
            parse ~no_quant ~pending ~header ~print uqbs quants clauses inp
        | "p" :: _ ->
            parse ~no_quant ~pending ~header ~print uqbs quants clauses inp
        | "%" :: _ ->
            exhaust inp;
            raise End_of_file
        | "a" :: ns ->
            let ns = elim_last_zero ns line in
            if no_quant then failwith @@ "quantifiers not allowed: " ^ line
            else if List.exists ns ~f:(fun l -> Stdlib.(String.get l 0 = '-'))
            then failwith @@ "illegal quantification: " ^ line
            else
              parse ~no_quant ~pending ~header ~print (ns @ uqbs)
                (First ns :: quants) clauses inp
        | "e" :: ns ->
            let ns = elim_last_zero ns line in
            if no_quant then failwith @@ "quantifiers not allowed: " ^ line
            else if List.exists ns ~f:(fun l -> Stdlib.(String.get l 0 = '-'))
            then failwith @@ "illegal quantification: " ^ line
            else
              parse ~no_quant ~pending ~header ~print uqbs
                (Second (ns, None (*Some uqbs*)) :: quants)
                clauses inp
        | "d" :: n :: ns ->
            let ns = elim_last_zero ns line in
            if no_quant then failwith @@ "quantifiers not allowed: " ^ line
            else if
              (not @@ List.is_empty @@ List.diff ns uqbs)
              || List.exists (n :: ns) ~f:(fun l ->
                  Stdlib.(String.get l 0 = '-'))
            then failwith @@ "illegal dependency quantification: " ^ line
            else
              parse ~no_quant ~pending ~header ~print uqbs
                (Second ([ n ], Some ns) :: quants)
                clauses inp
        | ns ->
            (* [acc] holds the literals of the clause being read, reversed *)
            let rec consume acc clauses = function
              | [] -> (acc, clauses)
              | "0" :: rest ->
                  consume [] (clause_of (List.rev acc) :: clauses) rest
              | literal :: rest ->
                  if String.(literal = "-0") then
                    failwith @@ "-0 is not a literal: " ^ line
                  else consume (literal :: acc) clauses rest
            in
            let pending, clauses = consume pending clauses ns in
            parse ~no_quant:true ~pending ~header ~print uqbs quants clauses inp
        )
  with End_of_file -> finish ()
