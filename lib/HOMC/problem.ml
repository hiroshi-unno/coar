(* Higher-order model checking problems.  An [RSFD] is a higher-order recursion
   scheme with finite data (the input tree automaton, whose states serve as the
   data values, the rules, and the specification automaton the generated tree
   must satisfy); an [EHMTT] is an extended higher-order macro tree transducer
   with an input tree automaton and the refinement type of its start symbol,
   which the reducer turns into several RSFD problems.  The readers parse the
   [.hors] and EHMTT formats; [pr] prints an RSFD in the format the external
   model checkers read, and [reads_alternating] says which of them can read it.
   *)
open Core
open Common.Util
open Ast
open Automata

type t =
  | RSFD of TTA.trs * RSFD.t * TreeAutomaton.t
  | EHMTT of EHMTT.t * TTA.pre_trs * (Ident.tvar * Ident.tvar RefType.t)

type solution = Sat | Unsat | Unknown

let str_of_solution = function
  | Sat -> "sat"
  | Unsat -> "unsat"
  | Unknown -> "unknown"

(* Parse one input with [parse] from [ic], naming it [name] in positions and
   error messages.  [ic] is the caller's: it is neither closed nor read past
   what the parser consumes.  A syntax error prints the position before the
   exception is re-raised. *)
let parse_channel ?(token = Lexer.token) parse ~name ic =
  let lexbuf = Lexing.from_channel ic in
  Lexing.set_filename lexbuf name;
  try parse token lexbuf
  with e ->
    LexingHelper.print_error_information lexbuf;
    raise e

(* The tokens of a HORS file.  [case], [of], [coerce], [copy] and [gen] are
   keywords of the EHMTT language only: HorSat2's and TRecS's formats have no
   such constructs, and a scheme may name a terminal, a variable or a state
   so.  Read as keywords they made a terminal [copy] a tree copier and a
   terminal [gen] an input tree, which a scheme cannot contain, and the
   reader failed on a legal file. *)
let hors_token lexbuf =
  match Lexer.token lexbuf with
  | Parser.CASE -> Parser.LIDENT "case"
  | OF -> LIDENT "of"
  | COERCE -> LIDENT "coerce"
  | COPY -> LIDENT "copy"
  | GEN -> LIDENT "gen"
  | t -> t

let from_hors_channel ~name ic =
  let rules, (ta : TreeAutomaton.t) =
    parse_channel ~token:hors_token Parser.hors ~name ic
  in
  (* the rules have no case analysis (there is no input automaton), so no
     name of the reduction's enters *)
  RSFD ([], EHMTT.rsfd_of ~names:(EHMTT.names_for []) [] rules, ta)

(* [map_states f rules] applies [f] to every state the rules name: the target
   of a [coerce] and the state of a [gen]. *)
let map_states f (rules : EHMTT.t) : EHMTT.t =
  let rec term = function
    | EHMTT.Coerce (q, t, idx) -> EHMTT.Coerce (f q, term t, idx)
    | Tree q -> Tree (f q)
    | App (t1, t2) -> App (term t1, term t2)
    | Case (x, pats) ->
        Case (x, List.map pats ~f:(fun (c, (xs, t)) -> (c, (xs, term t))))
    | Copy t -> Copy (term t)
    | (Fd _ | Nonterm _ | Var _ | Term _ | VarOrTerm _) as t -> t
  in
  List.map rules ~f:(fun (nt, (xs, t)) -> (nt, (xs, term t)))

let rec map_reftype f = function
  | RefType.Base q -> RefType.Base (f q)
  | Func (t1, t2) -> Func (map_reftype f t1, map_reftype f t2)

(* The automaton of a [%BEGINX] section, whose text [text] begins at [pos] of
   the input [name].  The definitions are read by the regular tree expression
   reader (a syntax error names this input's line and column) and translated
   by [RegTreeExp.named_tta_of]: the translation [-p xmltype] prints, applied
   to each schema of the section, with a state for every defined type.  The
   transitions are those a [%BEGINA] section listing that automaton would
   give, so the rest of the reduction cannot tell the two apart.  States are renamed
   for the model checkers, whose automaton readers take a capitalised name
   for a non-terminal: the state of type [T] becomes [q] followed by [T], and
   the translation's other states keep their names [q<digits>], which cannot
   coincide with those.  Returns the transitions and the map from each type
   name to its state.  Raises [Failure] when the section cannot be read: with
   the input's line and column for a lexical or syntax error, with the input's
   name and the defect for no definition, a type defined twice or an
   undefined type. *)
let automaton_of_xtypes ~name (text, pos) =
  let defs =
    match Grammar.RegTreeExpReader.from_string ~name ~pos text with
    | Ok defs -> defs
    | Error err -> failwith (Error.to_string_hum err)
  in
  let state_of_type = List.map defs ~f:(fun (t, _) -> (t, "q" ^ t)) in
  let st q =
    Option.value ~default:q
    @@ List.Assoc.find ~equal:String.equal state_of_type q
  in
  let trs : TTA.pre_trs =
    List.concat_map (Grammar.RegTreeExp.named_tta_of defs) ~f:(fun (q, body) ->
        List.map body ~f:(fun (a, qs) -> (st q, (a, List.map qs ~f:st))))
  in
  (trs, state_of_type)

(* With a [%BEGINA] section a state is a lower-case name; an upper-case one
   names a type, which only a [%BEGINX] section defines, so it is refused
   here rather than read as a state no transition mentions.  With a
   [%BEGINX] section every state named by the specification, a [coerce] or a
   [gen] must be a defined type, and is replaced by that type's state. *)
let from_ehmtt_channel ~name ic =
  let rules, section, (*spec.*) (id_nt, main_typ) =
    parse_channel Parser.hmtt ~name ic
  in
  match section with
  | `Both (pos : Lexing.position) ->
      (* with both, a state named in one section and a state named in the
         other would share one name space, and nothing says whether a name
         meant the same state in both *)
      failwithf
        "%s:%d:%d: a %%BEGINA section and a %%BEGINX section in one file; give \
         the automaton by transitions or by type definitions, not both"
        name pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol + 1)
        ()
  | `Transitions (trs : TTA.pre_trs) ->
      let check q =
        let s = Ident.name_of_tvar q in
        if Char.is_uppercase s.[0] then
          failwithf
            "%s: %s names a type, but the automaton is given by a %%BEGINA \
             section, which defines no types (a type is a state only with a \
             %%BEGINX section)"
            name s ()
        else q
      in
      ignore (map_states check rules : EHMTT.t);
      ignore (map_reftype check main_typ : Ident.tvar RefType.t);
      EHMTT (rules, trs, (id_nt, main_typ))
  | `XTypes section ->
      let trs, state_of_type = automaton_of_xtypes ~name section in
      let to_state where q =
        let s = Ident.name_of_tvar q in
        match List.Assoc.find ~equal:String.equal state_of_type s with
        | Some q' -> Ident.Tvar q'
        | None ->
            failwithf
              "%s: %s names %s, which is not a type defined in the %%BEGINX \
               section"
              name where s ()
      in
      EHMTT
        ( map_states (to_state "a coerce or gen") rules,
          trs,
          (id_nt, map_reftype (to_state "the %BEGINT specification") main_typ)
        )

(* The file readers own the channel they open and close it on every exit. *)
let from_hors_file ~print filename =
  print @@ lazy (sprintf "--------------------\nFile: %s" filename);
  In_channel.with_file filename
    ~f:(from_hors_channel ~name:(Filename.basename filename))

let from_ehmtt_file ~print filename =
  print @@ lazy (sprintf "--------------------\nFile: %s" filename);
  In_channel.with_file filename
    ~f:(from_ehmtt_channel ~name:(Filename.basename filename))

(* Standard input is always read as an EHMTT, as the original EHMTT verifier
   read it: the two formats cannot be told apart from their first section
   (both open with [%BEGING]), and an extension, which decides for a file,
   is not available.  Standard input is not closed. *)
let from_ehmtt_stdin ~print () =
  print @@ lazy "--------------------\nFile: (standard input)";
  from_ehmtt_channel ~name:"stdin" In_channel.stdin

(* The two external higher-order model checkers this tool drives read *different*
   dialects of the same file extension, and each rejects the other's.  Which one
   a file is written in is decided by the automaton section at its end: a
   [%BEGINA] section is a trivial tree automaton, which TRecS reads and HorSat2's
   converter refuses; [%BEGINR] together with [%BEGINATA] is an alternating tree
   automaton, which HorSat2 reads and TRecS's lexer refuses with "unknown token
   %".  Neither refusal is legible on its own -- both arrive as a short stdout
   that the wrappers report as a failed verification -- so each wrapper checks
   this first and says which backend to use.  [reads_alternating] is what
   HorSat2 requires and TRecS cannot take. *)
let reads_alternating = function
  | RSFD (_, _, TreeAutomaton.ATA _) -> true
  | _ -> false

let dialect_str_of = function
  | RSFD (_, _, TreeAutomaton.TTA _) ->
      "a trivial tree automaton (a %BEGINA section)"
  | RSFD (_, _, TreeAutomaton.ATA _) ->
      "an alternating tree automaton (%BEGINR and %BEGINATA sections)"
  | RSFD (_, _, TreeAutomaton.RTA _) -> "a ranked tree automaton"
  | EHMTT _ -> "an EHMTT"

let pr ppf = function
  | RSFD (trs_in, rules, trs_out) ->
      Format.fprintf ppf "@[<v>";
      Format.fprintf ppf "%%BEGING@,";
      RSFD.pr_rules trs_in ppf rules;
      Format.fprintf ppf "%%ENDG@,";
      Format.fprintf ppf "@,";
      TreeAutomaton.pr ppf trs_out;
      Format.fprintf ppf "@]@."
  | EHMTT _ -> failwith "not implemented"
