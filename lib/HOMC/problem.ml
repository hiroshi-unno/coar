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

let from_hors_file ~print filename =
  let rules, (ta : TreeAutomaton.t) =
    if true then (
      print @@ lazy (sprintf "--------------------\nFile: %s" filename);
      let res =
        In_channel.with_file filename ~f:(fun ic ->
            let lexbuf = Lexing.from_channel ic in
            Lexing.set_filename lexbuf (Filename.basename filename);
            try Parser.hors Lexer.token lexbuf
            with e ->
              LexingHelper.print_error_information lexbuf;
              raise e)
      in
      res)
    else
      let res =
        let lexbuf = Lexing.from_string @@ input_lines In_channel.stdin in
        Lexing.set_filename lexbuf "stdin";
        try
          let res = Parser.hors Lexer.token lexbuf in
          res
        with e ->
          LexingHelper.print_error_information lexbuf;
          raise e
      in
      res
  in
  RSFD ([], EHMTT.rsfd_of [] rules, ta)

let from_ehmtt_file ~print filename =
  let rules, (trs : TTA.pre_trs), (*spec.*) (id_nt, main_typ) =
    if true then (
      print @@ lazy (sprintf "--------------------\nFile: %s" filename);
      let res =
        In_channel.with_file filename ~f:(fun ic ->
            let lexbuf = Lexing.from_channel ic in
            Lexing.set_filename lexbuf (Filename.basename filename);
            try Parser.hmtt Lexer.token lexbuf
            with e ->
              LexingHelper.print_error_information lexbuf;
              raise e)
      in
      res)
    else
      let res =
        let lexbuf = Lexing.from_string @@ input_lines In_channel.stdin in
        Lexing.set_filename lexbuf "stdin";
        try
          let res = Parser.hmtt Lexer.token lexbuf in
          res
        with e ->
          LexingHelper.print_error_information lexbuf;
          raise e
      in
      res
  in
  EHMTT (rules, trs, (id_nt, main_typ))

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
