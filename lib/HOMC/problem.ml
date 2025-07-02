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
        let ic = In_channel.create filename in
        let lexbuf = Lexing.from_channel ic in
        Lexing.set_filename lexbuf (Filename.basename filename);
        try
          let res = Parser.hors Lexer.token lexbuf in
          In_channel.close ic;
          res
        with e ->
          LexingHelper.print_error_information lexbuf;
          In_channel.close ic;
          raise e
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
        let ic = In_channel.create filename in
        let lexbuf = Lexing.from_channel ic in
        Lexing.set_filename lexbuf (Filename.basename filename);
        try
          let res = Parser.hmtt Lexer.token lexbuf in
          In_channel.close ic;
          res
        with e ->
          LexingHelper.print_error_information lexbuf;
          In_channel.close ic;
          raise e
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

let pr ppf = function
  | RSFD (trs_in, rules, trs_out) ->
      Format.fprintf ppf "@[<v>";
      Format.fprintf ppf "%%BEGING@,";
      RSFD.pr_rules trs_in ppf rules;
      Format.fprintf ppf "%%ENDG@,";
      Format.fprintf ppf "@,";
      TreeAutomaton.pr ppf trs_out;
      Format.fprintf ppf "@]@."
  | EHMTT _ -> failwith "not implmented"
