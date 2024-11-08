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
  let parse_buf filename lb =
    lb.Lexing.lex_curr_p <-
      {
        Lexing.pos_fname = filename;
        Lexing.pos_lnum = 1;
        Lexing.pos_cnum = 0;
        Lexing.pos_bol = 0;
      };
    Parser.hors Lexer.token lb
  in
  let rules, (ta : TreeAutomaton.t) =
    if true then (
      print @@ lazy (sprintf "--------------------\nFile: %s" filename);
      let inchan = In_channel.create filename in
      let tl =
        parse_buf (Filename.basename filename) @@ Lexing.from_channel inchan
      in
      In_channel.close inchan;
      tl)
    else parse_buf "" @@ Lexing.from_string @@ input_lines In_channel.stdin
  in
  RSFD ([], EHMTT.rsfd_of [] rules, ta)

let from_ehmtt_file ~print filename =
  let parse_buf filename lb =
    lb.Lexing.lex_curr_p <-
      {
        Lexing.pos_fname = filename;
        Lexing.pos_lnum = 1;
        Lexing.pos_cnum = 0;
        Lexing.pos_bol = 0;
      };
    Parser.hmtt Lexer.token lb
  in
  let rules, (trs : TTA.pre_trs), (*spec.*) (id_nt, main_typ) =
    if true then (
      print @@ lazy (sprintf "--------------------\nFile: %s" filename);
      let inchan = In_channel.create filename in
      let tl =
        parse_buf (Filename.basename filename) @@ Lexing.from_channel inchan
      in
      In_channel.close inchan;
      tl)
    else parse_buf "" @@ Lexing.from_string @@ input_lines In_channel.stdin
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
