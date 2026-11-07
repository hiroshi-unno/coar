(* The labelled transition system llvm2lts builds, and its printing in the T2
   text format CoAR reads (-p lts*, -p lts*bv).

   Values are integers: bit-vectors of a stated width in BV mode,
   mathematical integers in the Int modes.  T2 has no conditional expression and no
   Boolean values, so a choice is two transitions guarded by a condition and
   its negation. *)

(* How an Int mode reads the IR's integers:
   - Plain: as mathematical integers, without wrap-around; bit operations
     are outside it;
   - Bitwise: the same, with the bit operations read in infinite two's
     complement (the integer's i-th bit is floor(x / 2^i) mod 2);
   - Wrap_unsigned: every iN value as its unsigned representative in
     [0, 2^N), so that arithmetic wraps as the IR's does; an operation the
     IR marks nsw is assumed not to overflow as signed (the C semantics of
     signed arithmetic, whose overflow is undefined);
   - Wrap_all: the same, with nsw not read, so signed arithmetic wraps too
     (two's complement, as gcc -fwrapv). *)
type ints = Plain | Bitwise | Wrap_unsigned | Wrap_all

type mode = Bv | Int of ints

type expr =
  | Var of string
  | Const of string  (** a decimal literal, possibly negative *)
  | Nondet of string  (** [nondet], or a sized one such as [nondet_int] *)
  | Neg of expr
  | Infix of string * expr * expr
      (** [+ - * / %] (signed in BV mode), [udiv urem] *)
  | Apply of string * string list * expr list
      (** [shl(e, e)], [extract(h, l, e)], [sign_extend(m, n, e)], ...: the
          name, integer parameters, then the arguments *)

type cond =
  | True
  | Compare of string * expr * expr
      (** [== != < <= > >=] (signed in BV mode), [ult ule ugt uge] *)
  | And of cond * cond
  | Or of cond * cond
  | Not of cond

type command = Assign of string * expr | Assume of cond

type transition = { src : string; commands : command list; dst : string }

type t = {
  start : string;
  error : string option;
  widths : (string * int) list;  (** BV mode: every scalar variable's width *)
  arrays : (string * int) list;
      (** every array variable, with its element width in BV mode (indices
          are 64 bits wide) *)
  transitions : transition list;
}

let conj a b = match (a, b) with True, c | c, True -> c | _ -> And (a, b)

let rec pp_expr buf = function
  | Var x -> Buffer.add_string buf x
  | Const c ->
      if c <> "" && c.[0] = '-' then (
        Buffer.add_string buf "(-";
        Buffer.add_string buf (String.sub c 1 (String.length c - 1));
        Buffer.add_char buf ')')
      else Buffer.add_string buf c
  | Nondet name ->
      Buffer.add_string buf name;
      Buffer.add_string buf "()"
  | Neg e ->
      Buffer.add_string buf "(-";
      pp_expr buf e;
      Buffer.add_char buf ')'
  | Infix (op, a, b) ->
      Buffer.add_char buf '(';
      pp_expr buf a;
      Printf.bprintf buf " %s " op;
      pp_expr buf b;
      Buffer.add_char buf ')'
  | Apply (name, params, args) ->
      Buffer.add_string buf name;
      Buffer.add_char buf '(';
      List.iteri
        (fun i p ->
          if i > 0 then Buffer.add_string buf ", ";
          Buffer.add_string buf p)
        params;
      List.iteri
        (fun i a ->
          if i > 0 || params <> [] then Buffer.add_string buf ", ";
          pp_expr buf a)
        args;
      Buffer.add_char buf ')'

let rec pp_cond buf = function
  | True -> Buffer.add_string buf "0 == 0"
  | Compare (op, a, b) ->
      pp_expr buf a;
      Printf.bprintf buf " %s " op;
      pp_expr buf b
  | And (a, b) ->
      Buffer.add_char buf '(';
      pp_cond buf a;
      Buffer.add_string buf " && ";
      pp_cond buf b;
      Buffer.add_char buf ')'
  | Or (a, b) ->
      Buffer.add_char buf '(';
      pp_cond buf a;
      Buffer.add_string buf " || ";
      pp_cond buf b;
      Buffer.add_char buf ')'
  | Not c ->
      Buffer.add_string buf "!(";
      pp_cond buf c;
      Buffer.add_char buf ')'

let to_t2 lts =
  let buf = Buffer.create 4096 in
  Printf.bprintf buf "START: %s;\n" lts.start;
  List.iter (fun (x, n) -> Printf.bprintf buf "TYPE %s: bv(%d);\n" x n) lts.widths;
  Option.iter (fun e -> Printf.bprintf buf "ERROR: %s;\n" e) lts.error;
  List.iter
    (fun { src; commands; dst } ->
      Printf.bprintf buf "\nFROM: %s;\n" src;
      List.iter
        (function
          | Assign (x, e) ->
              Printf.bprintf buf "%s := " x;
              pp_expr buf e;
              Buffer.add_string buf ";\n"
          | Assume c ->
              Buffer.add_string buf "assume(";
              pp_cond buf c;
              Buffer.add_string buf ");\n")
        commands;
      Printf.bprintf buf "TO: %s;\n" dst)
    lts.transitions;
  Buffer.contents buf
