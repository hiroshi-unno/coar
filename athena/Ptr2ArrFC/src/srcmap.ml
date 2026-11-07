(* The source map of the record: for every statement of the output, where it
   is printed (line and column of its first character in the output file), the
   role it plays for a witness of the input, and the position in the input
   file of the input statement it comes from.

   Positions.
   - Output: counted while the output is printed. The printer is Frama-C's,
     extended so that each statement opens a zero-width semantic tag right
     before its first character (after its labels); with tag marking on, the
     formatter calls the marking function when it actually writes the tag,
     in order with the text around it, and the output functions count every
     character written. So the position read there is the one in the file,
     whatever the formatter's line breaking decided. A tab counts as one
     column, as does every byte.
   - Input: a physical line and column of the input file, in bytes (Frama-C
     counts columns in bytes; a multibyte character before the position
     counts as its bytes). A statement's own location in Frama-C is not its
     first character: an assignment carries the location of its right-hand
     side, an [if] that of its condition, a loop's condition [if] that of the
     condition. The untyped AST keeps the full extent of every statement and
     expression, so a statement is mapped to the innermost untyped statement
     whose extent holds the start of its location, and a target to the
     innermost statement or full expression (a condition, a for clause, a
     returned value, an initialiser), as a witness's target location asks.
   - Extents and locations are positions in the file Frama-C lexed. A .c
     input is preprocessed first, so they are positions in the preprocessed
     text: the line in the input comes from the preprocessor's line markers,
     and the column is found by matching the tokens of the preprocessed line
     against those of the input's line (see [align]); a position inside a
     macro's expansion is placed at the macro's name. A .i input is lexed as it is, and its
     positions are the physical ones, line markers notwithstanding: a
     witness locates a statement by counting lines in the file it was given.
     A statement in another file (a header of a .c input) or made by the
     transformation has no input position.

   Roles.
   - loop-head: a loop the input wrote with [for] or [while]. Its head, where
     the output's loop starts an iteration, is right before the condition is
     evaluated, since the front end puts the condition first in the body. A
     [do] loop evaluates its condition at the end of the body, so its loop is
     [other].
   - branch: an [if] that evaluates the whole controlling expression of an
     input [if], [while], [do] or [for] and branches on it: the only [if] the
     front end made from that expression (an expression with [&&], [||] or
     [?:] becomes several, none of which evaluates the whole). Such an [if]
     has the input's expression as its condition and the input's branches in
     the input's order; cond_negated says whether the output prints its
     condition negated ([if (! c) break;], or [if (! c) s] for an empty
     then-branch), which the printer decides.
   - target: where a property is violated. In the normal mode, a call of the
     input's reach_error (unreach-call). With --check-overflow, a call of an
     overflow check function (no-overflow). In --memory-safety and
     --memory-cleanup, a call of a check function whose body reaches a
     violation marker, with the properties of those markers (one entry per
     property), including the end checks. The markers themselves are called
     inside generated functions that many places call, so the call in the
     program is the place that directly holds the violation; its input
     position is the statement or full expression it guards. The end check
     after the return from main is placed at the input main's return.
   - call: a call of a function of the input (defined or only declared)
     made at a position in the input.
   - other: anything else.

   Contract: [analyse] runs with the input as the current project and reads
   the output project [prj] beside it; [print] writes [prj] and returns the
   output positions; [to_json] assembles the field. The statements listed are
   those the output prints: a statement printing nothing (an empty statement,
   a [break] folded into a [while] head) has no position, and a block is not
   listed (its statements are). *)

open Cil_types

(* ---- files ---- *)

let lines_cache : (string, string array) Hashtbl.t = Hashtbl.create 4

(* The lines of the file [path], without their line terminators; empty when
   it cannot be read. *)
let lines_of path =
  match Hashtbl.find_opt lines_cache path with
  | Some l -> l
  | None ->
      let l =
        try
          let ic = open_in_bin path in
          Fun.protect
            ~finally:(fun () -> close_in ic)
            (fun () ->
              let acc = ref [] in
              (try
                 while true do
                   let s = input_line ic in
                   let n = String.length s in
                   acc := (if n > 0 && s.[n - 1] = '\r' then String.sub s 0 (n - 1) else s) :: !acc
                 done
               with End_of_file -> ());
              Array.of_list (List.rev !acc))
        with Sys_error _ -> [||]
      in
      Hashtbl.replace lines_cache path l;
      l

let line_text path n =
  let l = lines_of path in
  if n >= 1 && n <= Array.length l then Some l.(n - 1) else None

let is_space c = c = ' ' || c = '\t' || c = '\011' || c = '\012' || c = '\r'

(* The tokens of a line, as (text, first column from 0): words (identifiers
   and numbers), string and character literals, comments, and single
   characters otherwise. *)
let tokens line =
  let n = String.length line in
  let word c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_' in
  let rec go i acc =
    if i >= n then List.rev acc
    else if is_space line.[i] then go (i + 1) acc
    else
      let j =
        if word line.[i] then
          let rec w j = if j < n && word line.[j] then w (j + 1) else j in
          w i
        else if line.[i] = '"' || line.[i] = '\'' then
          let q = line.[i] in
          let rec lit j =
            if j >= n then n
            else if line.[j] = '\\' then lit (j + 2)
            else if line.[j] = q then j + 1
            else lit (j + 1)
          in
          lit (i + 1)
        else if i + 1 < n && line.[i] = '/' && line.[i + 1] = '*' then
          let rec com j =
            if j + 1 >= n then n else if line.[j] = '*' && line.[j + 1] = '/' then j + 2 else com (j + 1)
          in
          com (i + 2)
        else if i + 1 < n && line.[i] = '/' && line.[i + 1] = '/' then n
        else i + 1
      in
      go j ((String.sub line i (min j n - i), i) :: acc)
  in
  go 0 []

(* The column (from 1) in [orig] of the character at column [col] of [pp],
   a preprocessed copy of the same line. The preprocessor keeps the
   column of a line's first token, squeezes the whitespace between tokens
   and replaces each macro use by its expansion, so the two lines share
   their tokens outside the expansions: the tokens are matched by a longest
   common subsequence, and a token of [pp] that is matched has the column of
   its partner. The line's first token is the first token of [orig]: the
   preprocessor writes it at its column, or, when a macro's expansion
   starts the line, where the macro's name was. A token that follows tokens
   of [orig] the alignment skips, the first of them a word, starts a
   macro's expansion and is placed at the macro's name, and so is a token
   not matched, which is inside the latest expansion (or keeps [col] when
   none came before it). *)
let align ~pp ~orig col =
  let a = Array.of_list (tokens pp) and b = Array.of_list (tokens orig) in
  let na = Array.length a and nb = Array.length b in
  match Array.find_index (fun (_, c) -> c = col - 1) a with
  | None -> col
  | Some 0 when nb > 0 -> snd b.(0) + 1
  | Some k ->
      (* lcs.(i).(j): the longest common subsequence of a.(i..) and b.(j..) *)
      let lcs = Array.make_matrix (na + 1) (nb + 1) 0 in
      for i = na - 1 downto 0 do
        for j = nb - 1 downto 0 do
          lcs.(i).(j) <-
            (if fst a.(i) = fst b.(j) then lcs.(i + 1).(j + 1) + 1
             else max lcs.(i + 1).(j) lcs.(i).(j + 1))
        done
      done;
      let word (t, _) =
        t <> "" && (match t.[0] with 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false)
      in
      (* along an optimal alignment up to token k ([last], the partner in
         [orig] of the last token matched before it; [macro], the column of
         the latest macro name met), then the first partner of token k that
         keeps it optimal. The tokens of [orig] skipped right before a
         partner, when they start with a word, are a macro's use, and the
         token matched there begins its expansion. A token k with no partner
         is inside the latest expansion. *)
      let rec walk last macro i j =
        let gap j' = if last + 1 < j' && word b.(last + 1) then Some (snd b.(last + 1) + 1) else None in
        if i >= na || j >= nb then macro
        else if i = k then
          let rec find j' =
            if j' >= nb || lcs.(k).(j') <> lcs.(k).(j) then macro
            else if fst a.(k) = fst b.(j') && lcs.(k).(j') = lcs.(k + 1).(j' + 1) + 1 then
              Some (match gap j' with Some c -> c | None -> snd b.(j') + 1)
            else find (j' + 1)
          in
          find j
        else if fst a.(i) = fst b.(j) && lcs.(i).(j) = lcs.(i + 1).(j + 1) + 1 then
          walk j (match gap j with Some c -> Some c | None -> macro) (i + 1) (j + 1)
        else if lcs.(i + 1).(j) >= lcs.(i).(j + 1) then walk last macro (i + 1) j
        else walk last macro i (j + 1)
      in
      match walk (-1) None 0 0 with Some c -> c | None -> col

(* ---- input positions ---- *)

type pos = { line : int; column : int }

(* The position in the input file [input] of the Frama-C position [p], or
   None when it is not in that file. *)
let input_pos input p =
  if Filepos.is_empty p || Filepos.input_line p <= 0 then None
  else if Filepath.equal (Filepos.input_path p) input then
    Some { line = Filepos.input_line p; column = Filepos.input_column p }
  else if Filepos.is_preprocessed p && Filepath.equal (Filepos.path p) input then
    let line = Filepos.line p in
    let column =
      match
        ( line_text (Filepath.to_string (Filepos.input_path p)) (Filepos.input_line p),
          line_text (Filepath.to_string input) line )
      with
      | Some pp, Some orig -> align ~pp ~orig (Filepos.input_column p)
      | _ -> Filepos.input_column p
    in
    Some { line; column }
  else None

(* ---- the untyped AST: extents of statements and full expressions ---- *)

type extent = {
  path : Filepath.t;  (* the file lexed *)
  start : int;  (* offsets in it, [start, stop) *)
  stop : int;
  first : Filepos.t;  (* the first character *)
}

type cabs_stmt = {
  ext : extent;
  cond : extent option;  (* the controlling expression of a selection or iteration *)
  cid : int;  (* a number of its own *)
}

let extent_of ((a, b) : Cabs.cabsloc) =
  if Filepos.is_empty a || Filepos.input_offset a < 0 then None
  else
    Some
      { path = Filepos.input_path a; start = Filepos.input_offset a;
        stop = max (Filepos.input_offset b) (Filepos.input_offset a + 1); first = a }

let expr_extent (e : Cabs.expression) =
  match e.expr_node with Cabs.NOTHING -> None | _ -> extent_of e.expr_loc

type index = {
  stmts : cabs_stmt list;  (* statements, wrappers (blocks, labels) left out *)
  exprs : extent list;  (* full expressions *)
  funcs : (extent * string) list;  (* function definitions, with their names *)
}

let empty_index = { stmts = []; exprs = []; funcs = [] }

(* The statements and full expressions of every function the untyped AST of
   the current project defines; empty when it has none. *)
let cabs_index () =
  let stmts = ref [] and exprs = ref [] and funcs = ref [] and n = ref 0 in
  let add_expr e = Option.iter (fun x -> exprs := x :: !exprs) (expr_extent e) in
  let add ?cond loc =
    match extent_of loc with
    | Some ext ->
        incr n;
        stmts := { ext; cond = Stdlib.Option.bind cond expr_extent; cid = !n } :: !stmts
    | None -> ()
  in
  let rec init_exprs = function
    | Cabs.SINGLE_INIT e -> add_expr e
    | Cabs.COMPOUND_INIT l -> List.iter (fun (_, i) -> init_exprs i) l
    | Cabs.NO_INIT -> ()
  in
  let rec def = function
    | Cabs.FUNDEF (_, (_, (name, _, _, _)), b, (a, _), (_, z)) ->
        (match extent_of (a, z) with Some e -> funcs := (e, name) :: !funcs | None -> ());
        List.iter stmt b.Cabs.bstmts
    | Cabs.DECDEF (_, (_, names), loc) ->
        add loc;
        List.iter (fun (_, i) -> init_exprs i) names
    | Cabs.LINKAGE (_, _, l) -> List.iter def l
    | _ -> ()
  and stmt (s : Cabs.statement) =
    let open Cabs in
    match s.stmt_node with
    | NOP _ | CODE_ANNOT _ | CODE_SPEC _ -> ()
    | COMPUTATION (e, loc) -> add loc; add_expr e
    | BLOCK (b, _, _) -> List.iter stmt b.bstmts
    | IF (e, a, b, loc) -> add ~cond:e loc; add_expr e; stmt a; stmt b
    | WHILE (_, e, a, loc) -> add ~cond:e loc; add_expr e; stmt a
    | DOWHILE (_, e, a, loc) -> add ~cond:e loc; add_expr e; stmt a
    | FOR (_, fc, e2, e3, a, loc) ->
        add ~cond:e2 loc;
        (match fc with FC_EXP e -> add_expr e | FC_DECL d -> def d);
        add_expr e2; add_expr e3; stmt a
    | RETURN (e, loc) -> add loc; add_expr e
    | SWITCH (e, a, loc) -> add loc; add_expr e; stmt a
    | CASE (_, a, _) | CASERANGE (_, _, a, _) | DEFAULT (a, _) | LABEL (_, a, _) -> stmt a
    | BREAK loc | CONTINUE loc | GOTO (_, loc) -> add loc
    | COMPGOTO (e, loc) -> add loc; add_expr e
    | DEFINITION d -> def d
    | ASM (_, _, _, loc) -> add loc
    | THROW (e, loc) -> add loc; Option.iter add_expr e
    | TRY_CATCH (a, l, loc) -> add loc; stmt a; List.iter (fun (_, b) -> stmt b) l
  in
  match Ast.UntypedFiles.get () with
  | files ->
      List.iter (fun (_, defs) -> List.iter (fun (_, d) -> def d) defs) files;
      { stmts = !stmts; exprs = !exprs; funcs = !funcs }
  | exception (Ast.NoUntypedAst | Ast.Bad_Initialization _) -> empty_index

let holds (e : extent) path off = Filepath.equal e.path path && e.start <= off && off < e.stop

(* The innermost of [cands] holding the start of the location [p]: the
   latest start, then the shortest. *)
let innermost ext_of cands (p : Filepos.t) =
  let path = Filepos.input_path p and off = Filepos.input_offset p in
  List.fold_left
    (fun best c ->
      let e = ext_of c in
      if not (holds e path off) then best
      else
        match best with
        | Some b ->
            let eb = ext_of b in
            if e.start > eb.start || (e.start = eb.start && e.stop < eb.stop) then Some c else best
        | None -> Some c)
    None cands

(* [innermost ext_of cands], computed once for many locations: the
   candidates of each file sorted by their start, so that a query looks only
   at the candidates that start at or before the location and could still
   hold it (it stops at the first candidate below which every extent ends
   before the location, or that starts before the best one found).  The
   answer is [innermost]'s, ties on start and end going to the earlier
   candidate in [cands], as there.  [innermost] scans every candidate for
   each location, which is quadratic in the size of a function: the
   generated tasks whose functions hold thousands of statements spent most
   of their transformation time there. *)
let innermost_finder ext_of cands =
  let by_path = Hashtbl.create 4 in
  List.iteri
    (fun i c ->
      let e = ext_of c in
      let k = Filepath.to_string e.path in
      Hashtbl.replace by_path k ((i, c, e) :: Option.value ~default:[] (Hashtbl.find_opt by_path k)))
    cands;
  let tables = Hashtbl.create 4 in
  Hashtbl.iter
    (fun k l ->
      let a = Array.of_list l in
      Array.stable_sort
        (fun (i, _, (e : extent)) (j, _, (f : extent)) ->
          if e.start <> f.start then compare e.start f.start else compare i j)
        a;
      let maxstop = Array.make (Array.length a) 0 in
      Array.iteri
        (fun k (_, _, (e : extent)) ->
          maxstop.(k) <- (if k = 0 then e.stop else max maxstop.(k - 1) e.stop))
        a;
      Hashtbl.replace tables k (a, maxstop))
    by_path;
  fun (p : Filepos.t) ->
    match Hashtbl.find_opt tables (Filepath.to_string (Filepos.input_path p)) with
    | None -> None
    | Some (a, maxstop) ->
        let off = Filepos.input_offset p in
        (* the last candidate starting at or before [off] *)
        let lo = ref 0 and hi = ref (Array.length a - 1) and last = ref (-1) in
        while !lo <= !hi do
          let mid = (!lo + !hi) / 2 in
          let _, _, e = a.(mid) in
          if e.start <= off then (last := mid; lo := mid + 1) else hi := mid - 1
        done;
        let best = ref None in
        let k = ref !last in
        let continue = ref true in
        while !continue && !k >= 0 do
          let i, c, e = a.(!k) in
          if maxstop.(!k) <= off then continue := false
          else begin
            (match !best with
             | Some (_, _, (b : extent)) when e.start < b.start -> continue := false
             | _ -> ());
            if !continue && off < e.stop then
              match !best with
              | None -> best := Some (i, c, e)
              | Some (bi, _, b) ->
                  if e.start > b.start
                     || (e.start = b.start && (e.stop < b.stop || (e.stop = b.stop && i < bi)))
                  then best := Some (i, c, e)
          end;
          decr k
        done;
        Option.map (fun (_, c, _) -> c) !best

(* ---- the analysis ---- *)

(* Tables keyed by an output statement itself: the statements the
   transformation makes do not all have a number of their own (several have
   -1), so a statement's sid does not identify it. *)
module Phys = Hashtbl.Make (struct
  type t = stmt

  let equal = ( == )
  let hash (s : stmt) = Hashtbl.hash (s.sid, Fileloc.line (Cil_datatype.Stmt.loc s), Hashtbl.hash s.skind)
end)

type role = Loop_head | Branch | Call_site | Target of string list | Other

type entry = {
  out_stmt : stmt;
  func : string;
  role : role;
  input : (pos * string) option;  (* position and input function *)
}

(* What the analysis needs to know about the transformation. *)
type facts = {
  roles : (int, string) Hashtbl.t;  (* variable id -> role; absent: program *)
  violation_calls : (instr * string) list;  (* a marker's call, its property *)
  overflow_marker : varinfo option;
  unreach_call : bool;  (* the input's reach_error calls are targets *)
  main_return : int list;  (* the output statements of the end check after main *)
}

let no_facts ~unreach_call =
  { roles = Hashtbl.create 1; violation_calls = []; overflow_marker = None; unreach_call;
    main_return = [] }

let role_of facts vi = Option.value ~default:"program" (Hashtbl.find_opt facts.roles vi.vid)

let first_stmt_pos s = fst (Cil_datatype.Stmt.loc s)

(* [f] on every statement of [fd]'s body. *)
let body_stmts fd f =
  let rec walk s =
    f s;
    let sub b = List.iter walk b.bstmts in
    match s.skind with
    | Block b | Loop (_, b, _, _, _) | Switch (_, b, _, _) -> sub b
    | If (_, b1, b2, _) -> sub b1; sub b2
    | UnspecifiedSequence l -> List.iter (fun (s', _, _, _, _) -> walk s') l
    | TryFinally (b1, b2, _) -> sub b1; sub b2
    | TryExcept (b1, _, b2, _) -> sub b1; sub b2
    | TryCatch (b, l, _) -> sub b; List.iter (fun (_, b') -> sub b') l
    | Instr _ | Return _ | Goto _ | Break _ | Continue _ | Throw _ -> ()
  in
  List.iter walk fd.sbody.bstmts

(* The function an instruction calls directly, if any. *)
let callee = function
  | Call (_, Var f, _, _) | Local_init (_, ConsInit (f, _, _), _) -> Some f
  | _ -> None

(* The analysis of the input and the output: one entry per output statement
   that is not a block, in no particular order. [input] is the input file as
   Frama-C names it, [pairs] the (input sid, output sid) pairs of the copy.

   An output statement's input position is read from its own location when
   that is in the input file: the transformation gives the instructions it
   adds the location of the instruction or expression they serve, and the
   front end splices a translated instruction's statements into the
   enclosing block, where they are no longer inside the statement they were
   copied from. A statement with no such location (one the transformation
   made from nothing in particular) takes the position of the innermost
   copied statement around it, if any. *)
let analyse ~input ~prj ~pairs facts =
  let idx = cabs_index () in
  let in_cond_stmt = innermost_finder (fun c -> c.ext) (List.filter (fun c -> c.cond <> None) idx.stmts) in
  let in_func = innermost_finder fst idx.funcs in
  let in_stmt_ext = innermost_finder (fun c -> c.ext) idx.stmts in
  let in_expr = innermost_finder Fun.id idx.exprs in
  let by_cid = Hashtbl.create 256 in
  List.iter (fun c -> Hashtbl.replace by_cid c.cid c) idx.stmts;
  (* the input's statements by sid, and the return of its main *)
  let in_stmt = Hashtbl.create 256 in
  let in_return = ref None in
  List.iter
    (function
      | GFun (fd, _) ->
          body_stmts fd (fun s ->
              Hashtbl.replace in_stmt s.sid s;
              match s.skind with
              | Return _ when fd.svar.vname = "main" -> in_return := Some s
              | _ -> ())
      | _ -> ())
    (Ast.get ()).globals;
  (* the [if]s that evaluate a whole controlling expression: by the
     untyped statement whose condition holds their location, those of the
     statements that have exactly one *)
  let conds = Hashtbl.create 32 in
  Hashtbl.iter
    (fun _ s ->
      match s.skind with
      | If _ -> (
          let p = first_stmt_pos s in
          let in_cond c =
            match c.cond with
            | Some e -> holds e (Filepos.input_path p) (Filepos.input_offset p)
            | None -> false
          in
          match in_cond_stmt p with
          | Some c when in_cond c ->
              Hashtbl.replace conds c.cid
                (s.sid :: Option.value ~default:[] (Hashtbl.find_opt conds c.cid))
          | _ -> ())
      | _ -> ())
    in_stmt;
  let whole_cond = Hashtbl.create 32 in
  Hashtbl.iter
    (fun cid sids ->
      match sids with
      | [ sid ] -> Hashtbl.replace whole_cond sid (Hashtbl.find by_cid cid)
      | _ -> ())
    conds;
  (* the position in the input of a Frama-C position, with the input
     function whose definition holds it *)
  let with_func (p : Filepos.t) =
    Option.map
      (fun q ->
        let f = in_func p in
        (q, match f with Some (_, name) -> name | None -> ""))
      (input_pos input p)
  in
  (* the first character of the innermost untyped statement holding [p]
     (with [full], statement or full expression) *)
  let first_of ?(full = false) p =
    let st = Option.map (fun c -> c.ext) (in_stmt_ext p) in
    let ex = if full then in_expr p else None in
    let best =
      match (st, ex) with
      | Some a, Some b ->
          if b.start > a.start || (b.start = a.start && b.stop < a.stop) then Some b else Some a
      | (Some _ as a), None -> a
      | None, b -> b
    in
    match best with Some e -> e.first | None -> p
  in
  let loop_kind s =
    List.find_map
      (fun (n, _) -> match n with "while" | "for" | "dowhile" -> Some n | _ -> None)
      s.sattr
  in
  let out2in = Hashtbl.create 256 in
  List.iter (fun (i, o) -> Hashtbl.replace out2in o i) pairs;
  Project.on prj
    (fun () ->
      let fundecs =
        List.filter_map (function GFun (fd, _) -> Some fd | _ -> None) (Ast.get ()).globals
      in
      let props_of_instr i =
        List.filter_map (fun (j, p) -> if j == i then Some p else None) facts.violation_calls
        @
        match (i, facts.overflow_marker) with
        | Call (_, Var f, _, _), Some m when f.vid = m.vid -> [ "no-overflow" ]
        | _ -> []
      in
      let has_main_return fd =
        let r = ref false in
        body_stmts fd (fun s -> if List.mem s.sid facts.main_return then r := true);
        !r
      in
      (* the functions of the program (and the new main): the others are
         generated, and a call of one is a target when its body reaches a
         violation, directly or through the generated functions it calls *)
      let program fd = role_of facts fd.svar = "program" || has_main_return fd in
      let props = Hashtbl.create 16 and calls = Hashtbl.create 16 in
      List.iter
        (fun fd ->
          if not (program fd) then begin
            let d = ref [] and c = ref [] in
            body_stmts fd (fun s ->
                match s.skind with
                | Instr i ->
                    d := props_of_instr i @ !d;
                    Option.iter (fun g -> c := g.vid :: !c) (callee i)
                | _ -> ());
            Hashtbl.replace props fd.svar.vid (List.sort_uniq compare !d);
            Hashtbl.replace calls fd.svar.vid !c
          end)
        fundecs;
      let changed = ref true in
      while !changed do
        changed := false;
        List.iter
          (fun (f, ps) ->
            let more =
              List.concat_map
                (fun g -> Option.value ~default:[] (Hashtbl.find_opt props g))
                (Option.value ~default:[] (Hashtbl.find_opt calls f))
            in
            let ps' = List.sort_uniq compare (ps @ more) in
            if ps' <> ps then begin
              Hashtbl.replace props f ps';
              changed := true
            end)
          (Hashtbl.fold (fun f ps acc -> (f, ps) :: acc) props [])
      done;
      let entries = ref [] in
      List.iter
        (fun fd ->
          let in_program = program fd in
          let rec go anc s =
            let anc =
              match Hashtbl.find_opt out2in s.sid with
              | Some i -> Option.fold ~none:anc ~some:Option.some (Hashtbl.find_opt in_stmt i)
              | None -> anc
            in
            let own = first_stmt_pos s in
            (* the Frama-C position the statement comes from *)
            let src =
              if input_pos input own <> None then Some own
              else Option.map first_stmt_pos anc
            in
            let at ?full () = Stdlib.Option.bind src (fun p -> with_func (first_of ?full p)) in
            let role, inp =
              if not in_program then (Other, None)
              else
                let target_props =
                  match s.skind with
                  | Instr i ->
                      let via =
                        match callee i with
                        | Some g when role_of facts g <> "program" ->
                            Option.value ~default:[] (Hashtbl.find_opt props g.vid)
                        | Some g when facts.unreach_call && g.vname = "reach_error" ->
                            [ "unreach-call" ]
                        | _ -> []
                      in
                      List.sort_uniq compare (props_of_instr i @ via)
                  | _ -> []
                in
                if target_props <> [] then
                  ( Target target_props,
                    if List.mem s.sid facts.main_return then
                      Stdlib.Option.bind !in_return (fun r -> with_func (first_of (first_stmt_pos r)))
                    else at ~full:true () )
                else
                  match (s.skind, anc) with
                  | Loop _, Some o when Hashtbl.mem out2in s.sid ->
                      ((match loop_kind o with Some ("while" | "for") -> Loop_head | _ -> Other), at ())
                  | If _, Some o
                    when Hashtbl.mem whole_cond o.sid
                         && Fileloc.equal (Cil_datatype.Stmt.loc s) (Cil_datatype.Stmt.loc o) ->
                      (Branch, with_func (Hashtbl.find whole_cond o.sid).ext.first)
                  | Instr i, _
                    when (match callee i with Some g -> role_of facts g = "program" | None -> false)
                         && input_pos input own <> None ->
                      (Call_site, at ())
                  | _ -> (Other, at ())
            in
            (match s.skind with
             | Block _ | UnspecifiedSequence _ -> ()
             | _ ->
                 let roles =
                   match role with Target ps -> List.map (fun p -> Target [ p ]) ps | r -> [ r ]
                 in
                 List.iter
                   (fun role ->
                     entries := { out_stmt = s; func = fd.svar.vname; role; input = inp } :: !entries)
                   roles);
            let sub b = List.iter (go anc) b.bstmts in
            match s.skind with
            | Block b | Loop (_, b, _, _, _) | Switch (_, b, _, _) -> sub b
            | If (_, b1, b2, _) -> sub b1; sub b2
            | UnspecifiedSequence l -> List.iter (fun (s', _, _, _, _) -> go anc s') l
            | TryFinally (b1, b2, _) -> sub b1; sub b2
            | TryExcept (b1, _, b2, _) -> sub b1; sub b2
            | TryCatch (b, l, _) -> sub b; List.iter (fun (_, b') -> sub b') l
            | Instr _ | Return _ | Goto _ | Break _ | Continue _ | Throw _ -> ()
          in
          List.iter (go None) fd.sbody.bstmts)
        fundecs;
      List.rev !entries)
    ()

(* ---- printing ---- *)

(* The start of a statement, of the [if] a [while] head is printed from
   (which shares the [while]'s line and gets no #line of its own), and of a
   function definition. *)
type Format.stag += Stmt_start of stmt | Head_if of stmt | Global_start

type printed = {
  positions : pos Phys.t;  (* output statement -> its first character *)
  negated : bool Phys.t;  (* output [if] -> condition printed negated *)
}

(* Set for the duration of one [print]. *)
let negated_tbl : bool Phys.t ref = ref (Phys.create 1)

module Ext (X : Printer.PrinterClass) = struct
  class printer () =
    object (self)
      inherit X.printer () as super

      method! stmtkind sattr next fmt sk =
        (match self#current_stmt with
         | Some s -> (
             (match sk with
              | Block _ | UnspecifiedSequence _ -> ()
              | _ ->
                  Format.pp_open_stag fmt (Stmt_start s);
                  Format.pp_close_stag fmt ());
             (* how Frama-C's printer writes an [if]: with an empty
                then-branch (or one that jumps to the next statement) and a
                non-empty else-branch, as the negated condition and the else
                branch; otherwise as it is *)
             match sk with
             | If (_, t, e, _) ->
                 let empty b = b.bstmts = [] && b.battrs = [] in
                 let goto_next b =
                   match b.bstmts with
                   | [ { skind = Goto (g, _); labels = []; _ } ] -> !g == next
                   | _ -> false
                 in
                 let neg =
                   (not (empty e || goto_next e))
                   && (empty t || goto_next t)
                   && not (Cil.is_ghost_else e)
                 in
                 Phys.replace !negated_tbl s neg
             | _ -> ())
         | None -> ());
        super#stmtkind sattr next fmt sk

      (* the [if (! c) break;] a [while] head is printed from *)
      method! pp_while_head fmt cond =
        (match self#current_stmt with
         | Some ({ skind = If (c, _, _, _); _ } as s) ->
             Format.pp_open_stag fmt (Head_if s);
             Format.pp_close_stag fmt ();
             Phys.replace !negated_tbl s (not (cond == c))
         | _ -> ());
        super#pp_while_head fmt cond

      method! global fmt g =
        (match g with
         | GFun _ ->
             Format.pp_open_stag fmt Global_start;
             Format.pp_close_stag fmt ()
         | _ -> ());
        super#global fmt g
    end
end

let c_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (fun c ->
      match c with
      | '"' | '\\' -> Buffer.add_char b '\\'; Buffer.add_char b c
      | '\n' -> Buffer.add_string b "\\n"
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

(* Writes [prj] to [path], as File.pretty_ast does, and returns where each
   statement was printed. With [directives = Some (input, entries)], each
   statement listed in [entries] is preceded by a [#line] line naming its
   input position in the file [input] (the name as given), or, without one,
   the next line of [path] itself; so is each function definition, so that
   a declaration does not keep the line of the statement before it. *)
let print ?directives prj path =
  let positions = Phys.create 256 in
  negated_tbl := Phys.create 64;
  let target = Phys.create 256 in
  Option.iter
    (fun (_, entries) ->
      List.iter
        (fun e -> Phys.replace target e.out_stmt (Option.map (fun (p, _) -> p.line) e.input))
        entries)
    directives;
  let oc = open_out_bin path in
  let line = ref 1 and col = ref 0 in
  let count s pos len =
    for k = pos to pos + len - 1 do
      if s.[k] = '\n' then (incr line; col := 0) else incr col
    done
  in
  (* the channel's own formatter, its output counted: newlines, spaces and
     indentation are written through the formatter's string output too *)
  let fmt = Format.formatter_of_out_channel oc in
  let f = Format.pp_get_formatter_out_functions fmt () in
  Format.pp_set_formatter_out_functions fmt
    { f with Format.out_string = (fun s pos len -> f.out_string s pos len; count s pos len) };
  let directive l file =
    (* on a line of its own, the rest of the line indented as before *)
    let s = Printf.sprintf "\n#line %d %s\n%s" l (c_string file) (String.make !col ' ') in
    s
  in
  let mark = function
    | Stmt_start st ->
        let s =
          match (directives, Phys.find_opt target st) with
          | Some (input, _), Some (Some l) -> directive l input
          | Some _, Some None -> directive (!line + 2) path
          | _ -> ""
        in
        let nl = if s = "" then 0 else 2 in
        if not (Phys.mem positions st) then
          Phys.replace positions st { line = !line + nl; column = !col + 1 };
        s
    | Head_if st ->
        if not (Phys.mem positions st) then
          Phys.replace positions st { line = !line; column = !col + 1 };
        ""
    | Global_start -> (
        match directives with Some _ -> directive (!line + 2) path | None -> "")
    | _ -> ""
  in
  Format.pp_set_mark_tags fmt true;
  Format.pp_set_formatter_stag_functions fmt
    { Format.mark_open_stag = mark; mark_close_stag = (fun _ -> "");
      print_open_stag = ignore; print_close_stag = ignore };
  let old = Printer.current_printer () in
  Printer.update_printer (module Ext : Printer.PrinterExtension);
  Fun.protect
    ~finally:(fun () ->
      Printer.set_printer old;
      close_out oc)
    (fun () ->
      File.pretty_ast ~prj ~fmt ();
      Format.pp_print_flush fmt ());
  { positions; negated = !negated_tbl }

(* ---- the field ---- *)

let role_name = function
  | Loop_head -> "loop-head"
  | Branch -> "branch"
  | Call_site -> "call"
  | Target _ -> "target"
  | Other -> "other"

(* The record's source_map: [input_file] the input's name as the record
   gives it; the entries printed, in the order of their output positions. *)
let to_json ~input_file entries printed =
  let rows =
    List.filter_map
      (fun e ->
        Option.map (fun p -> (p, e)) (Phys.find_opt printed.positions e.out_stmt))
      entries
    |> List.stable_sort (fun ((a : pos), _) ((b : pos), _) -> compare (a.line, a.column) (b.line, b.column))
  in
  `Assoc
    [ ("input_file", `String input_file);
      ( "statements",
        `List
          (List.map
             (fun ((p : pos), e) ->
               `Assoc
                 [ ("output_line", `Int p.line);
                   ("output_column", `Int p.column);
                   ("function", `String e.func);
                   ("role", `String (role_name e.role));
                   ( "input",
                     match e.input with
                     | Some (q, f) ->
                         `Assoc [ ("line", `Int q.line); ("column", `Int q.column); ("function", `String f) ]
                     | None -> `Null );
                   ("property", match e.role with Target [ p ] -> `String p | _ -> `Null);
                   ( "cond_negated",
                     match e.role with
                     | Branch -> (
                         match Phys.find_opt printed.negated e.out_stmt with
                         | Some b -> `Bool b
                         | None -> `Null)
                     | _ -> `Null ) ])
             rows) ) ]
