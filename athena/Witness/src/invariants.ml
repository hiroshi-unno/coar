(* The loop invariants, loop transition invariants and path states of a
   result, from the lines CoAR prints after its verdict on the direct LLVM
   route (the LLVM frontend's [witness] setting), turned into entries of a
   witness of the input file.

   A line is about one loop head of the program CoAR read (Ptr2ArrFC's
   output):

     (invariant (loc LINE COLUMN) (function "F") (vars (X signed|unsigned WIDTH [global]) ...) EXPR)
     (transition (loc LINE COLUMN) (function "F") (vars ...) EXPR)
     (state (loc LINE COLUMN) (function "F") (vars ...) EXPR)
     (skipped [(loc LINE COLUMN)] (function "F") "REASON")

   LINE and COLUMN are the first character of the loop statement in the
   output file; EXPR is an S-expression over the output's variables X, in
   linear integer arithmetic (numerals, + - *, = distinct <= < >= >, and or
   not, true false).  An invariant is true of every state reachable there.
   A transition (termination, TRUE) is over X and (prev X), X's value at an
   earlier visit, and is a transitive, well-founded relation containing every
   pair of visits; it becomes a loop transition invariant, (prev X) becoming
   \at(X, AnyPrev).  The state lines (FALSE) are the visits of loop heads
   along one violating execution, in its order, each the values of some
   variables there; the first visit of each loop becomes an assumption
   waypoint before the target.

   Each top-level conjunct of EXPR is written as C or dropped; dropping one
   only weakens the invariant.  A conjunct is dropped when one of its
   variables is not a name of the input (by the record's names: role
   program, and the original name), and when one of its subterms may not fit
   a [long long]: every variable is converted to [long long] and every
   numeral written as one, and the range of each subterm is computed from the
   variables' types, so the C expression has no overflow and means what EXPR
   means over the integers.

   The output's loop heads are mapped to the input with the source map's
   loop-head statements.  Several output loops can come from one input loop;
   the input loop then gets the disjunction of their invariants, and none at
   all unless every one of them has an invariant line, since a loop the
   result says nothing about may reach any state there. *)

type sexp = Atom of string | Quoted of string | List of sexp list

exception Parse of string

let parse s =
  let n = String.length s in
  let rec skip_ws i = if i < n && (s.[i] = ' ' || s.[i] = '\t' || s.[i] = '\r') then skip_ws (i + 1) else i in
  let rec item i =
    let i = skip_ws i in
    if i >= n then raise (Parse "unexpected end")
    else
      match s.[i] with
      | '(' ->
          let rec items i acc =
            let i = skip_ws i in
            if i < n && s.[i] = ')' then (List (List.rev acc), i + 1)
            else
              let x, i = item i in
              items i (x :: acc)
          in
          items (i + 1) []
      | ')' -> raise (Parse "unexpected )")
      | '"' ->
          let b = Buffer.create 16 in
          let rec str i =
            if i >= n then raise (Parse "unterminated string")
            else if s.[i] = '\\' && i + 1 < n then (
              Buffer.add_char b s.[i + 1];
              str (i + 2))
            else if s.[i] = '"' then (Quoted (Buffer.contents b), i + 1)
            else (
              Buffer.add_char b s.[i];
              str (i + 1))
          in
          str (i + 1)
      | _ ->
          let rec atom j = if j < n && not (List.mem s.[j] [ ' '; '\t'; '\r'; '('; ')'; '"' ]) then atom (j + 1) else j in
          let j = atom i in
          (Atom (String.sub s i (j - i)), j)
  in
  let x, i = item 0 in
  if skip_ws i <> n then raise (Parse "trailing text");
  x

type cvar = { cname : string; signed : bool; width : int; global : bool }

type kind = Invariant | Transition | State

type line =
  | Line of { kind : kind; loc : int * int; func : string; vars : cvar list; expr : sexp }
  | Skipped of { loc : (int * int) option; func : string; reason : string }

let int_of a = match int_of_string_opt a with Some n -> n | None -> raise (Parse ("not a number: " ^ a))

let loc_of = function
  | List [ Atom "loc"; Atom l; Atom c ] -> (int_of l, int_of c)
  | _ -> raise (Parse "expected (loc LINE COLUMN)")

let func_of = function List [ Atom "function"; Quoted f ] -> f | _ -> raise (Parse "expected (function \"F\")")

let var_of = function
  | List (Atom cname :: Atom sign :: Atom width :: rest) ->
      let signed =
        match sign with "signed" -> true | "unsigned" -> false | _ -> raise (Parse ("not a signedness: " ^ sign))
      in
      let global = match rest with [] -> false | [ Atom "global" ] -> true | _ -> raise (Parse "bad variable") in
      { cname; signed; width = int_of width; global }
  | _ -> raise (Parse "expected (NAME signed|unsigned WIDTH [global])")

let kind_of = function
  | "invariant" -> Some Invariant
  | "transition" -> Some Transition
  | "state" -> Some State
  | _ -> None

let line_of_sexp = function
  | List [ Atom k; loc; func; List (Atom "vars" :: vars); expr ] when kind_of k <> None ->
      Line { kind = Option.get (kind_of k); loc = loc_of loc; func = func_of func; vars = List.map var_of vars; expr }
  | List [ Atom "skipped"; loc; func; Quoted reason ] -> Skipped { loc = Some (loc_of loc); func = func_of func; reason }
  | List [ Atom "skipped"; func; Quoted reason ] -> Skipped { loc = None; func = func_of func; reason }
  | _ -> raise (Parse "none of (invariant ...), (transition ...), (state ...), (skipped ...)")

(* The lines of [path], skipping blank ones; an error names the first line
   that is not one of the forms. *)
let read path =
  match In_channel.with_open_text path In_channel.input_all with
  | exception Sys_error e -> Error e
  | text -> (
      let lines = String.split_on_char '\n' text |> List.filter (fun l -> String.trim l <> "") in
      try Ok (List.mapi (fun i l -> try line_of_sexp (parse l) with Parse m -> raise (Parse (Printf.sprintf "line %d: %s" (i + 1) m))) lines)
      with Parse m -> Error (path ^ ": " ^ m))

(* -- To C ------------------------------------------------------------------ *)

exception Drop of string

let drop fmt = Printf.ksprintf (fun s -> raise (Drop s)) fmt
let ll_min = Z.neg (Z.shift_left Z.one 63)
let ll_max = Z.pred (Z.shift_left Z.one 63)

let fits (lo, hi) = Z.geq lo ll_min && Z.leq hi ll_max

let int_range width signed =
  if signed then (Z.neg (Z.shift_left Z.one (width - 1)), Z.pred (Z.shift_left Z.one (width - 1)))
  else (Z.zero, Z.pred (Z.shift_left Z.one width))

(* A variable of the output as the input names it, with the range of its
   values: the record's type for that name, else the line's. *)
let resolve (record : Record.t) func (v : cvar) =
  let candidates =
    List.filter
      (fun (n : Record.name) ->
        n.name = v.cname
        && if v.global then n.kind = "global" else (n.kind = "formal" || n.kind = "local") && n.name_func = Some func)
      record.names
  in
  match candidates with
  | [ { name_role = "program"; original = Some original; int_type; _ } ] ->
      let range =
        match int_type with
        | Some Bool_type -> (Z.zero, Z.one)
        | Some (Int_type { width; signed }) -> int_range width signed
        | None -> int_range v.width v.signed
      in
      (original, range)
  | [ n ] -> drop "%s is not a variable of the input (role %s)" v.cname n.name_role
  | [] -> drop "%s is not in the record's names" v.cname
  | _ -> drop "%s names several variables in %s" v.cname func

(* The variables a line's expression may name, each with its C name and
   range, and whether it may name their earlier values (a transition). *)
type env = { vars : (string * (string * (Z.t * Z.t))) list; prev : bool }

let rec term env = function
  | Atom a when String.length a > 0 && a.[0] >= '0' && a.[0] <= '9' ->
      let z = Z.of_string a in
      if not (fits (z, z)) then drop "the constant %s does not fit a long long" a;
      (Z.to_string z ^ "LL", (z, z))
  | Atom a -> (
      match List.assoc_opt a env.vars with
      | Some (c, range) -> ("(long long)" ^ c, range)
      | None -> drop "%s is not among the line's variables" a)
  | List [ Atom "prev"; Atom a ] -> (
      match (env.prev, List.assoc_opt a env.vars) with
      | false, _ -> drop "an earlier value outside a transition"
      | true, Some (c, range) -> ("(long long)\\at(" ^ c ^ ", AnyPrev)", range)
      | true, None -> drop "%s is not among the line's variables" a)
  | List [ Atom "-"; a ] ->
      let c, (lo, hi) = term env a in
      ("(-" ^ c ^ ")", (Z.neg hi, Z.neg lo))
  | List [ Atom (("+" | "-" | "*") as op); a; b ] ->
      let ca, (alo, ahi) = term env a in
      let cb, (blo, bhi) = term env b in
      let range =
        match op with
        | "+" -> (Z.add alo blo, Z.add ahi bhi)
        | "-" -> (Z.sub alo bhi, Z.sub ahi blo)
        | _ ->
            let ps = [ Z.mul alo blo; Z.mul alo bhi; Z.mul ahi blo; Z.mul ahi bhi ] in
            (List.fold_left Z.min (List.hd ps) ps, List.fold_left Z.max (List.hd ps) ps)
      in
      if not (fits range) then drop "a subterm may not fit a long long";
      ("(" ^ ca ^ " " ^ op ^ " " ^ cb ^ ")", range)
  | _ -> drop "a term outside linear integer arithmetic"

let rec formula env = function
  | Atom "true" -> "1"
  | Atom "false" -> "0"
  | List (Atom (("and" | "or") as op) :: (_ :: _ as es)) ->
      "(" ^ String.concat (if op = "and" then " && " else " || ") (List.map (formula env) es) ^ ")"
  | List [ Atom "not"; e ] -> "!" ^ formula env e
  | List [ Atom op; a; b ] ->
      let cop =
        match op with
        | "=" -> "=="
        | "distinct" -> "!="
        | "<=" | "<" | ">=" | ">" -> op
        | _ -> drop "an operator %s" op
      in
      "(" ^ fst (term env a) ^ " " ^ cop ^ " " ^ fst (term env b) ^ ")"
  | _ -> drop "a formula outside the connectives and comparisons"

let conjuncts = function List (Atom "and" :: es) -> es | e -> [ e ]

(* The C expression of one line, or [None] when every conjunct is dropped;
   the reasons conjuncts were dropped go to [note]. *)
let c_of_line record note = function
  | Skipped _ -> None
  | Line { kind; func; vars; expr; _ } ->
      let vars =
        List.filter_map
          (fun v ->
            match resolve record func v with
            | r -> Some (v.cname, r)
            | exception Drop why ->
                note why;
                None)
          vars
      in
      let env = { vars; prev = kind = Transition } in
      let kept =
        List.filter_map
          (fun c ->
            match formula env c with
            | s -> Some s
            | exception Drop why ->
                note why;
                None)
          (conjuncts expr)
      in
      if kept = [] then None else Some (String.concat " && " kept)

let loop_heads (record : Record.t) =
  List.filter_map
    (fun (s : Record.statement) ->
      match (s.role, s.input) with
      | Record.Loop_head, Some pos -> Some ((s.output_line, s.output_column), pos)
      | _ -> None)
    record.source_map

(* The invariants of [kind] of the input, from [lines]: one per input loop
   every output copy of which has a line of that kind.  Several copies'
   invariants are joined by disjunction, a sound invariant of the input loop;
   transitions only when there is one copy, since a disjunction of transitive
   relations need not be transitive. *)
let to_witness ?(kind = Invariant) (record : Record.t) ~input_file note lines =
  let loop_heads = loop_heads record in
  let lines = List.filter (function Line l -> l.kind = kind | Skipped _ -> true) lines in
  let at loc = List.filter (function Line l -> l.loc = loc | Skipped { loc = Some l; _ } -> l = loc | _ -> false) lines in
  let inputs = List.sort_uniq compare (List.map snd loop_heads) in
  List.filter_map
    (fun (pos : Record.input_position) ->
      let outputs = List.filter_map (fun (out, p) -> if p = pos then Some out else None) loop_heads in
      let parts =
        List.map
          (fun out ->
            match at out with
            | [ l ] -> c_of_line record note l
            | [] -> None
            | _ :: _ :: _ ->
                note (Printf.sprintf "several lines for the output loop at %d:%d" (fst out) (snd out));
                None)
          outputs
      in
      if List.exists Option.is_none parts then None
      else
        match (kind, List.map Option.get parts) with
        | Transition, _ :: _ :: _ ->
            note (Printf.sprintf "several output loops for the input loop at line %d: no transition" pos.line);
            None
        | _, parts ->
            let value =
              match parts with [ c ] -> c | cs -> String.concat " || " (List.map (fun c -> "(" ^ c ^ ")") cs)
            in
            Some
              {
                Witness.inv_type = (if kind = Transition then Loop_transition_invariant else Loop_invariant);
                inv_location = { file_name = input_file; line = pos.line; column = pos.column; function_ = pos.func };
                inv_value = value;
                inv_format = (if kind = Transition then Ext_c_expression else C_expression);
              })
    inputs

(* The assumption waypoints of a FALSE result's path, from the state lines
   in their order: the first visit of each input loop, constraining the
   values the line gives there.  A waypoint at a loop statement is passed
   when the statement is reached, before the loop is entered, not at every
   iteration: CPAchecker 4.2.2 confirms a path with one assumption at a loop
   and does not confirm the same path with one per iteration.  So later
   visits are left out, as is a visit whose values cannot all be written: a
   waypoint fewer is still a sequence the execution follows. *)
let path_waypoints (record : Record.t) ~input_file note lines =
  let loop_heads = loop_heads record in
  let seen = ref [] in
  List.filter_map
    (function
      | Line ({ kind = State; loc; _ } as l) -> (
          match List.assoc_opt loc loop_heads with
          | None ->
              note (Printf.sprintf "a state at %d:%d, which is no loop head of the input" (fst loc) (snd loc));
              None
          | Some pos when List.mem pos !seen -> None
          | Some (pos : Record.input_position) -> (
              seen := pos :: !seen;
              match c_of_line record note (Line l) with
              | None -> None
              | Some value ->
                  Some
                    {
                      Witness.wp_type = Assumption;
                      action = Follow;
                      wp_location =
                        { file_name = input_file; line = pos.line; column = pos.column; function_ = pos.func };
                      constraint_ = Some { value; format = Some C_expression };
                    }))
      | _ -> None)
    lines
