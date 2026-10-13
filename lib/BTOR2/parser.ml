open Core
open Problem

(* A line-oriented reader for BTOR2. Each line is one node, and a node refers only to nodes
   defined before it, so the file is read in one pass without recursion; the models this reads
   run to hundreds of thousands of lines. The checks are those of the reference parser
   (btor2parser.c of btor2tools): a model it rejects is not BTOR2, and translating one would
   answer a question about something the format does not define. *)

exception Parse_error of int * string

let err lineno fmt = ksprintf (fun s -> raise (Parse_error (lineno, s))) fmt
let is_space c = Char.equal c ' ' || Char.equal c '\t'

let skip_spaces line pos =
  let n = String.length line in
  let rec go i = if i < n && is_space line.[i] then go (i + 1) else i in
  go pos

(* one whitespace-delimited token, or [None] at the end of the line or at a comment *)
let next_token line pos =
  let n = String.length line in
  let s = skip_spaces line pos in
  if s >= n || Char.equal line.[s] ';' then None
  else
    let rec stop e = if e < n && not (is_space line.[e]) then stop (e + 1) else e in
    let e = stop s in
    Some (String.sub line ~pos:s ~len:(e - s), e)

(* The rest of the line is an optional symbol. It may contain spaces, but a space followed by
   ';' starts a trailing comment. *)
let rest_as_symbol line pos =
  let n = String.length line in
  let s = skip_spaces line pos in
  if s >= n || Char.equal line.[s] ';' then None
  else
    let rec stop e =
      if e >= n then n
      else if is_space line.[e] && e + 1 < n && Char.equal line.[e + 1] ';' then e
      else stop (e + 1)
    in
    let rec trim e = if e > s && is_space line.[e - 1] then trim (e - 1) else e in
    let e = trim (stop s) in
    if e <= s then None else Some (String.sub line ~pos:s ~len:(e - s))

let tok line pos lineno what =
  match next_token line pos with
  | None -> err lineno "expected %s" what
  | Some tp -> tp

let int_tok line pos lineno what =
  let t, p = tok line pos lineno what in
  match Int.of_string_opt t with
  | None -> err lineno "expected %s, got %S" what t
  | Some v -> (v, p)

type state = {
  nodes : (int, node) Hashtbl.t;
  sorts : (int, sort) Hashtbl.t;
  inited : int Hash_set.t;
  nexted : int Hash_set.t;
  mutable last_id : int;
  mutable order : int list;
}

let sort_ref st line pos lineno =
  let id, pos = int_tok line pos lineno "sort id" in
  match Hashtbl.find st.sorts id with
  | None -> err lineno "undefined sort id %d" id
  | Some s -> (s, pos)

let parse_sort_decl st line pos lineno =
  let kind, pos = tok line pos lineno "sort kind" in
  match kind with
  | "bitvec" ->
      let w, pos = int_tok line pos lineno "bit width" in
      if w <= 0 then err lineno "bit width must be greater than 0";
      (Bitvec w, pos)
  | "array" ->
      let i, pos = sort_ref st line pos lineno in
      let e, pos = sort_ref st line pos lineno in
      (Array (i, e), pos)
  | _ -> err lineno "invalid sort tag %S" kind

let bitvec lineno what = function
  | Bitvec w -> w
  | Array _ -> err lineno "expected a bit-vector sort for %s" what

let arg_node st lineno a =
  match Hashtbl.find st.nodes (Int.abs a) with
  | None -> err lineno "undefined argument id %d" a
  | Some m -> (
      match m.tag with
      | Sort_decl | Init | Next | Bad | Constraint | Fair | Justice | Output ->
          err lineno "'%s' cannot be used as argument" (string_of_tag m.tag)
      | _ -> m)

let arg_sort st lineno a =
  match (arg_node st lineno a).nsort with
  | None -> err lineno "argument %d has no sort" a
  | Some s -> s

(* No input may occur below an initialization value. *)
let check_no_input_below st lineno v =
  let seen = Hash_set.create (module Int) in
  let rec go = function
    | [] -> ()
    | id :: rest ->
        let id = Int.abs id in
        if Hash_set.mem seen id then go rest
        else (
          Hash_set.add seen id;
          let n = Hashtbl.find_exn st.nodes id in
          if equal_tag n.tag Input then
            err lineno
              "inputs are not allowed in initialization expressions (input %d)" id;
          go (n.args @ rest))
  in
  go [ v ]

let check_node st (n : node) =
  let lineno = n.lineno in
  let name = string_of_tag n.tag in
  let asort i = arg_sort st lineno (List.nth_exn n.args i) in
  let awidth i = bitvec lineno name (asort i) in
  let self () =
    match n.nsort with Some s -> s | None -> err lineno "missing sort for %s" name
  in
  let selfw () = bitvec lineno name (self ()) in
  let same_as_self i =
    if not (equal_sort (asort i) (self ())) then
      err lineno "sort of argument %d of %s does not match its own sort" (i + 1) name
  in
  let width_1 () =
    if selfw () <> 1 then err lineno "expected a bit-vector of size 1 for %s" name
  in
  let literal () =
    match n.cst with Some c -> c | None -> err lineno "missing constant"
  in
  let state_arg () =
    let s = List.hd_exn n.args in
    if not (equal_tag (arg_node st lineno s).tag State) then
      err lineno "expected state as first argument of %s" name
  in
  match n.tag with
  | Sort_decl | Input | State -> ()
  | Const ->
      let c = literal () in
      if not (String.for_all c ~f:(fun ch -> Char.equal ch '0' || Char.equal ch '1'))
      then err lineno "invalid binary constant %S" c;
      if String.length c <> selfw () then
        err lineno "constant %S does not match bit-vector sort size %d" c (selfw ())
  | Constd ->
      let c = literal () in
      let w = selfw () in
      let z =
        try Z.of_string c with _ -> err lineno "invalid decimal constant %S" c
      in
      if Z.geq z (Z.shift_left Z.one w) || Z.lt z (Z.neg (Z.shift_left Z.one (w - 1)))
      then err lineno "constant %s does not match bit-vector sort size %d" c w
  | Consth ->
      let c = literal () in
      let w = selfw () in
      let z =
        try Z.of_string ("0x" ^ c)
        with _ -> err lineno "invalid hexadecimal constant %S" c
      in
      if Z.lt z Z.zero || Z.geq z (Z.shift_left Z.one w) then
        err lineno "constant %s does not fit into bit-vector of size %d" c w
  | One | Ones | Zero -> ignore (selfw ())
  | Not | Inc | Dec | Neg ->
      ignore (selfw ());
      same_as_self 0
  | Redand | Redor | Redxor ->
      width_1 ();
      ignore (awidth 0)
  | Slice -> (
      match n.imm with
      | [ u; l ] ->
          if u >= awidth 0 then err lineno "upper index %d is out of range" u;
          if selfw () <> u - l + 1 then
            err lineno "expected a bit-vector of size %d for slice" (u - l + 1)
      | _ -> err lineno "malformed slice")
  | Uext | Sext -> (
      match n.imm with
      | [ k ] ->
          if selfw () <> awidth 0 + k then
            err lineno "expected a bit-vector of size %d for %s" (awidth 0 + k) name
      | _ -> err lineno "malformed %s" name)
  | Add | And | Mul | Nand | Nor | Or | Rol | Ror | Sdiv | Sll | Smod | Sra | Srem | Srl
  | Sub | Udiv | Urem | Xnor | Xor ->
      ignore (selfw ());
      same_as_self 0;
      same_as_self 1
  | Uaddo | Ugt | Ugte | Ult | Ulte | Umulo | Usubo | Saddo | Sdivo | Sgt | Sgte | Slt
  | Slte | Smulo | Ssubo ->
      width_1 ();
      if awidth 0 <> awidth 1 then
        err lineno "sorts of the two arguments of %s do not match" name
  | Eq | Neq ->
      width_1 ();
      if not (equal_sort (asort 0) (asort 1)) then
        err lineno "sorts of the two arguments of %s do not match" name
  | Concat ->
      if selfw () <> awidth 0 + awidth 1 then
        err lineno "expected a bit-vector of size %d for concat" (awidth 0 + awidth 1)
  | Implies | Iff ->
      width_1 ();
      if awidth 0 <> 1 || awidth 1 <> 1 then
        err lineno "expected bit-vectors of size 1 for %s" name
  | Read -> (
      match asort 0 with
      | Array (i, e) ->
          if not (equal_sort (asort 1) i) then
            err lineno "index sort of read does not match the array";
          if not (equal_sort (self ()) e) then
            err lineno "sort of read does not match the element sort"
      | Bitvec _ -> err lineno "expected an array as the first argument of read")
  | Write -> (
      match asort 0 with
      | Array (i, e) ->
          if not (equal_sort (self ()) (asort 0)) then
            err lineno "sort of write does not match the array";
          if not (equal_sort (asort 1) i) then
            err lineno "index sort of write does not match the array";
          if not (equal_sort (asort 2) e) then
            err lineno "value sort of write does not match the element sort"
      | Bitvec _ -> err lineno "expected an array as the first argument of write")
  | Ite ->
      if bitvec lineno name (asort 0) <> 1 then
        err lineno "expected a bit-vector of size 1 as the condition of ite";
      if not (equal_sort (asort 1) (asort 2)) then
        err lineno "the two branches of ite have different sorts";
      if not (equal_sort (self ()) (asort 1)) then
        err lineno "sort of ite does not match its branches"
  | Init -> (
      state_arg ();
      let s = List.nth_exn n.args 0 and v = List.nth_exn n.args 1 in
      if s <= Int.abs v then
        err lineno "state id must be greater than id of second operand";
      check_no_input_below st lineno v;
      if not (equal_sort (asort 0) (self ())) then
        err lineno "sort of the state does not match the init line";
      match (self (), asort 1) with
      | Array (_, e), (Bitvec _ as v) ->
          (* an array state initialized by a bit-vector: the constant array of it *)
          if not (equal_sort v e) then
            err lineno "sort of the init value does not match the element sort"
      | _ ->
          if not (equal_sort (asort 1) (self ())) then
            err lineno "sort of the init value does not match the state")
  | Next ->
      state_arg ();
      if not (equal_sort (asort 0) (self ())) then
        err lineno "sort of the state does not match the next line";
      if not (equal_sort (asort 1) (self ())) then
        err lineno "sort of the next value does not match the state"
  | Bad | Constraint | Fair ->
      if bitvec lineno name (asort 0) <> 1 then
        err lineno "expected a bit-vector of size 1 for %s" name
  | Justice ->
      List.iteri n.args ~f:(fun i a ->
          if bitvec lineno name (arg_sort st lineno a) <> 1 then
            err lineno "expected a bit-vector of size 1 for justice argument %d" (i + 1))
  | Output -> ignore (arg_sort st lineno (List.hd_exn n.args))

(* initialized, or given a next value, at most once *)
let check_unique st (n : node) =
  let once set s =
    if Hash_set.mem set s then
      err n.lineno "%s for state %d set twice" (string_of_tag n.tag) s;
    Hash_set.add set s
  in
  match (n.tag, n.args) with
  | Init, s :: _ -> once st.inited s
  | Next, s :: _ -> once st.nexted s
  | _ -> ()

let operands k line pos lineno =
  let rec go i pos acc =
    if i = 0 then (List.rev acc, pos)
    else
      let a, pos = int_tok line pos lineno "argument id" in
      go (i - 1) pos (a :: acc)
  in
  go k pos []

let parse_line st lineno line =
  let s = skip_spaces line 0 in
  if s < String.length line && not (Char.equal line.[s] ';') then (
    let id, pos = int_tok line s lineno "node id" in
    if id <= 0 then err lineno "node id must be positive";
    if Hashtbl.mem st.nodes id || Hashtbl.mem st.sorts id then
      err lineno "id %d already defined" id;
    if id <= st.last_id then err lineno "id out-of-order";
    st.last_id <- id;
    let name, pos = tok line pos lineno "tag" in
    let tag =
      match tag_of_string name with
      | None -> err lineno "invalid tag %S" name
      | Some t -> t
    in
    let add ?nsort ?(args = []) ?(imm = []) ?cst pos =
      let n = { nid = id; lineno; tag; nsort; args; imm; cst; sym = rest_as_symbol line pos } in
      check_node st n;
      check_unique st n;
      Hashtbl.set st.nodes ~key:id ~data:n;
      st.order <- id :: st.order
    in
    match tag with
    | Sort_decl ->
        let srt, _ = parse_sort_decl st line pos lineno in
        Hashtbl.set st.sorts ~key:id ~data:srt
    | Input | State ->
        let srt, pos = sort_ref st line pos lineno in
        add ~nsort:srt pos
    | Const | Constd | Consth ->
        let srt, pos = sort_ref st line pos lineno in
        let lit, pos = tok line pos lineno "constant" in
        add ~nsort:srt ~cst:lit pos
    | One | Ones | Zero ->
        let srt, pos = sort_ref st line pos lineno in
        add ~nsort:srt pos
    | Slice ->
        let srt, pos = sort_ref st line pos lineno in
        let a, pos = int_tok line pos lineno "argument id" in
        let u, pos = int_tok line pos lineno "upper index" in
        let l, pos = int_tok line pos lineno "lower index" in
        if l < 0 || l > u then err lineno "invalid slice indices %d %d" u l;
        add ~nsort:srt ~args:[ a ] ~imm:[ u; l ] pos
    | Uext | Sext ->
        let srt, pos = sort_ref st line pos lineno in
        let a, pos = int_tok line pos lineno "argument id" in
        let k, pos = int_tok line pos lineno "extension width" in
        if k < 0 then err lineno "extension width must be non-negative";
        add ~nsort:srt ~args:[ a ] ~imm:[ k ] pos
    | Init | Next ->
        let srt, pos = sort_ref st line pos lineno in
        let a, pos = int_tok line pos lineno "state id" in
        if a < 0 then err lineno "invalid negated first argument";
        let v, pos = int_tok line pos lineno "value id" in
        add ~nsort:srt ~args:[ a; v ] pos
    | Bad | Constraint | Fair | Output ->
        let a, pos = int_tok line pos lineno "argument id" in
        add ~args:[ a ] pos
    | Justice ->
        let k, pos = int_tok line pos lineno "number of conditions" in
        if k < 0 then err lineno "negative number of conditions";
        let args, pos = operands k line pos lineno in
        add ~args pos
    | Not | Inc | Dec | Neg | Redand | Redor | Redxor ->
        let srt, pos = sort_ref st line pos lineno in
        let args, pos = operands 1 line pos lineno in
        add ~nsort:srt ~args pos
    | Ite | Write ->
        let srt, pos = sort_ref st line pos lineno in
        let args, pos = operands 3 line pos lineno in
        add ~nsort:srt ~args pos
    | _ ->
        let srt, pos = sort_ref st line pos lineno in
        let args, pos = operands 2 line pos lineno in
        add ~nsort:srt ~args pos)

let of_channel ic =
  let st =
    {
      nodes = Hashtbl.create (module Int);
      sorts = Hashtbl.create (module Int);
      inited = Hash_set.create (module Int);
      nexted = Hash_set.create (module Int);
      last_id = 0;
      order = [];
    }
  in
  ignore
  @@ In_channel.fold_lines ic ~init:1 ~f:(fun lineno line ->
      parse_line st lineno line;
      lineno + 1);
  { nodes = st.nodes; order = List.rev st.order }

let from_file filename =
  try Ok (In_channel.with_file filename ~f:of_channel)
  with Parse_error (lineno, msg) ->
    Or_error.error_string (sprintf "%s:%d: syntax error: %s" filename lineno msg)
