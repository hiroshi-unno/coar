open Core

(** A word-level hardware model in BTOR2 (A. Niemetz, M. Preiner, C. Wolf, A. Biere, "Btor2, BtorMC
    and Boolector 3.0", CAV 2018), and the transition system it denotes. The format has no
    standalone grammar; the tags, their operand shapes and the well-formedness rules follow the
    reference parser of the btor2tools package. *)

type sort = Bitvec of int | Array of sort * sort [@@deriving eq]

type tag =
  | Sort_decl
  | Input
  | State
  | Const
  | Constd
  | Consth
  | One
  | Ones
  | Zero
  | Not
  | Inc
  | Dec
  | Neg
  | Redand
  | Redor
  | Redxor
  | Slice
  | Uext
  | Sext
  | Add
  | And
  | Mul
  | Nand
  | Nor
  | Or
  | Rol
  | Ror
  | Sdiv
  | Sll
  | Smod
  | Sra
  | Srem
  | Srl
  | Sub
  | Udiv
  | Urem
  | Xnor
  | Xor
  | Uaddo
  | Ugt
  | Ugte
  | Ult
  | Ulte
  | Umulo
  | Usubo
  | Saddo
  | Sdivo
  | Sgt
  | Sgte
  | Slt
  | Slte
  | Smulo
  | Ssubo
  | Eq
  | Neq
  | Concat
  | Implies
  | Iff
  | Read
  | Ite
  | Write
  | Init
  | Next
  | Bad
  | Constraint
  | Fair
  | Justice
  | Output
[@@deriving eq]

let names =
  [
    (Sort_decl, "sort");
    (Input, "input");
    (State, "state");
    (Const, "const");
    (Constd, "constd");
    (Consth, "consth");
    (One, "one");
    (Ones, "ones");
    (Zero, "zero");
    (Not, "not");
    (Inc, "inc");
    (Dec, "dec");
    (Neg, "neg");
    (Redand, "redand");
    (Redor, "redor");
    (Redxor, "redxor");
    (Slice, "slice");
    (Uext, "uext");
    (Sext, "sext");
    (Add, "add");
    (And, "and");
    (Mul, "mul");
    (Nand, "nand");
    (Nor, "nor");
    (Or, "or");
    (Rol, "rol");
    (Ror, "ror");
    (Sdiv, "sdiv");
    (Sll, "sll");
    (Smod, "smod");
    (Sra, "sra");
    (Srem, "srem");
    (Srl, "srl");
    (Sub, "sub");
    (Udiv, "udiv");
    (Urem, "urem");
    (Xnor, "xnor");
    (Xor, "xor");
    (Uaddo, "uaddo");
    (Ugt, "ugt");
    (Ugte, "ugte");
    (Ult, "ult");
    (Ulte, "ulte");
    (Umulo, "umulo");
    (Usubo, "usubo");
    (Saddo, "saddo");
    (Sdivo, "sdivo");
    (Sgt, "sgt");
    (Sgte, "sgte");
    (Slt, "slt");
    (Slte, "slte");
    (Smulo, "smulo");
    (Ssubo, "ssubo");
    (Eq, "eq");
    (Neq, "neq");
    (Concat, "concat");
    (Implies, "implies");
    (Iff, "iff");
    (Read, "read");
    (Ite, "ite");
    (Write, "write");
    (Init, "init");
    (Next, "next");
    (Bad, "bad");
    (Constraint, "constraint");
    (Fair, "fair");
    (Justice, "justice");
    (Output, "output");
  ]

let tag_of_string s =
  List.find_map names ~f:(fun (t, n) -> if String.equal n s then Some t else None)

let string_of_tag t =
  snd @@ List.find_exn names ~f:(fun (t', _) -> equal_tag t t')

let rec string_of_sort = function
  | Bitvec w -> sprintf "bitvec %d" w
  | Array (i, e) -> sprintf "array (%s) (%s)" (string_of_sort i) (string_of_sort e)

type node = {
  nid : int;
  lineno : int;
  tag : tag;
  nsort : sort option;  (** absent for sort declarations and properties *)
  args : int list;  (** operand ids; a negative id is the bitwise negation of the node *)
  imm : int list;  (** [slice]: upper and lower index; [uext]/[sext]: the extension width *)
  cst : string option;  (** the literal of [const]/[constd]/[consth] *)
  sym : string option;
}

type t = {
  nodes : (int, node) Hashtbl.t;
  order : int list;  (** node ids in file order, sort declarations excluded *)
}

let find m id =
  match Hashtbl.find m.nodes (Int.abs id) with
  | Some n -> n
  | None -> failwithf "BTOR2: undefined node id %d" id ()

let sort_of m id =
  match (find m id).nsort with
  | Some s -> s
  | None -> failwithf "BTOR2: node %d has no sort" id ()

(** The transition system of a model. A state with a [next] line is registered; one without is
    free, and behaves as an input at every time, time 0 included, whether or not it has an [init]
    ("A state variable without associated next function is treated as a primary input", CAV 2018,
    section 2). *)
type ts = {
  model : t;
  states : int list;  (** in file order *)
  inputs : int list;  (** in file order *)
  init : (int, int) Hashtbl.t;  (** state id to the signed id of its initial value *)
  next : (int, int) Hashtbl.t;  (** state id to the signed id of its next value *)
  constraints : int list;  (** signed ids *)
  bads : int list;  (** signed ids, in file order *)
  justices : int list list;
  fairs : int list;
}

let ts_of (m : t) =
  let init = Hashtbl.create (module Int) and next = Hashtbl.create (module Int) in
  let states, inputs, constraints, bads, justices, fairs =
    List.fold m.order ~init:([], [], [], [], [], [])
      ~f:(fun (st, inp, cs, bs, js, fs) id ->
        let n = find m id in
        match (n.tag, n.args) with
        | State, _ -> (id :: st, inp, cs, bs, js, fs)
        | Input, _ -> (st, id :: inp, cs, bs, js, fs)
        | Init, [ s; v ] ->
            Hashtbl.set init ~key:s ~data:v;
            (st, inp, cs, bs, js, fs)
        | Next, [ s; v ] ->
            Hashtbl.set next ~key:s ~data:v;
            (st, inp, cs, bs, js, fs)
        | Constraint, [ c ] -> (st, inp, c :: cs, bs, js, fs)
        | Bad, [ b ] -> (st, inp, cs, b :: bs, js, fs)
        | Justice, args -> (st, inp, cs, bs, args :: js, fs)
        | Fair, [ f ] -> (st, inp, cs, bs, js, f :: fs)
        | _ -> (st, inp, cs, bs, js, fs))
  in
  {
    model = m;
    states = List.rev states;
    inputs = List.rev inputs;
    init;
    next;
    constraints = List.rev constraints;
    bads = List.rev bads;
    justices = List.rev justices;
    fairs = List.rev fairs;
  }

let is_registered ts s = Hashtbl.mem ts.next s

(** The nodes the value of [roots] can depend on: their operands, transitively, and for every
    state reached its [init] and [next] values, which may reach further states. A node outside the
    cone is read by nothing inside it, so a trace of the reduced system extends to one of the full
    system by giving each dropped state any value its [init] and [next] allow, and every trace of
    the full system restricts to one of the reduced. *)
let cone ts roots =
  let seen = Hash_set.create (module Int) in
  let rec visit = function
    | [] -> ()
    | id :: rest ->
        let id = Int.abs id in
        if Hash_set.mem seen id then visit rest
        else (
          Hash_set.add seen id;
          let n = find ts.model id in
          let succs =
            match n.tag with
            | State ->
                List.filter_opt [ Hashtbl.find ts.init id; Hashtbl.find ts.next id ]
            | _ -> []
          in
          visit (succs @ n.args @ rest))
  in
  visit roots;
  seen
