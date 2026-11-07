(* The translation of [main], after inlining, into a labelled transition
   system for the unreach-call or the termination property.

   For unreach-call, a call to reach_error (or __VERIFIER_error, its name in
   older tasks) moves to the error location.  For
   termination there is no error location: reach_error, like abort, exit and
   __assert_fail, ends the execution, which is a move to a location with no
   outgoing transition, as returning from main is; __VERIFIER_assume(0)
   loops forever, as SV-COMP's rules say a verifier may assume.

   Each basic block is a location.  Its instructions become the commands of
   the transitions leaving it; a phi becomes an assignment on the edge into
   its block.  An instruction that chooses between values (a select, a
   comparison whose result is used as a value) ends the current transition
   at a fresh location and continues from there.

   Only executions without undefined behaviour are kept: before an
   operation that would be UB, or would produce poison (a signed overflow
   under nsw, a shift by the width or more), the transition assumes it is
   not, so an execution that would reach UB stops there.  Under that
   reading poison never reaches a use.

   Memory is the variables whose address is taken and the arrays of
   integers, local and global, each one variable of the LTS (an array
   variable for an array); an access is located from the shape of its
   address, a global or an alloca possibly through getelementptr, with no
   alias analysis.  Array indices are not checked against the length: an
   access out of bounds is UB, which the translation assumes away.

   Values are bit-vectors in BV mode and mathematical integers in the Int
   modes (Lts.ints).  In Plain and Bitwise no operation wraps: the result
   agrees with C as long as no operation leaves its type's range, which
   those modes assume.  Bitwise reads and, or, xor and shifts by a constant
   in infinite two's complement.  Wrap_unsigned and Wrap_all keep every iN
   value as its unsigned representative in [0, 2^N) and reduce every result
   into that range, which is the IR's arithmetic; the signed reading of a
   value, where an instruction asks for it, is x - 2^N when x >= 2^(N-1).
   Bit operations between two variables wider than i1, shifts by a variable
   amount and the intrinsics that are bit manipulations are outside every
   Int mode. *)

open Lts

type property = Unreach_call | Termination

(* An object in memory (Memory) and its components, each one variable of
   the LTS: an array variable when [carray], indexed by 64-bit values in BV
   mode. *)
type cvar = { comp : Memory.comp; cname : string; carray : bool }

type obj = {
  name : string;
  value : Llvm.llvalue;  (** the alloca or the global variable *)
  elem : Llvm.lltype;
  count : int option;  (** how many values of [elem]; [None] when variable *)
  comps : cvar list;
}

type state = {
  mode : mode;
  unbounded_nondet : bool;
      (** in the non-wrapping Int modes, a __VERIFIER_nondet_T is any
          integer rather than one of T's range *)
  ids : (Llvm.llvalue, int) Hashtbl.t;
  blocks : (Llvm.llbasicblock, string) Hashtbl.t;
  widths : (string, int) Hashtbl.t;
  mutable next_id : int;
  mutable transitions : transition list;
  (* Comparisons used only as conditions in their own block: their
     condition is used in place, and no variable holds them. *)
  in_place : (Llvm.llvalue, unit) Hashtbl.t;
  (* For each *.with.overflow call, the variables of its two fields. *)
  pairs : (Llvm.llvalue, string * string) Hashtbl.t;
  (* Whether some transition goes to the location that loops forever. *)
  mutable diverges : bool;
  layout : Llvm_target.DataLayout.t;
  (* Loads kept as their parts (bit position, width, value) rather than
     assembled into one integer, because they are only stored. *)
  parts : (Llvm.llvalue, (int * int * expr) list) Hashtbl.t;
  objects : (Llvm.llvalue, obj) Hashtbl.t;
  (* The array variables and their element widths. *)
  arrays : (string, int) Hashtbl.t;
  (* The objects in the order they were met, latest first. *)
  mutable object_order : obj list;
}

let error_location = "error"
let end_location = "end"
let diverge_location = "diverge"
let unknown = Scope.unknown

let width v = Llvm.integer_bitwidth (Llvm.type_of v)

let fresh st =
  st.next_id <- st.next_id + 1;
  st.next_id

let declare st name n = if st.mode = Bv then Hashtbl.replace st.widths name n

let is_int st = match st.mode with Int _ -> true | Bv -> false

(* The Int modes whose values are unsigned representatives. *)
let wraps st = match st.mode with Int (Wrap_unsigned | Wrap_all) -> true | _ -> false

let var st v =
  let id =
    match Hashtbl.find_opt st.ids v with
    | Some id -> id
    | None ->
        let id = fresh st in
        Hashtbl.add st.ids v id;
        id
  in
  let name = Printf.sprintf "v%d" id in
  declare st name (width v);
  name

let temp st n =
  let name = Printf.sprintf "t%d" (fresh st) in
  declare st name n;
  name

let global_name g =
  "g_"
  ^ String.map
      (fun c ->
        match c with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> c | _ -> '_')
      (Llvm.value_name g)

let block_location st block =
  match Hashtbl.find_opt st.blocks block with
  | Some name -> name
  | None ->
      let name = Printf.sprintf "b%d" (fresh st) in
      Hashtbl.add st.blocks block name;
      name

(* -- Constants -------------------------------------------------------- *)

(* Decimal numerals of any size, for the unsigned reading of a negative
   constant: [two_pow n] is 2^n, and [sub_decimal a b] is a - b for
   non-negative numerals with a >= b. *)
let two_pow n =
  let double s =
    let carry, digits =
      List.fold_right
        (fun ch (carry, acc) ->
          let d = (2 * (Char.code ch - 48)) + carry in
          (d / 10, Char.chr (48 + (d mod 10)) :: acc))
        (List.init (String.length s) (String.get s))
        (0, [])
    in
    String.of_seq (List.to_seq (if carry > 0 then '1' :: digits else digits))
  in
  let rec go k s = if k = 0 then s else go (k - 1) (double s) in
  go n "1"

let sub_decimal a b =
  let la = String.length a and lb = String.length b in
  let digit s l i = if i < l then Char.code s.[l - 1 - i] - 48 else 0 in
  let buf = Bytes.make la '0' in
  let borrow = ref 0 in
  for i = 0 to la - 1 do
    let d = digit a la i - digit b lb i - !borrow in
    borrow := if d < 0 then 1 else 0;
    Bytes.set buf (la - 1 - i) (Char.chr (48 + ((d + 10) mod 10)))
  done;
  let s = Bytes.to_string buf in
  let rec first i = if i < la - 1 && s.[i] = '0' then first (i + 1) else i in
  String.sub s (first 0) (la - first 0)

(* The value of an integer constant as a decimal string: as a signed number,
   or, when [unsigned], as an unsigned one (2^N plus the signed value when
   that is negative).  An i1 constant is always 0 or 1.  T2 literals have no
   size limit, so any width is written exactly. *)
let constant_value ~unsigned c =
  let n = width c in
  let signed =
    match Llvm.int64_of_const c with
    | Some x -> Some (Int64.to_string x, x < 0L)
    | None -> (
        (* Wider than 64 bits: read the printed form "iN value". *)
        match String.split_on_char ' ' (Llvm.string_of_llvalue c) with
        | [ _; digits ] -> Some (digits, String.length digits > 0 && digits.[0] = '-')
        | _ -> None)
  in
  match signed with
  | None -> None
  | Some (s, negative) ->
      if n = 1 then Some (if negative || s = "1" then "1" else "0")
      else if negative && unsigned then
        Some (sub_decimal (two_pow n) (String.sub s 1 (String.length s - 1)))
      else Some s

let constant at ~unsigned c =
  match constant_value ~unsigned c with
  | Some s -> Const s
  | None -> unknown at "the constant %s cannot be read" (Llvm.string_of_llvalue c)

(* -- Integer arithmetic in the Int modes ----------------------------- *)

let pow2 k = Const (two_pow k)

(* e mod 2^k, in [0, 2^k), and the floor of e / 2^k.  T2's / and % round
   towards zero, which is floor for a non-negative e ([nonneg]); otherwise
   the remainder is first made non-negative. *)
let mod2 ~nonneg e k =
  if k = 0 then Const "0"
  else if nonneg then Infix ("%", e, pow2 k)
  else Infix ("%", Infix ("+", Infix ("%", e, pow2 k), pow2 k), pow2 k)

let div2 ~nonneg e k =
  if k = 0 then e
  else if nonneg then Infix ("/", e, pow2 k)
  else Infix ("/", Infix ("-", e, mod2 ~nonneg e k), pow2 k)

(* -2^(n-1) <= e < 2^(n-1) *)
let in_signed_range n e =
  And
    ( Compare (">=", e, Const ("-" ^ two_pow (n - 1))),
      Compare ("<", e, pow2 (n - 1)) )

(* The signed value of an n-bit unsigned representative x: x - 2^n when
   x >= 2^(n-1), and x / 2^(n-1) is exactly that test (0 or 1). *)
let to_signed n e =
  Infix ("-", e, Infix ("*", pow2 n, Infix ("/", e, pow2 (n - 1))))

(* In the wrapping Int modes, the commands that confine a variable v of n
   bits whose value comes from outside the arithmetic (a nondet, a memory
   cell whose contents may be arbitrary) to the representatives. *)
let representative st v n =
  if wraps st then
    [ Assume (And (Compare (">=", Var v, Const "0"), Compare ("<", Var v, pow2 n))) ]
  else []

(* -- Operands --------------------------------------------------------- *)

let rec term st at ?(unsigned = false) v =
  match Llvm.classify_value v with
  | ConstantInt -> constant at ~unsigned:(wraps st || (unsigned && is_int st)) v
  | PoisonValue -> Nondet "nondet"
  | Instruction ICmp when Hashtbl.mem st.in_place v ->
      unknown at "a comparison used as a value"
  | Instruction _ | Argument -> Var (var st v)
  | ConstantExpr -> unknown at "a constant expression operand"
  | _ -> unknown at "an operand of kind %s" (Llvm.string_of_llvalue v)

(* An operand read as signed by the instruction using it: in the wrapping
   Int modes, the signed value of its unsigned representative; otherwise
   the operand itself. *)
and signed_term st at v =
  if not (wraps st) then term st at v
  else
    match Llvm.classify_value v with
    | ConstantInt -> constant at ~unsigned:false v
    | _ -> to_signed (width v) (term st at v)

and icmp_cond st at instr =
  let pred =
    match Llvm.icmp_predicate instr with
    | Some p -> p
    | None -> unknown at "a comparison without a predicate"
  in
  let unsigned =
    match pred with Ugt | Uge | Ult | Ule -> true | _ -> false
  in
  let signed = match pred with Sgt | Sge | Slt | Sle -> true | _ -> false in
  let operand i =
    if signed then signed_term st at (Llvm.operand instr i)
    else term st at ~unsigned (Llvm.operand instr i)
  in
  let a = operand 0 in
  let b = operand 1 in
  let op =
    match (pred, st.mode) with
    | Eq, _ -> "=="
    | Ne, _ -> "!="
    | (Sgt | Ugt), Int _ | Sgt, Bv -> ">"
    | (Sge | Uge), Int _ | Sge, Bv -> ">="
    | (Slt | Ult), Int _ | Slt, Bv -> "<"
    | (Sle | Ule), Int _ | Sle, Bv -> "<="
    | Ugt, Bv -> "ugt"
    | Uge, Bv -> "uge"
    | Ult, Bv -> "ult"
    | Ule, Bv -> "ule"
  in
  Compare (op, a, b)

(* The condition that an i1 value is true. *)
and truth st at v =
  match Llvm.classify_value v with
  | Instruction ICmp when Hashtbl.mem st.in_place v -> icmp_cond st at v
  | ConstantInt -> (
      match constant_value ~unsigned:true v with
      | Some "0" -> Not True
      | _ -> True)
  | _ -> Compare ("!=", term st at v, Const "0")

(* -- Transitions ------------------------------------------------------ *)

(* The transition being built: where it starts and its commands so far. *)
type segment = { mutable loc : string; mutable commands : command list }

let emit seg c = seg.commands <- c :: seg.commands

let finish st seg ?(extra = []) dst =
  st.transitions <-
    { src = seg.loc; commands = List.rev seg.commands @ extra; dst }
    :: st.transitions

(* Ends the current transition with one transition per case, each guarded by
   its condition, all meeting at a fresh location where the block goes on. *)
let branch st seg cases =
  let next = Printf.sprintf "%s_%d" seg.loc (fresh st) in
  List.iter
    (fun (guard, commands) ->
      st.transitions <-
        {
          src = seg.loc;
          commands = List.rev seg.commands @ (Assume guard :: commands);
          dst = next;
        }
        :: st.transitions)
    cases;
  seg.loc <- next;
  seg.commands <- []

(* -- Integer operations ----------------------------------------------- *)

let int_mode_only_arith st at what =
  if is_int st then unknown at "%s in Int mode" what

(* [e] taken at [n] bits, sign- or zero-extended to [m] bits (BV mode). *)
let sext n m e = Apply ("sign_extend", [ string_of_int n; string_of_int m ], [ e ])
let zext n m e = Apply ("zero_extend", [ string_of_int n; string_of_int m ], [ e ])
let extract h l e = Apply ("extract", [ string_of_int h; string_of_int l ], [ e ])

(* No overflow of [a op b] at [n] bits when computed one bit wider: the top
   two bits of the wider result are equal, i.e. it is 0 or 3 read unsigned. *)
let no_signed_overflow n op a b =
  let wide = Infix (op, sext n (n + 1) a, sext n (n + 1) b) in
  let top = extract n (n - 1) wide in
  Or (Compare ("==", top, Const "0"), Compare ("==", top, Const "3"))

let no_unsigned_overflow n op a b =
  let wide = Infix (op, zext n (n + 1) a, zext n (n + 1) b) in
  Compare ("==", extract n n wide, Const "0")

(* Multiplication needs twice the width: no overflow when the upper n + 1
   bits of the 2n-bit product are all equal (signed) or all zero
   (unsigned). *)
let no_signed_mul_overflow n a b =
  let wide = Infix ("*", sext n (2 * n) a, sext n (2 * n) b) in
  let top = extract ((2 * n) - 1) (n - 1) wide in
  Or (Compare ("==", top, Const "0"), Compare ("==", top, Const "-1"))

let no_unsigned_mul_overflow n a b =
  let wide = Infix ("*", zext n (2 * n) a, zext n (2 * n) b) in
  Compare ("==", extract ((2 * n) - 1) n wide, Const "0")

let shift name a s = Apply (name, [], [ a; s ])

(* -- Bit operations in the Int modes ------------------------------------ *)

(* The maximal runs [lo, hi) of 1 bits of a constant c.  With [bits] =
   Some n only its n low bits are read (an unsigned representative); with
   None its signed value is read in infinite two's complement, so a
   negative c ends in a run with no upper end (hi = None). *)
let one_runs c ~bits =
  let top = match bits with Some n -> n | None -> 64 in
  let bit i = Int64.logand (Int64.shift_right_logical c i) 1L = 1L in
  let rec go i start acc =
    if i >= top then
      match start with
      | None -> List.rev acc
      | Some lo -> List.rev ((lo, if bits = None then None else Some top) :: acc)
    else
      match (bit i, start) with
      | true, None -> go (i + 1) (Some i) acc
      | true, Some _ -> go (i + 1) start acc
      | false, Some lo -> go (i + 1) None ((lo, Some i) :: acc)
      | false, None -> go (i + 1) None acc
  in
  go 0 None []

(* x & c for a constant c: the bits [lo, hi) of x weigh (x mod 2^hi) -
   (x mod 2^lo), and the bits from lo upwards weigh x - (x mod 2^lo), which
   holds in infinite two's complement for a negative x too.  With [width] =
   Some n, x is an n-bit unsigned representative, so x mod 2^n = x. *)
let and_const ~width x c =
  let nonneg = width <> None in
  let m k = if Some k = width then x else mod2 ~nonneg x k in
  let part (lo, hi) =
    let upper = match hi with Some k -> m k | None -> x in
    if lo = 0 then upper else Infix ("-", upper, m lo)
  in
  match List.map part (one_runs c ~bits:width) with
  | [] -> Const "0"
  | p :: ps -> List.fold_left (fun acc p -> Infix ("+", acc, p)) p ps

(* and, or and xor in an Int mode other than Plain.  With a constant
   operand c: x & c as above, x | c = x + c - (x & c) and x ^ c = x + c -
   2 (x & c), identities of infinite two's complement.  Between two i1
   values, which are 0 or 1, by their sum.  An i1 constant is 0 or 1 in
   every Int mode, so i1 is read as unsigned in all of them. *)
let bitwise_int st at instr op =
  let n = width instr in
  let x0 = Llvm.operand instr 0 and x1 = Llvm.operand instr 1 in
  let const v =
    match Llvm.classify_value v with ConstantInt -> Llvm.int64_of_const v | _ -> None
  in
  let with_const x cv c =
    let unsigned = wraps st || n = 1 in
    let x = term st at x in
    let lit = constant at ~unsigned cv in
    let conj_ = and_const ~width:(if unsigned then Some n else None) x c in
    match op with
    | Llvm.Opcode.And -> conj_
    | Or -> Infix ("-", Infix ("+", x, lit), conj_)
    | _ -> Infix ("-", Infix ("+", x, lit), Infix ("*", Const "2", conj_))
  in
  match (const x1, const x0) with
  | Some c, _ -> with_const x0 x1 c
  | None, Some c -> with_const x1 x0 c
  | None, None ->
      if n <> 1 then unknown at "a bitwise operation between two variables in Int mode";
      let sum = Infix ("+", term st at x0, term st at x1) in
      (match op with
      | And -> Infix ("/", sum, Const "2")
      | Or -> Infix ("-", sum, Infix ("/", sum, Const "2"))
      | _ -> Infix ("%", sum, Const "2"))

(* A shift by a constant k in an Int mode other than Plain, with the guards
   for poison: k at least the width, and the flags.  Without wrapping, x <<
   k is x * 2^k and x >> k (logical and arithmetic alike, the operand
   being taken as in its type's range) the floor of x / 2^k.  On an
   unsigned representative x, x << k is reduced, and the arithmetic shift
   adds the copies of the sign bit, 2^n - 2^(n-k) when x >= 2^(n-1). *)
let shift_int st at instr op =
  let n = width instr in
  let a = term st at (Llvm.operand instr 0) in
  let k =
    match Llvm.int64_of_const (Llvm.operand instr 1) with
    | Some k when Llvm.classify_value (Llvm.operand instr 1) = ConstantInt -> k
    | _ -> unknown at "a shift by a variable amount in Int mode"
  in
  if k < 0L || k >= Int64.of_int n then (Not True, Const "0")
  else
    let k = Int64.to_int k in
    let exact () =
      if Ir.is_exact instr then Compare ("==", Infix ("%", a, pow2 k), Const "0")
      else True
    in
    match (st.mode, op) with
    | Int ((Wrap_unsigned | Wrap_all) as w), Llvm.Opcode.Shl ->
        let r = Infix ("*", a, pow2 k) in
        let nsw =
          if w = Wrap_unsigned && Ir.has_nsw instr then
            in_signed_range n (Infix ("*", to_signed n a, pow2 k))
          else True
        in
        let nuw = if Ir.has_nuw instr then Compare ("<", r, pow2 n) else True in
        (conj nsw nuw, Infix ("%", r, pow2 n))
    | Int (Wrap_unsigned | Wrap_all), LShr -> (exact (), div2 ~nonneg:true a k)
    | Int (Wrap_unsigned | Wrap_all), _ ->
        ( exact (),
          Infix
            ( "+",
              div2 ~nonneg:true a k,
              Infix
                ( "*",
                  Infix ("/", a, pow2 (n - 1)),
                  Const (sub_decimal (two_pow n) (two_pow (n - k))) ) ) )
    | _, Shl -> (True, Infix ("*", a, pow2 k))
    | _ -> (exact (), div2 ~nonneg:false a k)

(* The guards and value of an arithmetic instruction in the wrapping Int
   modes: the result reduced into [0, 2^n), the operands read as signed
   where the instruction is signed.  nsw is read only with [nsw_read]. *)
let arith_wrap st at instr ~nsw_read =
  let n = width instr in
  let op = Llvm.instr_opcode instr in
  let m = pow2 n in
  let a = term st at (Llvm.operand instr 0) in
  let b = term st at (Llvm.operand instr 1) in
  let sa () = signed_term st at (Llvm.operand instr 0) in
  let sb () = signed_term st at (Llvm.operand instr 1) in
  let guard_if c g = if c then g else True in
  let nsw () = nsw_read && Ir.has_nsw instr and nuw () = Ir.has_nuw instr in
  (* e in (-2^n, 2^n) made a representative *)
  let rep e = Infix ("%", Infix ("+", e, m), m) in
  let nonzero = Compare ("!=", b, Const "0") in
  match op with
  | Add ->
      ( conj
          (guard_if (nsw ()) (in_signed_range n (Infix ("+", sa (), sb ()))))
          (guard_if (nuw ()) (Compare ("<", Infix ("+", a, b), m))),
        Infix ("%", Infix ("+", a, b), m) )
  | Sub ->
      ( conj
          (guard_if (nsw ()) (in_signed_range n (Infix ("-", sa (), sb ()))))
          (guard_if (nuw ()) (Compare (">=", a, b))),
        rep (Infix ("-", a, b)) )
  | Mul ->
      ( conj
          (guard_if (nsw ()) (in_signed_range n (Infix ("*", sa (), sb ()))))
          (guard_if (nuw ()) (Compare ("<", Infix ("*", a, b), m))),
        Infix ("%", Infix ("*", a, b), m) )
  | UDiv ->
      ( conj nonzero
          (guard_if (Ir.is_exact instr) (Compare ("==", Infix ("%", a, b), Const "0"))),
        Infix ("/", a, b) )
  | URem -> (nonzero, Infix ("%", a, b))
  | SDiv | SRem ->
      (* INT_MIN / -1 overflows: the representatives 2^(n-1) and 2^n - 1. *)
      let no_overflow =
        Or
          ( Compare ("!=", a, pow2 (n - 1)),
            Compare ("!=", b, Const (sub_decimal (two_pow n) "1")) )
      in
      let sa = sa () and sb = sb () in
      let exact =
        guard_if (op = SDiv && Ir.is_exact instr)
          (Compare ("==", Infix ("%", sa, sb), Const "0"))
      in
      ( conj (conj nonzero no_overflow) exact,
        rep (Infix ((if op = SDiv then "/" else "%"), sa, sb)) )
  | Shl | LShr | AShr -> shift_int st at instr op
  | And | Or | Xor -> (True, bitwise_int st at instr op)
  | _ -> unknown at "the instruction %s" (Ir.opcode_name op)

(* The guards an arithmetic instruction needs to be free of UB and poison,
   and its value. *)
let arith st at instr =
  match st.mode with
  | Int ((Wrap_unsigned | Wrap_all) as w) ->
      arith_wrap st at instr ~nsw_read:(w = Wrap_unsigned)
  | _ ->
  let n = width instr in
  let op = Llvm.instr_opcode instr in
  let unsigned_operands =
    match op with UDiv | URem | LShr -> true | _ -> false
  in
  let a = term st at ~unsigned:unsigned_operands (Llvm.operand instr 0) in
  let b = term st at ~unsigned:unsigned_operands (Llvm.operand instr 1) in
  let bv = st.mode = Bv in
  let nsw () = bv && Ir.has_nsw instr and nuw () = bv && Ir.has_nuw instr in
  let exact () = Ir.is_exact instr in
  let guard_if c g = if c then g else True in
  let nonzero = Compare ("!=", b, Const "0") in
  (* INT_MIN / -1 overflows; INT_MIN is the one nonzero value equal to its
     own negation, which avoids writing 2^(n-1) as a literal. *)
  let not_min_by_minus_one =
    if bv then
      Or
        ( Compare ("!=", b, Const "-1"),
          Or (Compare ("==", a, Const "0"), Compare ("!=", a, Neg a)) )
    else True
  in
  match op with
  | Add ->
      ( conj
          (guard_if (nsw ()) (no_signed_overflow n "+" a b))
          (guard_if (nuw ()) (no_unsigned_overflow n "+" a b)),
        Infix ("+", a, b) )
  | Sub ->
      ( conj
          (guard_if (nsw ()) (no_signed_overflow n "-" a b))
          (guard_if (nuw ()) (no_unsigned_overflow n "-" a b)),
        Infix ("-", a, b) )
  | Mul ->
      ( conj
          (guard_if (nsw ()) (no_signed_mul_overflow n a b))
          (guard_if (nuw ()) (no_unsigned_mul_overflow n a b)),
        Infix ("*", a, b) )
  | SDiv ->
      ( conj (conj nonzero not_min_by_minus_one)
          (guard_if (exact ()) (Compare ("==", Infix ("%", a, b), Const "0"))),
        Infix ("/", a, b) )
  | SRem -> (conj nonzero not_min_by_minus_one, Infix ("%", a, b))
  | UDiv ->
      let div, rem = if bv then ("udiv", "urem") else ("/", "%") in
      ( conj nonzero
          (guard_if (exact ()) (Compare ("==", Infix (rem, a, b), Const "0"))),
        Infix (div, a, b) )
  | URem -> (nonzero, Infix ((if bv then "urem" else "%"), a, b))
  | (Shl | LShr | AShr) when st.mode = Int Bitwise -> shift_int st at instr op
  | (And | Or | Xor) when st.mode = Int Bitwise -> (True, bitwise_int st at instr op)
  | Shl | LShr | AShr | And | Or | Xor -> (
      int_mode_only_arith st at "a bitwise operation";
      let in_range = Compare ("ult", b, Const (string_of_int n)) in
      match op with
      | Shl ->
          let r = shift "shl" a b in
          ( conj in_range
              (conj
                 (guard_if (Ir.has_nsw instr)
                    (Compare ("==", shift "ashr" r b, a)))
                 (guard_if (Ir.has_nuw instr)
                    (Compare ("==", shift "lshr" r b, a)))),
            r )
      | LShr | AShr ->
          let name = if op = LShr then "lshr" else "ashr" in
          let r = shift name a b in
          ( conj in_range
              (guard_if (exact ()) (Compare ("==", shift "shl" r b, a))),
            r )
      | And -> (True, Apply ("and", [], [ a; b ]))
      | Or -> (True, Apply ("or", [], [ a; b ]))
      | _ ->
          (* T2 has no xor: a xor b = (a or b) - (a and b), since the bits
             set in both are counted once in the or and once in the and. *)
          ( True,
            Infix ("-", Apply ("or", [], [ a; b ]), Apply ("and", [], [ a; b ]))
          ))
  | _ -> unknown at "the instruction %s" (Ir.opcode_name op)

let cast st at instr =
  let src = Llvm.operand instr 0 in
  let n = width src and m = width instr in
  let a = term st at src in
  match (Llvm.instr_opcode instr, st.mode) with
  | ZExt, Bv -> zext n m a
  | SExt, Bv -> sext n m a
  | Trunc, Bv -> extract (m - 1) 0 a
  (* On an unsigned representative: zext keeps it, sext adds 2^m - 2^n
     when the sign bit is set, trunc reduces it. *)
  | ZExt, Int (Wrap_unsigned | Wrap_all) -> a
  | SExt, Int (Wrap_unsigned | Wrap_all) ->
      Infix
        ( "+",
          a,
          Infix ("*", Infix ("/", a, pow2 (n - 1)), Const (sub_decimal (two_pow m) (two_pow n))) )
  | Trunc, Int (Wrap_unsigned | Wrap_all) -> Infix ("%", a, pow2 m)
  (* The other Int modes: the value is unchanged, except that a true i1
     sign-extends to -1. *)
  | SExt, Int _ when n = 1 -> Neg a
  | (ZExt | SExt | Trunc), Int _ -> a
  | op, _ -> unknown at "the instruction %s" (Ir.opcode_name op)

(* -- Memory ------------------------------------------------------------ *)

let index_width = 64

(* A position along one array dimension, in elements: a constant plus a sum
   of index-wide terms. *)
type index = { offset : int64; terms : expr list }

let const_index n = { offset = n; terms = [] }
let is_zero idx = idx.offset = 0L && idx.terms = []

let add_index a b =
  { offset = Int64.add a.offset b.offset; terms = a.terms @ b.terms }

let scale_index idx k =
  if k = 1L then idx
  else
    {
      offset = Int64.mul idx.offset k;
      terms = List.map (fun t -> Infix ("*", t, Const (Int64.to_string k))) idx.terms;
    }

let index_expr { offset; terms } =
  match terms with
  | [] -> Const (Int64.to_string offset)
  | t :: rest ->
      let sum = List.fold_left (fun acc t -> Infix ("+", acc, t)) t rest in
      if offset = 0L then sum
      else Infix ("+", sum, Const (Int64.to_string offset))

let describe_type ty =
  match (Llvm.classify_type ty, Llvm.struct_name ty) with
  | Struct, Some name when Ir.is_union ty -> Printf.sprintf "the union %s" name
  | Struct, Some name -> Printf.sprintf "the struct %s" name
  | _ -> Printf.sprintf "a value of type %s" (Llvm.string_of_lltype ty)

let object_of st at p =
  match Hashtbl.find_opt st.objects p with
  | Some o -> o
  | None ->
      let elem, count, name =
        match Llvm.classify_value p with
        | Instruction Alloca ->
            ( Ir.allocated_type p,
              Option.map Int64.to_int (Llvm.int64_of_const (Llvm.operand p 0)),
              Printf.sprintf "m%d" (fresh st) )
        | GlobalVariable -> (Ir.global_value_type p, Some 1, global_name p)
        | _ -> unknown at "an access through a pointer whose target is not tracked"
      in
      let comps =
        match Memory.components elem with
        | comps -> comps
        | exception Memory.Unsupported ty -> unknown at "%s in memory" (describe_type ty)
      in
      let outer = count <> Some 1 in
      let comps =
        List.map
          (fun (c : Memory.comp) ->
            let cname = String.concat "." (name :: List.map string_of_int c.path) in
            let carray = outer || c.dims <> [] in
            if carray then Hashtbl.replace st.arrays cname c.width
            else declare st cname c.width;
            { comp = c; cname; carray })
          comps
      in
      let o = { name; value = p; elem; count; comps } in
      Hashtbl.add st.objects p o;
      st.object_order <- o :: st.object_order;
      o

let component at o path =
  match List.find_opt (fun cv -> cv.comp.path = path) o.comps with
  | Some cv -> cv
  | None -> unknown at "an access to part of a value"

(* The position of a leaf in its component: the outer index (which of the
   [count] allocations), then one index per array on its path, missing
   inner ones being 0, combined row-major. *)
let linear cv levels =
  let dims = cv.comp.dims in
  let missing = 1 + List.length dims - List.length levels in
  match levels @ List.init missing (fun _ -> const_index 0L) with
  | outer :: inner ->
      List.fold_left2
        (fun acc d i -> add_index (scale_index acc (Int64.of_int d)) i)
        outer dims inner
  | [] -> assert false

(* The number of leaves a component has in the whole object, if constant. *)
let total o cv = Option.map (fun n -> n * Memory.count cv.comp) o.count

let read at cv idx =
  if cv.carray then Apply ("select_array", [], [ Var cv.cname; index_expr idx ])
  else (
    if not (is_zero idx) then unknown at "an access beyond the variable %s" cv.cname;
    Var cv.cname)

let write at cv idx value =
  if cv.carray then
    Assign (cv.cname, Apply ("store_array", [], [ Var cv.cname; index_expr idx; value ]))
  else (
    if not (is_zero idx) then unknown at "an access beyond the variable %s" cv.cname;
    Assign (cv.cname, value))

(* New, arbitrary contents for the whole object. *)
let havoc o = List.map (fun cv -> Assign (cv.cname, Nondet "nondet")) o.comps

(* Whether the passes give this object its arbitrary contents: an integer
   local variable gets them from the marker stored into it. *)
let marked o = Ir.is_integer o.elem && o.count = Some 1

(* -- Addresses as byte offsets -- *)

(* A byte offset into an object: a constant plus terms, each a GEP index
   (signed, index-wide) times its stride in bytes. *)
type bytes = { bc : int64; bterms : (expr * int64) list }

let as_index st at v =
  let n = width v in
  match st.mode with
  | Int _ -> signed_term st at v
  | Bv when n < index_width -> sext n index_width (term st at v)
  | Bv when n = index_width -> term st at v
  | Bv -> unknown at "an index wider than %d bits" index_width

let add_stride st at b v stride =
  match (Llvm.classify_value v, Llvm.int64_of_const v) with
  | ConstantInt, Some c -> { b with bc = Int64.add b.bc (Int64.mul c stride) }
  | _ -> { b with bterms = b.bterms @ [ (as_index st at v, stride) ] }

let gep_bytes st at gep b =
  let layout = st.layout in
  let n = Llvm.num_operands gep in
  let rec go i ty b =
    if i >= n then b
    else
      let v = Llvm.operand gep i in
      match Llvm.classify_type ty with
      | Struct -> (
          match Llvm.int64_of_const v with
          | Some f ->
              let f = Int64.to_int f in
              go (i + 1)
                (Ir.struct_element_types ty).(f)
                { b with bc = Int64.add b.bc (Memory.field_offset layout ty f) }
          | None -> unknown at "a variable struct field")
      | Array ->
          let e = Llvm.element_type ty in
          go (i + 1) e (add_stride st at b v (Memory.size layout e))
      | _ -> unknown at "a getelementptr into %s" (describe_type ty)
  in
  let source = Ir.gep_source_element_type gep in
  go 2 source (add_stride st at b (Llvm.operand gep 1) (Memory.size layout source))

(* The object an address points into, and the byte offset. *)
let rec address st at p =
  let through_gep () =
    let o, b = address st at (Llvm.operand p 0) in
    (o, gep_bytes st at p b)
  in
  match Llvm.classify_value p with
  | Instruction Alloca | GlobalVariable -> (object_of st at p, { bc = 0L; bterms = [] })
  | Instruction GetElementPtr -> through_gep ()
  | ConstantExpr when Llvm.constexpr_opcode p = GetElementPtr -> through_gep ()
  | _ -> unknown at "an access through a pointer whose target is not tracked"

(* -- From byte offsets back to leaves -- *)

(* A position inside a value of type [ty] in the object: the struct fields
   and array elements chosen so far, and the bytes left to place. *)
type cursor = {
  ty : Llvm.lltype;
  path : int list;
  levels : index list;
  bc : int64;
  bterms : (expr * int64) list;
}

let floor_div a b =
  let q = Int64.div a b in
  if Int64.rem a b < 0L then Int64.pred q else q

(* Selects an element of an array of [elem]: the terms whose stride is the
   element size or a multiple of it choose it, the others are left for the
   arrays inside (an index stays within its array, accesses out of bounds
   being UB). *)
let enter_element st at cur elem =
  let s = Memory.size st.layout elem in
  if s = 0L then unknown at "an access into a value of size 0";
  let mine, rest = List.partition (fun (_, k) -> k >= s) cur.bterms in
  let q = floor_div cur.bc s in
  let idx =
    List.fold_left
      (fun acc (e, k) ->
        if Int64.rem k s <> 0L then
          unknown at "an index whose stride is not a whole number of elements";
        add_index acc (scale_index { offset = 0L; terms = [ e ] } (Int64.div k s)))
      (const_index q) mine
  in
  { ty = elem; path = cur.path; levels = cur.levels @ [ idx ];
    bc = Int64.sub cur.bc (Int64.mul q s); bterms = rest }

let enter_field st cur =
  let fields = Ir.struct_element_types cur.ty in
  let rec find i =
    if i >= Array.length fields then None
    else
      let off = Memory.field_offset st.layout cur.ty i in
      if off <= cur.bc && cur.bc < Int64.add off (Memory.size st.layout fields.(i))
      then
        Some { cur with ty = fields.(i); path = cur.path @ [ i ]; bc = Int64.sub cur.bc off }
      else find (i + 1)
  in
  find 0

let outer_cursor st at o (b : bytes) =
  enter_element st at { ty = o.elem; path = []; levels = []; bc = b.bc; bterms = b.bterms } o.elem

(* The leaves an access of [w] bytes covers: component, index, bit
   position in the accessed value, width. *)
let pieces st at o (b : bytes) ~w =
  let fits c = Int64.add c.bc w <= Memory.size st.layout c.ty in
  let rec descend cur =
    match Llvm.classify_type cur.ty with
    | Array ->
        let c = enter_element st at cur (Llvm.element_type cur.ty) in
        if fits c then descend c else (c, true)
    | Struct -> (
        match enter_field st cur with
        | Some c when fits c -> descend c
        | _ -> (cur, false))
    | _ -> (cur, false)
  in
  let start = outer_cursor st at o b in
  let cur, span = if fits start then descend start else (start, true) in
  if cur.bterms <> [] then unknown at "an access at a position that is not a field";
  let s = Memory.size st.layout cur.ty in
  let lo = cur.bc and hi = Int64.add cur.bc w in
  let leaves j =
    let shift = Int64.mul (Int64.of_int j) s in
    match
      Memory.leaves_in st.layout cur.ty ~lo:(Int64.sub lo shift) ~hi:(Int64.sub hi shift)
    with
    | leaves -> List.map (fun l -> (j, l)) leaves
    | exception Memory.Partial -> unknown at "an access to part of an integer"
    | exception Memory.Unsupported ty -> unknown at "%s in memory" (describe_type ty)
  in
  let elements = if span then Int64.to_int (floor_div (Int64.pred hi) s) + 1 else 1 in
  List.concat_map
    (fun (j, (suffix, inner, off, bits)) ->
      let cv = component at o (cur.path @ suffix) in
      let levels =
        match List.rev cur.levels with
        | last :: before when span ->
            List.rev before @ [ add_index last (const_index (Int64.of_int j)) ]
        | _ -> cur.levels
      in
      let idx = linear cv (levels @ List.map const_index inner) in
      let pos = Int64.sub (Int64.add off (Int64.mul (Int64.of_int j) s)) lo in
      [ (cv, idx, 8 * Int64.to_int pos, bits) ])
    (List.concat (List.init elements leaves))

(* The value of the bits [lo, lo + width) of a value whose parts are
   [parts] (bit position, width, value); bits no part covers (padding) are
   arbitrary.  Assembling bits needs BV mode. *)
let compose st seg at ~lo ~width parts =
  let overlapping =
    List.filter_map
      (fun (bp, bits, e) ->
        let a = max lo bp and z = min (lo + width) (bp + bits) in
        if a >= z then None
        else
          let part = if a = bp && z = bp + bits then e else extract (z - bp - 1) (a - bp) e in
          Some (a - lo, z - a, part))
      parts
  in
  match overlapping with
  | [ (0, n, e) ] when n = width -> e
  | _ ->
      if is_int st then
        unknown at "an integer assembled from several fields or padding (Int mode)";
      let placed =
        List.map
          (fun (pos, n, e) ->
            let e = if n = width then e else zext n width e in
            if pos = 0 then e else shift "shl" e (Const (string_of_int pos)))
          overlapping
      in
      let covered = List.fold_left (fun acc (_, n, _) -> acc + n) 0 overlapping in
      let padding =
        if covered = width then []
        else (
          if width > 64 then unknown at "padding inside an i%d value" width;
          let gaps =
            List.fold_left
              (fun m (pos, n, _) -> Int64.logand m (Int64.lognot (Memory.bit_mask ~lo:pos ~n 64)))
              (Memory.bit_mask ~lo:0 ~n:width 64) overlapping
          in
          let gaps =
            if width < 64 && Int64.logand gaps (Int64.shift_left 1L (width - 1)) <> 0L then
              Int64.sub gaps (Int64.shift_left 1L width)
            else gaps
          in
          let t = temp st width in
          emit seg (Assign (t, Nondet "nondet"));
          [ Apply ("and", [], [ Var t; Const (Int64.to_string gaps) ]) ])
      in
      match placed @ padding with
      | [] -> assert false
      | e :: rest -> List.fold_left (fun acc e -> Apply ("or", [], [ acc; e ])) e rest

(* Whether every use of [v] is as the value a store writes. *)
let only_stored v =
  let ok = ref true in
  Llvm.iter_uses
    (fun use ->
      let user = Llvm.user use in
      match Llvm.classify_value user with
      | Instruction Store when Llvm.operand user 0 == v && Llvm.operand user 1 != v -> ()
      | _ -> ok := false)
    v;
  !ok

(* A load covering several fields whose value is only stored (a struct
   passed by value travels as one integer, struct { int x; int y; } as an
   i64) keeps its fields as parts, each copied into a temporary, and the
   store writes them back field by field: no bit operations, so this works
   in Int mode too.  Any other load covering several fields is assembled
   by bit operations. *)
let load st seg at instr =
  let o, b = address st at (Llvm.operand instr 0) in
  let ty = Llvm.type_of instr in
  let n = Llvm.integer_bitwidth ty in
  let ps = pieces st at o b ~w:(Memory.store_size st.layout ty) in
  match ps with
  | [ (cv, idx, 0, bits) ] when bits = n ->
      let v = var st instr in
      emit seg (Assign (v, read at cv idx));
      List.iter (emit seg) (representative st v n)
  | _ when only_stored instr ->
      Hashtbl.replace st.parts instr
        (List.map
           (fun (cv, idx, bp, bits) ->
             let t = temp st cv.comp.width in
             emit seg (Assign (t, read at cv idx));
             (bp, bits, Var t))
           ps)
  | _ ->
      let parts = List.map (fun (cv, idx, bp, bits) -> (bp, bits, read at cv idx)) ps in
      emit seg (Assign (var st instr, compose st seg at ~lo:0 ~width:n parts))

let store st seg at instr =
  let o, b = address st at (Llvm.operand instr 1) in
  let value = Llvm.operand instr 0 in
  let ty = Llvm.type_of value in
  let n = Llvm.integer_bitwidth ty in
  let ps = pieces st at o b ~w:(Memory.store_size st.layout ty) in
  match Hashtbl.find_opt st.parts value with
  | Some parts ->
      (* Bits of the destination that no part covers (the source's
         padding) are arbitrary. *)
      List.iter
        (fun (cv, idx, bp, bits) ->
          emit seg (write at cv idx (compose st seg at ~lo:bp ~width:bits parts)))
        ps
  | None -> (
  let v = term st at value in
  match ps with
  | [ (cv, idx, 0, bits) ] when bits = n -> emit seg (write at cv idx v)
  | ps ->
      if is_int st then
        unknown at "an integer stored across several fields (Int mode)";
      List.iter
        (fun (cv, idx, bp, bits) ->
          let bits' = min bits (n - bp) in
          if bits' < bits then unknown at "a store that covers part of a field";
          emit seg (write at cv idx (extract (bp + bits - 1) bp v)))
        ps)

(* -- Whole regions: memset, memcpy -- *)

(* A memset or memcpy length, [k * unit] bytes ([k] = 1 when [None]). *)
type length = { k : expr option; unit_bytes : int64 }

type count = Known of int | Variable of expr

let length st at len =
  let as_count v =
    let e = term st at v in
    match st.mode with
    | Bv when width v < index_width -> zext (width v) index_width e
    | _ -> e
  in
  let const v =
    match (Llvm.classify_value v, Llvm.int64_of_const v) with
    | ConstantInt, Some c -> Some c
    | _ -> None
  in
  match const len with
  | Some n -> { k = None; unit_bytes = n }
  | None -> (
      match Llvm.classify_value len with
      | Instruction Mul when const (Llvm.operand len 1) <> None ->
          { k = Some (as_count (Llvm.operand len 0)); unit_bytes = Option.get (const (Llvm.operand len 1)) }
      | Instruction Mul when const (Llvm.operand len 0) <> None ->
          { k = Some (as_count (Llvm.operand len 1)); unit_bytes = Option.get (const (Llvm.operand len 0)) }
      | Instruction Shl when const (Llvm.operand len 1) <> None ->
          { k = Some (as_count (Llvm.operand len 0));
            unit_bytes = Int64.shift_left 1L (Int64.to_int (Option.get (const (Llvm.operand len 1)))) }
      | _ -> { k = Some (as_count len); unit_bytes = 1L })

(* The values of type [ty] a region covers: [m] consecutive elements of the
   array whose element the cursor is at, or one value when [m] is 1. *)
let region st at o (b : bytes) len =
  let size = Memory.size st.layout in
  let count_of factor =
    match len.k with
    | None -> Known (Int64.to_int factor)
    | Some e -> Variable (if factor = 1L then e else Infix ("*", e, Const (Int64.to_string factor)))
  in
  let starts c = c.bterms = [] && c.bc = 0L in
  let rec element cur =
    let s = size cur.ty in
    if starts cur && Int64.rem len.unit_bytes s = 0L then
      Some (cur, count_of (Int64.div len.unit_bytes s))
    else inside cur
  and inside cur =
    match Llvm.classify_type cur.ty with
    | Array -> element (enter_element st at cur (Llvm.element_type cur.ty))
    | Struct -> (
        match enter_field st cur with
        | Some c when starts c && len.k = None && len.unit_bytes = size c.ty -> Some (c, Known 1)
        | Some c -> inside c
        | None -> None)
    | _ -> None
  in
  element (outer_cursor st at o b)

(* Per component of the region's type: the component, its first leaf and
   the number of leaves. *)
let region_components at o (cur, m) =
  List.map
    (fun (c : Memory.comp) ->
      let cv = component at o (cur.path @ c.path) in
      let n = Memory.count c in
      let cnt =
        match m with
        | Known k -> Known (k * n)
        | Variable e -> Variable (if n = 1 then e else Infix ("*", e, Const (string_of_int n)))
      in
      (cv, linear cv cur.levels, cnt))
    (Memory.components cur.ty)

let covers_whole o cv start cnt =
  cv.carray && is_zero start
  && match (cnt, total o cv) with Known k, Some n -> k = n | _ -> false

let unrolled_limit = 16

(* The commands [body j] for every j < count: written out for a small
   constant count, otherwise a loop in the LTS with a counter of its own. *)
let for_each_leaf st seg count body =
  match count with
  | Known k when k <= unrolled_limit ->
      for j = 0 to k - 1 do
        List.iter (emit seg) (body (const_index (Int64.of_int j)))
      done
  | _ ->
      let bound =
        match count with Known k -> Const (string_of_int k) | Variable e -> e
      in
      let c = temp st index_width in
      emit seg (Assign (c, Const "0"));
      let head = Printf.sprintf "%s_%d" seg.loc (fresh st) in
      finish st seg head;
      let less, not_less = match st.mode with Bv -> ("ult", "uge") | Int _ -> ("<", ">=") in
      st.transitions <-
        {
          src = head;
          commands =
            (Assume (Compare (less, Var c, bound)) :: body { offset = 0L; terms = [ Var c ] })
            @ [ Assign (c, Infix ("+", Var c, Const "1")) ];
          dst = head;
        }
        :: st.transitions;
      seg.loc <- head;
      seg.commands <- [ Assume (Compare (not_less, Var c, bound)) ]

let memset st seg at instr =
  let o, b = address st at (Llvm.operand instr 0) in
  let byte = Llvm.operand instr 1 in
  let len = length st at (Llvm.operand instr 2) in
  let value cv =
    let w = cv.comp.width in
    if w = 8 then term st at byte
    else
      match Llvm.int64_of_const byte with
      | Some v when Llvm.classify_value byte = ConstantInt ->
          if w mod 8 <> 0 || w > 64 then unknown at "a memset of i%d values" w;
          if is_int st && Int64.logand v 0xFFL <> 0L then
            unknown at "a memset of a nonzero byte to i%d values in Int mode" w;
          Const (Int64.to_string (Memory.repeated_byte v w))
      | _ -> unknown at "a memset of a variable byte to i%d values" w
  in
  match region st at o b len with
  | None -> unknown at "a memset that does not cover whole values"
  | Some r ->
      List.iter
        (fun (cv, start, cnt) ->
          let v = value cv in
          if covers_whole o cv start cnt then
            emit seg (Assign (cv.cname, Apply ("const_array", [], [ v ])))
          else for_each_leaf st seg cnt (fun j -> [ write at cv (add_index start j) v ]))
        (region_components at o r)

let shape st ty =
  ( Memory.size st.layout ty,
    List.map (fun (c : Memory.comp) -> (c.width, Memory.count c)) (Memory.components ty) )

(* memcpy and memmove alike.  Between values of the same shape, component
   by component; otherwise, for a constant length, bit by bit (BV mode).
   The source is read before anything is written, so that an overlapping
   copy within one object reads the old contents. *)
let memcpy st seg at instr =
  let od, bd = address st at (Llvm.operand instr 0) in
  let os, bs = address st at (Llvm.operand instr 1) in
  let len = length st at (Llvm.operand instr 2) in
  match (region st at od bd len, region st at os bs len) with
  | Some ((cd, md) as rd), Some ((cs, ms) as rs) when shape st cd.ty = shape st cs.ty && md = ms ->
      List.iter2
        (fun (dv, dstart, cnt) (sv, sstart, _) ->
          if covers_whole od dv dstart cnt && covers_whole os sv sstart cnt then
            emit seg (Assign (dv.cname, Var sv.cname))
          else
            let sv =
              if od.value == os.value && sv.carray then (
                let copy = Printf.sprintf "t%d" (fresh st) in
                Hashtbl.replace st.arrays copy sv.comp.width;
                emit seg (Assign (copy, Var sv.cname));
                { sv with cname = copy })
              else sv
            in
            for_each_leaf st seg cnt (fun j ->
                [ write at dv (add_index dstart j) (read at sv (add_index sstart j)) ]))
        (region_components at od rd) (region_components at os rs)
  | _ -> (
      match len.k with
      | Some _ -> unknown at "a copy of a variable length between values of different types"
      | None ->
          let w = len.unit_bytes in
          let src =
            List.map
              (fun (cv, idx, bp, bits) ->
                let t = temp st cv.comp.width in
                emit seg (Assign (t, read at cv idx));
                (bp, bits, Var t))
              (pieces st at os bs ~w)
          in
          List.iter
            (fun (cv, idx, bp, bits) ->
              emit seg (write at cv idx (compose st seg at ~lo:bp ~width:bits src)))
            (pieces st at od bd ~w))

(* The size in bytes of the object an alloca makes, when constant. *)
let alloca_bytes st a =
  match Llvm.int64_of_const (Llvm.operand a 0) with
  | Some n -> Some (Int64.mul n (Memory.size st.layout (Ir.allocated_type a)))
  | None -> None

(* llvm.lifetime.start/end on a whole local variable of constant size, the
   form the inliner writes for the callee's variables. *)
let lifetime st seg at instr ~start =
  let size = Llvm.int64_of_const (Llvm.operand instr 0) in
  let p = Llvm.operand instr 1 in
  match Llvm.classify_value p with
  | Instruction Alloca when size <> None && size = alloca_bytes st p ->
      if start && Llvm.use_begin p <> None then
        List.iter (emit seg) (havoc (object_of st at p))
  | _ -> unknown at "a lifetime marker other than on a whole local variable"

(* A local array or struct gets arbitrary contents where it is declared, so
   that one declared in a loop is fresh on every iteration.  An integer
   variable gets its value there from the marker the passes store.  A
   parameter is declared after the argument is copied into it (a struct
   passed by value), so its declaration changes nothing. *)
let declare_local st seg at declare slot =
  match Llvm.classify_value slot with
  | Instruction Alloca when Llvm.use_begin slot <> None && Ir.declared_arg declare = 0 ->
      let o = object_of st at slot in
      if not (marked o) then List.iter (emit seg) (havoc o)
  | _ -> ()

(* -- Calls ------------------------------------------------------------ *)

(* The T2 nondet of a __VERIFIER_nondet_T in Int mode, which needs the
   range of T: its width and whether it is signed. *)
let sized_nondet at name n =
  let suffix =
    String.sub name 18 (String.length name - 18)
    (* after "__VERIFIER_nondet_" *)
  in
  let signed =
    match suffix with
    | "char" | "schar" | "short" | "int" | "long" | "longlong" | "s8" | "s16"
    | "s32" | "s64" ->
        Some true
    | "uchar" | "ushort" | "uint" | "unsigned" | "ulong" | "ulonglong" | "u8"
    | "u16" | "u32" | "u64" | "size_t" ->
        Some false
    | _ -> None
  in
  match (signed, n) with
  | Some s, 8 -> if s then "nondet_char" else "nondet_uchar"
  | Some s, 16 -> if s then "nondet_short" else "nondet_ushort"
  | Some s, 32 -> if s then "nondet_int" else "nondet_uint"
  | Some s, 64 -> if s then "nondet_long" else "nondet_ulong"
  | _ -> unknown at "%s: its range is not known in Int mode" name

let is_bool_nondet name =
  match name with
  | "__VERIFIER_nondet_bool" | "__VERIFIER_nondet__Bool" -> true
  | _ -> false

(* The absolute value of [instr]'s first operand, assigned to [instr].
   With [poison_at_min] the minimum value, the one nonzero value equal to
   its own negation (in the wrapping Int modes, the representative
   2^(n-1)), gives poison, so an execution reaching it stops.  Plain and
   Bitwise assume no value leaves its range, so need no test. *)
let absolute st seg at instr ~poison_at_min =
  let a = term st at (Llvm.operand instr 0) in
  let v = var st instr in
  let n = width instr in
  (if poison_at_min then
     match st.mode with
     | Bv ->
         emit seg
           (Assume (Or (Compare ("==", a, Const "0"), Compare ("!=", a, Neg a))))
     | Int (Wrap_unsigned | Wrap_all) ->
         emit seg (Assume (Compare ("!=", a, pow2 (n - 1))))
     | Int _ -> ());
  let negative = Compare ("<", signed_term st at (Llvm.operand instr 0), Const "0") in
  (* The representative of -x for a negative x is 2^n - x. *)
  let minus = if wraps st then Infix ("-", pow2 n, a) else Neg a in
  branch st seg
    [ (negative, [ Assign (v, minus) ]); (Not negative, [ Assign (v, a) ]) ]

(* The n-bit value [x] with its bytes reversed, read as unsigned, written
   with division and remainder by powers of 256: byte k of the unsigned
   value u, (u / 256^k) mod 256, moves to byte n/8 - 1 - k.  u is x itself
   where values are unsigned representatives or bit-vectors (BV's udiv and
   urem read it unsigned), and x reduced modulo 2^n in Plain and Bitwise,
   where an n-bit value may be negative.  The result is in [0, 2^n), which
   every mode holds as the unsigned n-bit value. *)
let byte_swap st seg x n =
  let div, rem = if st.mode = Bv then ("udiv", "urem") else ("/", "%") in
  let u = temp st n in
  emit seg
    (Assign (u, match st.mode with Int (Plain | Bitwise) -> mod2 ~nonneg:false x n | _ -> x));
  let bytes = n / 8 in
  let power k = Const (two_pow (8 * k)) in
  let byte k =
    let shifted = if k = 0 then Var u else Infix (div, Var u, power k) in
    let b = if k = bytes - 1 then shifted else Infix (rem, shifted, Const "256") in
    let target = bytes - 1 - k in
    if target = 0 then b else Infix ("*", b, power target)
  in
  let terms = List.init bytes byte in
  List.fold_left (fun acc t -> Infix ("+", acc, t)) (List.hd terms) (List.tl terms)

let intrinsic st seg at instr fn =
  let name = Llvm.value_name fn in
  let prefix p = String.starts_with ~prefix:p name in
  if prefix "llvm.dbg.declare" then
    match Ir.declared_slot instr with
    | Some slot -> declare_local st seg at instr slot
    | None -> ()
  else if
    prefix "llvm.dbg." || prefix "llvm.stacksave" || prefix "llvm.stackrestore"
    (* declares alias scopes for !noalias metadata: nothing at run time *)
    || prefix "llvm.experimental.noalias.scope.decl"
  then ()
  else if prefix "llvm.lifetime.start." then lifetime st seg at instr ~start:true
  else if prefix "llvm.lifetime.end." then lifetime st seg at instr ~start:false
  else if prefix "llvm.memset." then memset st seg at instr
  else if prefix "llvm.memcpy." || prefix "llvm.memmove." then memcpy st seg at instr
  else if prefix "llvm.abs." then
    absolute st seg at instr
      ~poison_at_min:(Llvm.int64_of_const (Llvm.operand instr 1) <> Some 0L)
  else if List.exists prefix
            [ "llvm.sadd.with.overflow."; "llvm.uadd.with.overflow.";
              "llvm.ssub.with.overflow."; "llvm.usub.with.overflow.";
              "llvm.smul.with.overflow."; "llvm.umul.with.overflow." ]
  then (
    if not (wraps st) then int_mode_only_arith st at "an overflow-checking intrinsic";
    let a = term st at (Llvm.operand instr 0) in
    let b = term st at (Llvm.operand instr 1) in
    let n = width (Llvm.operand instr 0) in
    let op = String.sub name 5 4 (* "sadd", "umul", ...: after "llvm." *) in
    let arith_op = match String.sub op 1 3 with "add" -> "+" | "sub" -> "-" | _ -> "*" in
    let no_overflow =
      if wraps st then
        (* The exact result, signed or unsigned, within the type's range. *)
        if op.[0] = 's' then
          in_signed_range n
            (Infix
               ( arith_op,
                 signed_term st at (Llvm.operand instr 0),
                 signed_term st at (Llvm.operand instr 1) ))
        else
          let r = Infix (arith_op, a, b) in
          And (Compare (">=", r, Const "0"), Compare ("<", r, pow2 n))
      else
        match op with
        | "sadd" | "ssub" -> no_signed_overflow n arith_op a b
        | "uadd" | "usub" -> no_unsigned_overflow n arith_op a b
        | "smul" -> no_signed_mul_overflow n a b
        | _ -> no_unsigned_mul_overflow n a b
    in
    let wrapped =
      if not (wraps st) then Infix (arith_op, a, b)
      else
        let r = Infix (arith_op, a, b) in
        let r = if arith_op = "-" then Infix ("+", r, pow2 n) else r in
        Infix ("%", r, pow2 n)
    in
    let value = Printf.sprintf "p%d" (fresh st) in
    let flag = Printf.sprintf "p%d" (fresh st) in
    declare st value n;
    declare st flag 1;
    Hashtbl.replace st.pairs instr (value, flag);
    emit seg (Assign (value, wrapped));
    branch st seg
      [ (no_overflow, [ Assign (flag, Const "0") ]); (Not no_overflow, [ Assign (flag, Const "1") ]) ])
  else if List.exists prefix [ "llvm.ctpop."; "llvm.ctlz."; "llvm.cttz."; "llvm.bswap." ]
  then (
    int_mode_only_arith st at "a bit-manipulation intrinsic";
    let x = term st at (Llvm.operand instr 0) in
    let n = width instr in
    let v = var st instr in
    (* The value after each step is kept in a temporary, so that no
       expression repeats a growing one. *)
    let step e =
      let t = temp st n in
      emit seg (Assign (t, e));
      Var t
    in
    let bit_count e =
      if n = 1 then e
      else
        let bits = List.init n (fun i -> zext 1 n (extract i i e)) in
        List.fold_left (fun acc b -> Infix ("+", acc, b)) (List.hd bits) (List.tl bits)
    in
    (* Every bit below the highest set bit (lshr), or above the lowest
       (shl), set too. *)
    let smear dir e =
      let rec go k e =
        if k >= n then e
        else go (2 * k) (step (Apply ("or", [], [ e; shift dir e (Const (string_of_int k)) ])))
      in
      go 1 e
    in
    (* With the flag true, a zero argument gives poison. *)
    let zero_is_poison () =
      match Llvm.int64_of_const (Llvm.operand instr 1) with
      | Some 0L -> ()
      | _ -> emit seg (Assume (Compare ("!=", x, Const "0")))
    in
    let value =
      if prefix "llvm.ctpop." then bit_count x
      else if prefix "llvm.ctlz." || prefix "llvm.cttz." then (
        zero_is_poison ();
        let s = smear (if prefix "llvm.ctlz." then "lshr" else "shl") x in
        Infix ("-", Const (string_of_int n), bit_count s))
      else (
        if n mod 16 <> 0 then unknown at "%s on i%d" name n;
        let bytes =
          List.init (n / 8) (fun k ->
              let b = zext 8 n (extract ((8 * k) + 7) (8 * k) x) in
              let to_ = n - 8 - (8 * k) in
              if to_ = 0 then b else shift "shl" b (Const (string_of_int to_)))
        in
        List.fold_left (fun acc b -> Apply ("or", [], [ acc; b ])) (List.hd bytes) (List.tl bytes))
    in
    emit seg (Assign (v, value)))
  else unknown at "the intrinsic %s is not translated yet" name

(* A widening of a comparison evaluated in place (see [used_in_place]): it
   is read only by cuts, which take the comparison itself. *)
let widened_in_place st v =
  match Llvm.classify_value v with
  | Instruction ZExt -> (
      let c = Llvm.operand v 0 in
      match Llvm.classify_value c with
      | Instruction ICmp when Hashtbl.mem st.in_place c -> Some c
      | _ -> None)
  | _ -> None

(* Returns false when the call ends the execution path. *)
let call st property seg instr =
  let at = instr in
  match Scope.classify_callee instr with
  | Intrinsic fn ->
      intrinsic st seg at instr fn;
      true
  | Defined fn ->
      unknown at "a call to %s left after inlining" (Llvm.value_name fn)
  | Modelled (kind, fn) -> (
      let name = Llvm.value_name fn in
      match kind with
      | Nondet ->
          let v = var st instr in
          let n = width instr in
          (match st.mode with
          | Bv | Int (Wrap_unsigned | Wrap_all) -> emit seg (Assign (v, Nondet "nondet"))
          | Int _ when st.unbounded_nondet || is_bool_nondet name || n = 1 ->
              emit seg (Assign (v, Nondet "nondet"))
          | Int _ -> emit seg (Assign (v, Nondet (sized_nondet at name n))));
          if is_bool_nondet name && n > 1 then
            emit seg
              (Assume
                 (And
                    ( Compare (">=", Var v, Const "0"),
                      Compare ("<=", Var v, Const "1") )))
          else if is_int st && n = 1 then
            emit seg
              (Assume
                 (And
                    ( Compare (">=", Var v, Const "0"),
                      Compare ("<=", Var v, Const "1") )))
          else List.iter (emit seg) (representative st v n);
          true
      | Uninit_marker ->
          let v = var st instr in
          emit seg (Assign (v, Nondet "nondet"));
          if is_int st && width instr = 1 then
            emit seg
              (Assume
                 (And
                    ( Compare (">=", Var v, Const "0"),
                      Compare ("<=", Var v, Const "1") )))
          else List.iter (emit seg) (representative st v (width instr));
          true
      | Assume -> (
          let holds = Compare ("!=", term st at (Llvm.operand instr 0), Const "0") in
          match property with
          | Unreach_call ->
              emit seg (Assume holds);
              true
          | Termination ->
              st.diverges <- true;
              st.transitions <-
                {
                  src = seg.loc;
                  commands = List.rev seg.commands @ [ Assume (Not holds) ];
                  dst = diverge_location;
                }
                :: st.transitions;
              emit seg (Assume holds);
              true)
      | Cut ->
          (* Ending the execution and having no next step are the same for
             both properties: neither reaches the error location, and both
             make the execution finite. As a guard the condition is a
             premise of the transition, where a move to the end location
             would be a branch of its own. *)
          let arg = Llvm.operand instr 0 in
          let holds =
            match widened_in_place st arg with
            | Some c -> icmp_cond st at c
            | None -> Compare ("!=", term st at arg, Const "0")
          in
          emit seg (Assume holds);
          true
      | Reach_error -> (
          match property with
          | Unreach_call ->
              finish st seg error_location;
              false
          | Termination ->
              finish st seg end_location;
              false)
      | Program_end ->
          finish st seg end_location;
          false
      | Region_arbitrary array ->
          (* Ptr2Arr's region arrays are C globals, which start at 0, but
             they stand for heap and local objects whose contents are
             indeterminate.  Ptr2Arr calls this at the head of main, before
             it writes the static objects, and only for those arrays. *)
          (match Llvm.lookup_global array (Llvm.global_parent fn) with
          | Some g -> List.iter (emit seg) (havoc (object_of st at g))
          | None -> unknown at "%s names no global array" name);
          true
      | Wrap (signed, n, nonneg) ->
          (* The call converts its argument to the n-bit type, so in BV
             mode, and in the wrapping Int modes whose trunc reduces, the
             argument already holds the C value and the function is the
             identity.  In Plain and Bitwise that conversion is not made
             (a trunc is the identity there), and the result is the
             argument reduced into the type's range modulo 2^n: the name is
             the only place the signedness is written, since a trunc has
             none.  T2's [%] rounds towards zero, so the remainder is made
             non-negative before the signed shift; an argument Ptr2Arr
             has shown non-negative needs only the one remainder. *)
          let v = var st instr in
          let e = term st at (Llvm.operand instr 0) in
          let m = Const (two_pow n) in
          let reduce x = Infix ("%", Infix ("+", Infix ("%", x, m), m), m) in
          let value =
            match st.mode with
            | Bv | Int (Wrap_unsigned | Wrap_all) -> e
            | Int _ when signed ->
                let h = Const (two_pow (n - 1)) in
                Infix ("-", reduce (Infix ("+", e, h)), h)
            | Int _ when nonneg -> Infix ("%", e, m)
            | Int _ -> reduce e
          in
          emit seg (Assign (v, value));
          true
      | Rand ->
          (* glibc's RAND_MAX, 2^31 - 1: a value every Int reading and BV
             mode hold as itself *)
          let v = var st instr in
          emit seg (Assign (v, Nondet "nondet"));
          emit seg
            (Assume
               (And
                  ( Compare (">=", Var v, Const "0"),
                    Compare ("<=", Var v, Const "2147483647") )));
          true
      | Time ->
          if Llvm.use_begin instr <> None then (
            let v = var st instr in
            emit seg (Assign (v, Nondet "nondet"));
            List.iter (emit seg) (representative st v (width instr)));
          true
      | No_effect -> true
      | Descriptor | Status ->
          (* Read as signed: -1 is the failure value. *)
          if Llvm.use_begin instr <> None then (
            let v = var st instr in
            let n = width instr in
            emit seg (Assign (v, Nondet "nondet"));
            List.iter (emit seg) (representative st v n);
            let s = if wraps st then to_signed n (Var v) else Var v in
            emit seg
              (Assume
                 (match kind with
                 | Descriptor -> Compare (">=", s, Const "-1")
                 | _ -> Or (Compare ("==", s, Const "0"), Compare ("==", s, Const "-1")))));
          true
      | Byte_swap n ->
          if Llvm.use_begin instr <> None then (
            let x = term st at (Llvm.operand instr 0) in
            let v = var st instr in
            emit seg (Assign (v, byte_swap st seg x n)));
          true
      | Inet_addr ->
          (if Llvm.use_begin instr <> None then
             match Scope.inet_addr_value instr with
             | Some a ->
                 (* in_addr_t is unsigned; BV literals are written signed,
                    as constants are read there *)
                 let a =
                   if st.mode = Bv && a >= 0x8000_0000L then Int64.sub a 0x1_0000_0000L
                   else a
                 in
                 emit seg (Assign (var st instr, Const (Int64.to_string a)))
             | None -> unknown at "%s of anything but a constant decimal dotted quad" name);
          true
      | Imaxabs ->
          absolute st seg at instr ~poison_at_min:true;
          true
      | Output ->
          (* printf, puts and putchar change no variable of the program
             (Ptr2Arr passes them no pointer but string literals) and
             return a count or a character, here any value.  A
             counterexample that relies on that value can be spurious. *)
          if Llvm.use_begin instr <> None then (
            let v = var st instr in
            emit seg (Assign (v, Nondet "nondet"));
            List.iter (emit seg) (representative st v (width instr)));
          true)

(* -- Blocks ----------------------------------------------------------- *)

(* The assignments of the phis of [target] on the edge from [source], made
   simultaneously: through temporaries when one phi reads another. *)
let phi_assignments st at ~source target =
  let phis =
    Llvm.fold_left_instrs
      (fun acc i -> if Llvm.instr_opcode i = PHI then i :: acc else acc)
      [] target
    |> List.rev
  in
  let incoming phi =
    match List.find_opt (fun (_, b) -> b == source) (Llvm.incoming phi) with
    | Some (v, _) -> v
    | None -> unknown at "a phi without a value for this edge"
  in
  let pairs = List.map (fun phi -> (phi, incoming phi)) phis in
  let reads_a_phi =
    List.exists (fun (_, v) -> List.exists (fun (p, _) -> p == v) pairs) pairs
  in
  if not reads_a_phi then
    List.map (fun (phi, v) -> Assign (var st phi, term st at v)) pairs
  else
    let temps = List.map (fun (phi, v) -> (phi, temp st (width phi), v)) pairs in
    List.map (fun (_, t, v) -> Assign (t, term st at v)) temps
    @ List.map (fun (phi, t, _) -> Assign (var st phi, Var t)) temps

let in_block block v =
  (match Llvm.classify_value v with Instruction _ -> true | _ -> false)
  && Llvm.instr_parent v == block

(* Whether [v] is used, and every use is the argument of a call of
   Ptr2Arr's cut (__ptr2arr_assume) in [block]. *)
let feeds_only_cuts block v =
  let ok = ref (Llvm.use_begin v <> None) in
  Llvm.iter_uses
    (fun use ->
      let user = Llvm.user use in
      match Llvm.classify_value user with
      | Instruction Call
        when in_block block user
             && Llvm.operand user 0 == v
             && Scope.modelled_of_name (Llvm.value_name (Ir.callee user))
                = Some Scope.Cut -> ()
      | _ -> ok := false)
    v;
  !ok

(* Whether a comparison's result is used only as the condition of its own
   block's terminator or of a select in its block, or, widened to an
   integer, only as the argument of cuts in its block (a cut reads its
   argument as a condition, see [call]). *)
let used_in_place icmp =
  let block = Llvm.instr_parent icmp in
  let ok = ref true in
  Llvm.iter_uses
    (fun use ->
      let user = Llvm.user use in
      let same = in_block block user in
      match Llvm.classify_value user with
      | Instruction Br when same -> ()
      | Instruction Select when same && Llvm.operand user 0 == icmp -> ()
      | Instruction ZExt when same && feeds_only_cuts block user -> ()
      | _ -> ok := false)
    icmp;
  !ok

let translate_block st property block =
  let seg = { loc = block_location st block; commands = [] } in
  let alive = ref true in
  Llvm.iter_instrs
    (fun instr ->
      if !alive then
        let at = instr in
        match Llvm.instr_opcode instr with
        | PHI -> ()
        | Add | Sub | Mul | UDiv | SDiv | URem | SRem | Shl | LShr | AShr
        | And | Or | Xor ->
            let guard, value = arith st at instr in
            if guard <> True then emit seg (Assume guard);
            emit seg (Assign (var st instr, value))
        | ZExt when widened_in_place st instr <> None -> ()
        | ZExt | SExt | Trunc -> emit seg (Assign (var st instr, cast st at instr))
        | ICmp ->
            if used_in_place instr then Hashtbl.replace st.in_place instr ()
            else
              let c = icmp_cond st at instr in
              let v = var st instr in
              branch st seg
                [ (c, [ Assign (v, Const "1") ]); (Not c, [ Assign (v, Const "0") ]) ]
        | Select ->
            let c = truth st at (Llvm.operand instr 0) in
            let v = var st instr in
            let a = term st at (Llvm.operand instr 1) in
            let b = term st at (Llvm.operand instr 2) in
            branch st seg [ (c, [ Assign (v, a) ]); (Not c, [ Assign (v, b) ]) ]
        | Call -> if not (call st property seg instr) then alive := false
        | ExtractValue -> (
            match Hashtbl.find_opt st.pairs (Llvm.operand instr 0) with
            | Some (value, flag) ->
                let field = if Ir.indices instr = [| 0 |] then value else flag in
                emit seg (Assign (var st instr, Var field))
            | None -> unknown at "an extractvalue")
        | Load -> load st seg at instr
        | Store -> store st seg at instr
        (* An array or struct gets arbitrary contents where it is
           allocated, for the paths that bypass its declaration; a
           variable-length one each time its allocation runs. *)
        | Alloca ->
            if Llvm.use_begin instr <> None then
              let o = object_of st at instr in
              if not (marked o) then List.iter (emit seg) (havoc o)
        (* An address is read where a load or store uses it. *)
        | GetElementPtr -> ()
        | Ret ->
            finish st seg end_location;
            alive := false
        | Unreachable -> alive := false
        | Br -> (
            alive := false;
            match Llvm.get_branch instr with
            | Some (`Unconditional target) ->
                finish st seg
                  ~extra:(phi_assignments st at ~source:block target)
                  (block_location st target)
            | Some (`Conditional (c, t, f)) ->
                let c = truth st at c in
                List.iter
                  (fun (guard, target) ->
                    st.transitions <-
                      {
                        src = seg.loc;
                        commands =
                          List.rev seg.commands
                          @ (Assume guard :: phi_assignments st at ~source:block target);
                        dst = block_location st target;
                      }
                      :: st.transitions)
                  [ (c, t); (Not c, f) ]
            | None -> unknown at "a branch")
        | Switch ->
            alive := false;
            let x = term st at (Llvm.operand instr 0) in
            let cases =
              List.init
                ((Llvm.num_operands instr - 2) / 2)
                (fun i ->
                  ( term st at (Llvm.operand instr (2 + (2 * i))),
                    Llvm.block_of_value (Llvm.operand instr (3 + (2 * i))) ))
            in
            let default = Llvm.block_of_value (Llvm.operand instr 1) in
            let goto guard target =
              st.transitions <-
                {
                  src = seg.loc;
                  commands =
                    List.rev seg.commands
                    @ (Assume guard :: phi_assignments st at ~source:block target);
                  dst = block_location st target;
                }
                :: st.transitions
            in
            List.iter (fun (c, target) -> goto (Compare ("==", x, c)) target) cases;
            goto
              (List.fold_left
                 (fun acc (c, _) -> conj acc (Compare ("!=", x, c)))
                 True cases)
              default
        | op -> unknown at "the instruction %s" (Ir.opcode_name op))
    block

(* What the start transition does to the objects: a global variable gets
   its initial value; in BV mode, every array is read once into variables
   of its index and element widths, which fixes its type for T2's type
   inference (an array variable has no TYPE line). *)
let initial_commands st =
  let constant at c =
    match constant_value ~unsigned:(wraps st) c with
    | Some s -> Const s
    | None ->
        Outcome.stop
          (Unknown
             (Printf.sprintf "the initial value of %s cannot be read"
                (Llvm.value_name at)))
  in
  let init o =
    match (Llvm.classify_value o.value, Llvm.global_initializer o.value) with
    | GlobalVariable, Some c -> (
        match Memory.nonzero_leaves c with
        | Ok leaves ->
            List.concat_map
              (fun cv ->
                let mine = List.filter (fun (p, _, _) -> p = cv.comp.path) leaves in
                if cv.carray then
                  Assign (cv.cname, Apply ("const_array", [], [ Const "0" ]))
                  :: List.map
                       (fun (_, idx, v) ->
                         let i = linear cv (List.map const_index (0L :: List.map Int64.of_int idx)) in
                         Assign
                           ( cv.cname,
                             Apply ("store_array", [], [ Var cv.cname; index_expr i; constant o.value v ]) ))
                       mine
                else
                  [ Assign (cv.cname, match mine with [ (_, _, v) ] -> constant o.value v | _ -> Const "0") ])
              o.comps
        | Error _ ->
            Outcome.stop
              (Unknown
                 (Printf.sprintf "the initial value of %s is not made of integers"
                    (Llvm.value_name o.value))))
    | _ -> []
  in
  let pin cv =
    if st.mode = Bv && cv.carray then (
      let x = temp st cv.comp.width in
      declare st "ix" index_width;
      [ Assign (x, Apply ("select_array", [], [ Var cv.cname; Var "ix" ])) ])
    else []
  in
  let objects = List.rev st.object_order in
  List.concat_map init objects
  @ List.concat_map (fun o -> List.concat_map pin o.comps) objects

let translate ~mode ~property ?(unbounded_nondet = false) llmodule =
  let main = Scope.main_function llmodule in
  let st =
    {
      mode;
      unbounded_nondet;
      ids = Hashtbl.create 64;
      blocks = Hashtbl.create 32;
      widths = Hashtbl.create 64;
      next_id = 0;
      transitions = [];
      in_place = Hashtbl.create 16;
      pairs = Hashtbl.create 4;
      diverges = false;
      layout = Llvm_target.DataLayout.of_string (Llvm.data_layout llmodule);
      parts = Hashtbl.create 8;
      objects = Hashtbl.create 16;
      arrays = Hashtbl.create 16;
      object_order = [];
    }
  in
  let entry = block_location st (Llvm.entry_block main) in
  Llvm.iter_blocks (translate_block st property) main;
  st.transitions <-
    st.transitions @ [ { src = "start"; commands = initial_commands st; dst = entry } ];
  if st.diverges then
    st.transitions <-
      { src = diverge_location; commands = []; dst = diverge_location }
      :: st.transitions;
  {
    start = "start";
    error =
      (match property with
      | Unreach_call -> Some error_location
      | Termination -> None);
    widths =
      List.sort compare (Hashtbl.fold (fun x n acc -> (x, n) :: acc) st.widths []);
    arrays =
      List.sort compare (Hashtbl.fold (fun x n acc -> (x, n) :: acc) st.arrays []);
    transitions = List.rev st.transitions;
  }
