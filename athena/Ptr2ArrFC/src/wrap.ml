(* Fixed-width integers made explicit, for a consumer that reads integers as
   mathematical integers (--wrap-integers).

   The output then has two readings. Read as C, [__p2a_wrap_k(e)] is a
   function whose parameter has the integer type k and whose body returns it,
   so the conversion of the call does what C does and nothing changes. Read
   with every integer variable and operation mathematical and every cast
   between integer types the identity, [__p2a_wrap_k] is red_k, the reduction
   into the range of k modulo 2^w, and the two readings agree on every integer
   value, because:

   - the ring operations (+, binary and unary -, *, and << as a product by a
     power of two) commute with the reduction, so a ring expression over
     in-range leaves has, reduced, its C value;
   - every place where the exact value of an expression is observed (a store,
     a comparison, a division, a shift count, a bitwise operation, a
     condition, an index, the integer operand of pointer arithmetic) gets its
     ring expression reduced first, if its type is unsigned;
   - a signed ring expression is not reduced: under the assumption that the
     execution has no undefined behaviour it does not overflow, so its C value
     is its mathematical value;
   - with [All] (--wrap-integers-kind all) signed overflow wraps instead, as
     gcc -fwrapv defines it: a maximal signed ring expression is computed in
     the unsigned type of the same width (its leaves converted to it, which
     the mathematical reading takes as the identity) and reduced to the
     signed type where it is used. The output stays defined C without
     -fwrapv, since unsigned arithmetic wraps and gcc defines a conversion to
     a signed type as the reduction modulo 2^w; read mathematically, the
     unsigned expression has the exact value, congruent to the -fwrapv value
     modulo 2^w, and the reduction gives that value. Division, remainder
     and right shift stay signed: gcc -fwrapv still traps on INT_MIN / -1,
     which stays excluded;
   - a conversion that narrows or changes signedness is a reduction to the
     target type, and a widening one is kept (its operand is reduced first);
   - the result of an external function is reduced when it is received, since
     a mathematical reading would let it return any integer.

   So every integer location holds an in-range value in both readings, and
   each observation sees the same value.

   With a scan (--integers=auto), a reduction is left out where the scan
   gives the expression's exact value an interval inside the target type's
   range: it would change nothing, in C or read mathematically. A reduction
   of an unsigned type whose argument the scan shows non-negative is written
   __p2a_wrapnn_k, the same identity in C, which a consumer may read with one
   remainder instead of the two a possibly negative argument needs. The
   result of a __VERIFIER_nondet_ function is not reduced: the consumers this
   serves confine it to its type's range themselves. An operand the scan
   found to have one value, where a bitwise operation is writable only with
   a constant there, is replaced by that constant. The environment variable
   P2A_WRAP_NO_ELIDE=1 keeps every reduction (for tests: the outputs with and
   without the omissions must behave alike).

   Contract: [run st] rewrites the current project in place; it must run
   before the pointer-replacing transformation, which then sees the
   reductions as calls with integer arguments and may ask for more of them
   ([fn st k]); [finish st] then adds the definitions of all the reduction
   functions used. [created st] lists the variables made (functions,
   parameters, temporaries). *)

open Cil_types

type kind = int * bool  (** width in bits, signed *)

let kind_of_ikind = function
  | IBool -> None
  | ik -> Some (Cil.bitsSizeOfInt ik, Cil.isSigned ik)

let kind_of_type t =
  match Ast_types.unroll_node t with
  | TInt ik -> kind_of_ikind ik
  | TEnum ei -> kind_of_ikind ei.ekind
  | _ -> None

(* The C type of an integer kind. 64 bits is long under LP64 and long long
   under ILP32, where long is 32 bits wide: the machine description decides. *)
let c_type = function
  | 8, false -> Cil_const.ucharType
  | 8, true -> Cil_const.scharType
  | 16, false -> Cil_const.ushortType
  | 16, true -> Cil_const.shortType
  | 32, false -> Cil_const.uintType
  | 32, true -> Cil_const.intType
  | 64, false when Cil.bitsSizeOfInt IULong = 64 -> Cil_const.ulongType
  | 64, true when Cil.bitsSizeOfInt ILong = 64 -> Cil_const.longType
  | 64, false -> Cil_const.ulongLongType
  | 64, true -> Cil_const.longLongType
  | w, _ -> raise (Transform.Not_implemented (Printf.sprintf "a %d-bit integer" w))

(* Does the range of [k'] contain the range of [k]? *)
let contains (w', s') (w, s) = (s' = s && w' >= w) || (s' && (not s) && w' > w)

(* Which overflow wraps: the unsigned operations only, a signed one assumed
   not to overflow; or the signed +, - and * too. *)
type mode = Unsigned | All

type st = {
  all : bool;  (** signed ring operations wrap too *)
  scan : IntScan.t option;
  elide : bool;  (** the scan's intervals and the nondet results are used *)
  fns : (kind * bool, fundec) Hashtbl.t;  (** with whether it is __p2a_wrapnn_ *)
  mutable created : varinfo list;
  mutable pending : instr list;  (** reversed *)
  mutable cur : fundec option;
}

let loc0 = Fileloc.unknown
let mk ?(loc = loc0) node = Cil.new_exp ~loc node

(* __p2a_wrap_k: the identity at type k, read as red_k; __p2a_wrapnn_k, the
   same for an argument known non-negative (unsigned k only). *)
let wrap_fn ?(nn = false) st ((w, s) as k) =
  match Hashtbl.find_opt st.fns (k, nn) with
  | Some fd -> fd
  | None ->
      let ty = c_type k in
      let fd =
        Cil.emptyFunction
          (if nn then Printf.sprintf "__p2a_wrapnn_u%d" w
           else Printf.sprintf "__p2a_wrap_%c%d" (if s then 's' else 'u') w)
      in
      Cil.setReturnType fd ty;
      let v = Cil.makeFormalVar fd "v" ty in
      fd.sbody.bstmts <- [ Cil.mkStmt ~valid_sid:true (Return (Some (Cil.evar v), loc0)) ];
      st.created <- fd.svar :: v :: st.created;
      Hashtbl.add st.fns (k, nn) fd;
      fd

let emit st i = st.pending <- i :: st.pending

let take st =
  let l = List.rev st.pending in
  st.pending <- [];
  l

(* [e] reduced to kind [k], as a temporary set by a queued call. *)
let count st f = Option.iter f st.scan

let elided st rule loc =
  count st (fun sc -> sc.IntScan.elided <- (IntScan.loc_string loc, rule) :: sc.elided)

let reduce ?(nn = false) st k e loc =
  count st (fun sc -> if nn then sc.IntScan.nonneg <- sc.nonneg + 1 else sc.kept <- sc.kept + 1);
  match st.cur with
  | None -> raise (Transform.Not_implemented "an integer reduction outside a function")
  | Some fd ->
      let fn = wrap_fn ~nn st k in
      let t = Cil.makeTempVar fd ~name:"p2a_w" (c_type k) in
      st.created <- t :: st.created;
      emit st (Call (Some (Cil.var t), Var fn.svar, [ e ], loc));
      mk ~loc (Lval (Cil.var t))

(* The scan's interval of [e]'s exact value, where omissions are made. *)
let interval st e =
  match st.scan with
  | Some sc when st.elide -> Hashtbl.find_opt sc.IntScan.intervals e.eid
  | _ -> None

let pow2 n = Z.shift_left Z.one n

let in_range (w, s) (lo, hi) =
  if s then Z.geq lo (Z.neg (pow2 (w - 1))) && Z.lt hi (pow2 (w - 1))
  else Z.geq lo Z.zero && Z.lt hi (pow2 w)

(* The constant the scan put in place of [e], if any. *)
let rescued st e =
  match st.scan with
  | Some sc -> (
      match (Hashtbl.find_opt sc.IntScan.rescued e.eid, Ast_types.unroll_node (Cil.typeOf e)) with
      | Some z, TInt ik -> Some (Cil.kinteger64 ~loc:e.eloc ~kind:ik z)
      | Some z, TEnum ei -> Some (Cil.kinteger64 ~loc:e.eloc ~kind:ei.ekind z)
      | _ -> None)
  | None -> None

(* A ring expression that is not a leaf: its C value is its reduced value. *)
let is_ring e =
  match e.enode with
  | BinOp ((PlusA | MinusA | Mult | Shiftlt), _, _, _) | UnOp (Neg, _, _) -> true
  | _ -> false

(* With [All]: a ring expression of a signed type, which wraps. *)
let is_signed_ring st e =
  st.all && is_ring e
  && match kind_of_type (Cil.typeOf e) with Some (_, true) -> true | _ -> false

let rec tr st e =
  let loc = e.eloc in
  let m node = mk ~loc node in
  match e.enode with
  | _ when rescued st e <> None -> Option.get (rescued st e)
  | _ when is_signed_ring st e -> (
      (* the top of a signed ring expression that wraps, where it is used:
         computed unsigned and reduced to its type *)
      match kind_of_type (Cil.typeOf e) with
      | Some k -> reduce st k (tr_unsigned st (fst k, false) e) loc
      | None -> assert false)
  | Const _ | SizeOf _ | SizeOfE _ | AlignOf _ | AlignOfE _ -> e
  | Lval lv -> m (Lval (tr_lval st lv))
  | AddrOf lv -> m (AddrOf (tr_lval st lv))
  | StartOf lv -> m (StartOf (tr_lval st lv))
  | UnOp (Neg, a, t) -> m (UnOp (Neg, tr st a, t))
  | UnOp (op, a, t) -> m (UnOp (op, observe st a, t))
  | BinOp (((PlusA | MinusA | Mult) as op), a, b, t) -> m (BinOp (op, tr st a, tr st b, t))
  | BinOp (Shiftlt, a, b, t) -> m (BinOp (Shiftlt, tr st a, observe st b, t))
  | BinOp (((PlusPI | MinusPI) as op), p, k, t) -> m (BinOp (op, tr st p, observe st k, t))
  | BinOp (MinusPP, a, b, t) -> m (BinOp (MinusPP, tr st a, tr st b, t))
  | BinOp (op, a, b, t) -> m (BinOp (op, observe st a, observe st b, t))
  | CastE (t', a) -> (
      match (kind_of_type t', kind_of_type (Cil.typeOf a)) with
      | Some k', Some k when not (contains k' k) ->
          (* narrowing or changing signedness: the reduction to the target,
             unless the operand's exact value is in the target's range *)
          let a' = tr st a in
          if Cil.isIntegerConstant a' then Cil.constFold true (m (CastE (t', a')))
          else (
            match interval st a with
            | Some iv when in_range k' iv -> elided st "W-Cast" loc; m (CastE (t', a'))
            | Some (lo, _) when (not (snd k')) && Z.geq lo Z.zero ->
                Cil.mkCast ~newt:t' (reduce ~nn:true st k' a' loc)
            | _ -> Cil.mkCast ~newt:t' (reduce st k' a' loc))
      | _ ->
          (* widening, to or from _Bool, to or from floating point, between
             pointers: the operand is observed *)
          if Ast_types.is_ptr t' && Ast_types.is_ptr (Cil.typeOf a) then m (CastE (t', tr st a))
          else m (CastE (t', observe st a)))

(* With [All]: the signed ring expression [e] of width [fst ku] computed in
   the unsigned kind [ku], so that its C value is its -fwrapv value reduced
   modulo 2^w and its mathematical value the exact one. The operands of the
   ring operations are themselves so computed; any other operand is
   converted to the unsigned type (a constant folded), and a shift count is
   observed as usual. *)
and tr_unsigned st ku e =
  let loc = e.eloc in
  let tu = c_type ku in
  let m node = mk ~loc node in
  match e.enode with
  | BinOp (((PlusA | MinusA | Mult) as op), a, b, _) when is_signed_ring st e ->
      m (BinOp (op, tr_unsigned st ku a, tr_unsigned st ku b, tu))
  | BinOp (Shiftlt, a, b, _) when is_signed_ring st e ->
      m (BinOp (Shiftlt, tr_unsigned st ku a, observe st b, tu))
  | UnOp (Neg, a, _) when is_signed_ring st e -> m (UnOp (Neg, tr_unsigned st ku a, tu))
  | _ ->
      let e' = tr st e in
      if Cil.isIntegerConstant e' then Cil.constFold true (m (CastE (tu, e')))
      else m (CastE (tu, e'))

and tr_lval st (host, off) =
  let host = match host with Var v -> Var v | Mem e -> Mem (tr st e) in
  (host, tr_offset st off)

and tr_offset st = function
  | NoOffset -> NoOffset
  | Field (f, o) -> Field (f, tr_offset st o)
  | Index (e, o) -> Index (observe st e, tr_offset st o)

(* [e] where its exact value is observed: reduced if it is an unsigned ring
   expression (a signed one does not overflow in an execution without
   undefined behaviour, so its C value is its mathematical value). *)
and observe st e =
  let e' = tr st e in
  match kind_of_type (Cil.typeOf e) with
  | Some ((_, false) as k) when is_ring e -> (
      match interval st e with
      | Some iv when in_range k iv -> elided st "W-Op/W-Store" e.eloc; e'
      | Some (lo, _) when Z.geq lo Z.zero -> reduce ~nn:true st k e' e.eloc
      | _ -> reduce st k e' e.eloc)
  | _ -> e'

let rec tr_init st = function
  | SingleInit e -> SingleInit (observe st e)
  | CompoundInit (t, l) -> CompoundInit (t, List.map (fun (o, i) -> (o, tr_init st i)) l)

let is_external f =
  not
    (try Kernel_function.is_definition (Globals.Functions.get f) with Not_found -> false)

(* A call; the result of an external function of integer type is received in
   a temporary and stored reduced. *)
let tr_call st ret f args loc mk_call =
  let args = List.map (observe st) args in
  match (ret, kind_of_type (Cil.getReturnType f.vtype)) with
  | Some lv, Some k
    when is_external f
         && kind_of_type (Cil.typeOfLval lv) <> None
         && not (st.elide && st.scan <> None && String.starts_with ~prefix:"__VERIFIER_nondet_" f.vname) ->
      let fd = match st.cur with Some fd -> fd | None -> assert false in
      let t = Cil.makeTempVar fd ~name:"p2a_r" (Cil.getReturnType f.vtype) in
      st.created <- t :: st.created;
      let fn = wrap_fn st k in
      [ mk_call (Some (Cil.var t)) args;
        Call (Some (tr_lval st lv), Var fn.svar, [ Cil.evar t ], loc) ]
  | Some _, Some _ when st.elide && st.scan <> None && String.starts_with ~prefix:"__VERIFIER_nondet_" f.vname ->
      count st (fun sc -> sc.IntScan.ext_elided <- sc.ext_elided + 1);
      [ mk_call (Option.map (tr_lval st) ret) args ]
  | _ -> [ mk_call (Option.map (tr_lval st) ret) args ]

let tr_instr st i =
  let is =
    match i with
    | Set (lv, e, loc) -> [ Set (tr_lval st lv, observe st e, loc) ]
    | Call (ret, Var f, args, loc) ->
        tr_call st ret f args loc (fun r args -> Call (r, Var f, args, loc))
    | Local_init (v, AssignInit i, loc) -> [ Local_init (v, AssignInit (tr_init st i), loc) ]
    | Local_init (v, ConsInit (f, args, k), loc) -> (
        match tr_call st (Some (Cil.var v)) f args loc (fun r args -> Call (r, Var f, args, loc)) with
        | [ Call (Some (Var v', NoOffset), Var g, args', _) ] when v' == v ->
            [ Local_init (v, ConsInit (g, args', k), loc) ]
        | [ call; Call (Some (Var v', NoOffset), Var g, args', _) ] when v' == v ->
            [ call; Local_init (v, ConsInit (g, args', Plain_func), loc) ]
        | is -> is)
    | i -> [ i ]
  in
  take st @ is

let create ?(mode = Unsigned) ?scan () =
  let elide = Sys.getenv_opt "P2A_WRAP_NO_ELIDE" <> Some "1" in
  { all = mode = All; scan; elide; fns = Hashtbl.create 8; created = []; pending = []; cur = None }

let fn st k = (wrap_fn st k).svar

let created st = st.created

let run st =
  let file = Ast.get () in
  let rewrite fd =
    st.cur <- Some fd;
    (* statements this pass made: the queued reductions placed before a
       statement are not rewritten again, and the statement they precede has
       its expression rewritten already *)
    let wrapped = Hashtbl.create 8 and generated = Hashtbl.create 8 in
    let visitor =
      object
        inherit Visitor.frama_c_inplace

        method! vinst i = Cil.ChangeTo (tr_instr st i)

        method! vstmt_aux s =
          if Hashtbl.mem generated s.sid then Cil.SkipChildren
          else begin
          if not (Hashtbl.mem wrapped s.sid) then begin
            let kind =
              match s.skind with
              | Return (Some e, loc) -> Some (Return (Some (observe st e), loc))
              | If (e, b1, b2, loc) -> Some (If (observe st e, b1, b2, loc))
              | Switch (e, b, l, loc) -> Some (Switch (observe st e, b, l, loc))
              | _ -> None
            in
            match (kind, take st) with
            | None, _ -> ()
            | Some k, [] -> s.skind <- k
            | Some k, pre ->
                let inner = Cil.mkStmt ~valid_sid:true k in
                Hashtbl.replace wrapped inner.sid ();
                let pre =
                  List.map
                    (fun i ->
                      let g = Cil.mkStmtOneInstr ~valid_sid:true i in
                      Hashtbl.replace generated g.sid ();
                      g)
                    pre
                in
                s.skind <- Block (Cil.mkBlock (pre @ [ inner ]))
          end;
          Cil.DoChildren
          end
      end
    in
    ignore (Visitor.visitFramacFunction visitor fd);
    st.cur <- None
  in
  List.iter (function GFun (fd, _) -> rewrite fd | _ -> ()) file.globals

(* The definitions of the reduction functions used by [run] and by the
   transformation after it, before the first function definition. *)
let finish st =
  let file = Ast.get () in
  let defs =
    Hashtbl.fold (fun k fd acc -> (k, fd) :: acc) st.fns []
    |> List.sort compare
    |> List.map (fun (_, fd) -> GFun (fd, loc0))
  in
  let rec insert = function
    | (GFun _ as g) :: rest -> defs @ (g :: rest)
    | g :: rest -> g :: insert rest
    | [] -> defs
  in
  file.globals <- insert file.globals
