(* Signed integer overflow made a reachable error (--check-overflow), for
   SV-COMP's no-overflow property: an operation whose result has a signed
   integer type must not produce a value outside that type's range, which is
   the overflow C11 leaves undefined (a conversion to a signed type is
   implementation-defined and is not such an overflow).

   Right before each such operation of the program the output calls a check
   function, one per operation and width, whose body calls reach_error() when
   the exact result is outside the range. Each check is written so that it
   cannot itself overflow, so it means the same in C and when integers are
   read as mathematical integers:

   - a + b: b > 0 and a > MAX - b, or b <= 0 and a < MIN - b;
   - a - b: b < 0 and a > MAX + b, or b >= 0 and a < MIN + b;
   - -a: a = MIN;
   - a / b and a % b: a = MIN and b = -1 (the remainder too, which C11 leaves
     undefined exactly when the quotient is);
   - a * b, width at most 32: the product computed exactly in 64 bits and
     compared with the range; width 64: the division test of CERT INT32-C;
   - a << b, for a count in [0, w) (a count outside it is not an overflow
     and is left alone): a > MAX >> b or a < MIN >> b, the exact a * 2^b
     compared with the range (MIN >> b is exact, MAX >> b the floor).

   Not checked: unsigned operations (their wrap-around is defined), division
   by zero and shift counts out of range (undefined, but not overflow),
   pointer arithmetic, and the operations the pointer-replacing
   transformation adds (this pass runs before it).

   The checks of one instruction or statement are placed before it, the
   operations visited inner first, which is their evaluation order in the
   normalised program: its expressions have no side effects and no logical
   operators (the front end makes && and || control flow; one met here is
   refused). An operand that is not a constant or an lvalue is evaluated
   once, into a temporary set after its own check, so that the checks of a
   nested expression stay linear in its size.

   The input's own reach_error (the unreach-call property's) is an ordinary
   function here: it is renamed, so that the output calls reach_error() for
   overflows alone.

   Contract: [run st] rewrites the current project in place and must run
   before the pointer-replacing transformation, which sees the checks as
   calls with integer arguments of functions it does not know; [finish st]
   then adds the declaration of reach_error and the check functions used.
   [created st] lists the variables made, [marker st] the reach_error
   declared (none when nothing is checked), [renamed st] the input's
   renamed reach_error. *)

open Cil_types

type op = Add | Sub | Neg | Mul | Div | Shl

let op_name = function
  | Add -> "add" | Sub -> "sub" | Neg -> "neg" | Mul -> "mul" | Div -> "div" | Shl -> "shl"

type st = {
  fns : (string, fundec) Hashtbl.t;
  mutable created : varinfo list;
  mutable pending : instr list;  (** reversed *)
  mutable cur : fundec option;
  names : (string, unit) Hashtbl.t;  (** every ordinary identifier taken *)
  mutable marker : varinfo option;
  mutable renamed : varinfo option;
}

let loc0 = Fileloc.unknown
let mk ?(loc = loc0) node = Cil.new_exp ~loc node

let create () =
  { fns = Hashtbl.create 8; created = []; pending = []; cur = None;
    names = Hashtbl.create 64; marker = None; renamed = None }

let created st = st.created
let marker st = st.marker
let renamed st = st.renamed

let fresh st base =
  let rec go i =
    let n = if i = 0 then base else Printf.sprintf "%s_%d" base i in
    if Hashtbl.mem st.names n then go (i + 1)
    else begin
      Hashtbl.replace st.names n ();
      n
    end
  in
  go 0

let kind_of_type t =
  match Ast_types.unroll_node t with
  | TInt ik when ik <> IBool -> Some (Cil.bitsSizeOfInt ik, Cil.isSigned ik)
  | TEnum ei when ei.ekind <> IBool -> Some (Cil.bitsSizeOfInt ei.ekind, Cil.isSigned ei.ekind)
  | _ -> None

let ikind_of ty =
  match Ast_types.unroll_node ty with TInt ik -> ik | _ -> assert false

(* reach_error(), declared only. *)
let marker_var st =
  match st.marker with
  | Some v -> v
  | None ->
      let v =
        Cil.makeGlobalVar "reach_error"
          (Cil_const.mk_tfun Cil_const.voidType (Some []) false)
      in
      st.marker <- Some v;
      v

let pow2 w = Z.two_power_of_int w

(* The check function of [op] at the signed width [w] (and the count kind
   [kb] of a shift). *)
let check_fn st op w kb =
  let key =
    match (op, kb) with
    | Shl, Some (wb, sb) -> Printf.sprintf "shl_s%d_%c%d" w (if sb then 's' else 'u') wb
    | _ -> Printf.sprintf "%s_s%d" (op_name op) w
  in
  match Hashtbl.find_opt st.fns key with
  | Some fd -> fd
  | None ->
      let ty = Wrap.c_type (w, true) in
      let ik = ikind_of ty in
      let fd = Cil.emptyFunction (fresh st ("__p2a_overflow_" ^ key)) in
      Cil.setReturnType fd Cil_const.voidType;
      let a = Cil.makeFormalVar fd "a" ty in
      let bty = match kb with Some k -> Wrap.c_type k | None -> ty in
      let b = if op = Neg then None else Some (Cil.makeFormalVar fd "b" bty) in
      let ea = Cil.evar a in
      let eb () = match b with Some b -> Cil.evar b | None -> assert false in
      let c ?(kind = ik) n = Cil.kinteger64 ~loc:loc0 ~kind n in
      let max = c (Z.pred (pow2 (w - 1))) and min = c (Z.neg (pow2 (w - 1))) in
      let bin op x y t = mk (BinOp (op, x, y, t)) in
      let cmp op x y = bin op x y Cil_const.intType in
      let error = Cil.mkStmtOneInstr ~valid_sid:true (Call (None, Var (marker_var st), [], loc0)) in
      let if_ cond thn els =
        Cil.mkStmt ~valid_sid:true (If (cond, Cil.mkBlock thn, Cil.mkBlock els, loc0))
      in
      let zero = c Z.zero in
      let body =
        match op with
        | Add ->
            [ if_ (cmp Gt (eb ()) zero)
                [ if_ (cmp Gt ea (bin MinusA max (eb ()) ty)) [ error ] [] ]
                [ if_ (cmp Lt ea (bin MinusA min (eb ()) ty)) [ error ] [] ] ]
        | Sub ->
            [ if_ (cmp Lt (eb ()) zero)
                [ if_ (cmp Gt ea (bin PlusA max (eb ()) ty)) [ error ] [] ]
                [ if_ (cmp Lt ea (bin PlusA min (eb ()) ty)) [ error ] [] ] ]
        | Neg -> [ if_ (cmp Eq ea min) [ error ] [] ]
        | Div -> [ if_ (cmp Eq ea min) [ if_ (cmp Eq (eb ()) (c Z.minus_one)) [ error ] [] ] [] ]
        | Mul when w <= 32 ->
            let wide = Wrap.c_type (64, true) in
            let wk = ikind_of wide in
            let p = Cil.makeLocalVar fd "p" wide in
            let cast e = mk (CastE (wide, e)) in
            [ Cil.mkStmtOneInstr ~valid_sid:true
                (Set (Cil.var p, bin Mult (cast ea) (cast (eb ())) wide, loc0));
              if_ (cmp Gt (Cil.evar p) (c ~kind:wk (Z.pred (pow2 (w - 1))))) [ error ]
                [ if_ (cmp Lt (Cil.evar p) (c ~kind:wk (Z.neg (pow2 (w - 1))))) [ error ] [] ] ]
        | Mul ->
            let div x y = bin Div x y ty in
            let b = eb () in
            [ if_ (cmp Gt ea zero)
                [ if_ (cmp Gt b zero)
                    [ if_ (cmp Gt ea (div max b)) [ error ] [] ]
                    [ if_ (cmp Lt b (div min ea)) [ error ] [] ] ]
                [ if_ (cmp Gt b zero)
                    [ if_ (cmp Lt ea (div min b)) [ error ] [] ]
                    [ if_ (cmp Ne ea zero) [ if_ (cmp Lt b (div max ea)) [ error ] [] ] [] ] ] ]
        | Shl ->
            let b = eb () in
            let bk = ikind_of bty in
            let shr x = bin Shiftrt x b ty in
            [ if_ (cmp Ge b (c ~kind:bk Z.zero))
                [ if_ (cmp Lt b (c ~kind:bk (Z.of_int w)))
                    [ if_ (cmp Gt ea (shr max)) [ error ]
                        [ if_ (cmp Lt ea (shr min)) [ error ] [] ] ]
                    [] ]
                [] ]
      in
      fd.sbody.bstmts <- body @ [ Cil.mkStmt ~valid_sid:true (Return (None, loc0)) ];
      st.created <- fd.svar :: a :: st.created;
      Option.iter (fun b -> st.created <- b :: st.created) b;
      List.iter (fun v -> st.created <- v :: st.created) fd.slocals;
      Hashtbl.add st.fns key fd;
      fd

let emit st i = st.pending <- i :: st.pending

let take st =
  let l = List.rev st.pending in
  st.pending <- [];
  l

let rec is_leaf e =
  match e.enode with
  | Const _ | Lval _ | SizeOf _ | SizeOfE _ | AlignOf _ | AlignOfE _ -> true
  | CastE (_, a) -> is_leaf a
  | _ -> false

let rec tr st e =
  let loc = e.eloc in
  let m node = mk ~loc node in
  let signed t = match kind_of_type t with Some (w, true) -> Some w | _ -> None in
  match e.enode with
  | Const _ | SizeOf _ | SizeOfE _ | AlignOf _ | AlignOfE _ -> e
  | Lval lv -> m (Lval (tr_lval st lv))
  | AddrOf lv -> m (AddrOf (tr_lval st lv))
  | StartOf lv -> m (StartOf (tr_lval st lv))
  | UnOp (Neg, a, t) when signed t <> None ->
      let w = Option.get (signed t) in
      let a = operand st a in
      check st Neg w None [ a ] loc;
      m (UnOp (Neg, a, t))
  | UnOp (op, a, t) -> m (UnOp (op, tr st a, t))
  | BinOp ((LAnd | LOr), _, _, _) ->
      raise (Transform.Not_implemented "a logical operator inside an expression (--check-overflow)")
  | BinOp (((PlusA | MinusA | Mult | Div | Mod) as op), a, b, t) when signed t <> None ->
      let w = Option.get (signed t) in
      let a = operand st a in
      let b = operand st b in
      let o = match op with PlusA -> Add | MinusA -> Sub | Mult -> Mul | _ -> Div in
      check st o w None [ a; b ] loc;
      m (BinOp (op, a, b, t))
  | BinOp (Shiftlt, a, b, t) when signed t <> None -> (
      let w = Option.get (signed t) in
      let a = operand st a in
      let b = operand st b in
      match kind_of_type (Cil.typeOf b) with
      | Some kb ->
          check st Shl w (Some kb) [ a; b ] loc;
          m (BinOp (Shiftlt, a, b, t))
      | None -> m (BinOp (Shiftlt, a, b, t)))
  | BinOp (op, a, b, t) -> m (BinOp (op, tr st a, tr st b, t))
  | CastE (t, a) -> m (CastE (t, tr st a))

(* An operand, its own operations checked first; evaluated into a temporary
   unless it is a leaf. *)
and operand st e =
  let e' = tr st e in
  (* a constant expression is folded (its own operations checked above, so
     a folded value that wrapped has had its check emitted already) *)
  let folded = Cil.constFold true e' in
  if Cil.isIntegerConstant folded then folded
  else if is_leaf e' then e'
  else
    match st.cur with
    | None -> raise (Transform.Not_implemented "an overflow check outside a function")
    | Some fd ->
        let t = Cil.makeTempVar fd ~name:"p2a_o" (Cil.typeOf e) in
        st.created <- t :: st.created;
        emit st (Set (Cil.var t, e', e.eloc));
        mk ~loc:e.eloc (Lval (Cil.var t))

(* The exact result of [op] on constant operands, when it is defined
   mathematically (None for a division by zero or a shift count out of
   range, which are not overflows). *)
and exact op args =
  match (op, List.map Cil.isInteger args) with
  | Add, [ Some a; Some b ] -> Some (Z.add a b)
  | Sub, [ Some a; Some b ] -> Some (Z.sub a b)
  | Mul, [ Some a; Some b ] -> Some (Z.mul a b)
  | Neg, [ Some a ] -> Some (Z.neg a)
  | Div, [ Some a; Some b ] when not (Z.equal b Z.zero) -> Some (Z.div a b)
  | Shl, [ Some a; Some b ] when Z.geq b Z.zero && Z.lt b (Z.of_int 64) ->
      Some (Z.shift_left a (Z.to_int b))
  | _ -> None

and check st op w kb args loc =
  if st.cur = None then raise (Transform.Not_implemented "an overflow check outside a function");
  let in_range v =
    Z.geq v (Z.neg (Z.two_power_of_int (w - 1))) && Z.lt v (Z.two_power_of_int (w - 1))
  in
  (* an operation on constants that stays in range needs no check (the
     front end leaves such expressions, INT_MIN as -INT_MAX - 1 among them) *)
  match exact op args with
  | Some v when in_range v -> ()
  | _ ->
      let fn = check_fn st op w kb in
      emit st (Call (None, Var fn.svar, args, loc))

and tr_lval st (host, off) =
  let host = match host with Var v -> Var v | Mem e -> Mem (tr st e) in
  (host, tr_offset st off)

and tr_offset st = function
  | NoOffset -> NoOffset
  | Field (f, o) -> Field (f, tr_offset st o)
  | Index (e, o) -> Index (tr st e, tr_offset st o)

let rec tr_init st = function
  | SingleInit e -> SingleInit (tr st e)
  | CompoundInit (t, l) -> CompoundInit (t, List.map (fun (o, i) -> (o, tr_init st i)) l)

let tr_instr st i =
  let is =
    match i with
    | Set (lv, e, loc) ->
        let e = tr st e in
        [ Set (tr_lval st lv, e, loc) ]
    | Call (ret, f, args, loc) ->
        let args = List.map (tr st) args in
        [ Call (Option.map (tr_lval st) ret, f, args, loc) ]
    | Local_init (v, AssignInit i, loc) -> [ Local_init (v, AssignInit (tr_init st i), loc) ]
    | Local_init (v, ConsInit (f, args, k), loc) ->
        [ Local_init (v, ConsInit (f, List.map (tr st) args, k), loc) ]
    | i -> [ i ]
  in
  take st @ is

(* The input's reach_error, and anything else it names reach_error at file
   scope, renamed: the marker's declaration would clash with it. So is its
   __VERIFIER_error, the older name of the same error event, so that a
   consumer reading that name as the error event never takes the input's
   for an overflow. *)
let rename_input_error_events st file =
  let rename original =
    let name = lazy (fresh st ("__p2a_input_" ^ original)) in
    List.iter
      (function
        | GFun ({ svar = vi; _ }, _) | GFunDecl (_, vi, _) | GVar (vi, _, _) | GVarDecl (vi, _)
          when vi.vname = original ->
            vi.vname <- Lazy.force name;
            if original = "reach_error" && Ast_types.is_fun vi.vtype then st.renamed <- Some vi
        | GType (ti, _) when ti.tname = original -> ti.tname <- Lazy.force name
        | GEnumTag (ei, _) | GEnumTagDecl (ei, _) ->
            List.iter
              (fun it -> if it.einame = original then it.einame <- Lazy.force name)
              ei.eitems
        | _ -> ())
      file.globals
  in
  rename "reach_error";
  rename "__VERIFIER_error"

let run st =
  let file = Ast.get () in
  let note n = Hashtbl.replace st.names n () in
  List.iter
    (function
      | GVar (vi, _, _) | GVarDecl (vi, _) | GFunDecl (_, vi, _) -> note vi.vname
      | GFun (fd, _) ->
          note fd.svar.vname;
          List.iter (fun v -> note v.vname) fd.sformals;
          List.iter (fun v -> note v.vname) fd.slocals
      | GType (ti, _) -> note ti.tname
      | GEnumTag (ei, _) | GEnumTagDecl (ei, _) -> List.iter (fun it -> note it.einame) ei.eitems
      | _ -> ())
    file.globals;
  rename_input_error_events st file;
  let rewrite fd =
    st.cur <- Some fd;
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
                | Return (Some e, loc) -> Some (Return (Some (tr st e), loc))
                | If (e, b1, b2, loc) -> Some (If (tr st e, b1, b2, loc))
                | Switch (e, b, l, loc) -> Some (Switch (tr st e, b, l, loc))
                | _ -> None
              in
              match (kind, take st) with
              | None, _ -> ()
              | Some k, [] -> s.skind <- k
              | Some k, pre ->
                  let inner = Cil.mkStmt ~valid_sid:true k in
                  Hashtbl.replace wrapped inner.sid ();
                  (* the labels and the case markers stay on the statement
                     that holds the checks, so that a jump runs them *)
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

(* The declaration of reach_error and the definitions of the check functions,
   before the first function definition. *)
let finish st =
  let file = Ast.get () in
  let defs =
    Hashtbl.fold (fun k fd acc -> (k, fd) :: acc) st.fns []
    |> List.sort (fun (a, _) (b, _) -> compare a b)
    |> List.map (fun (_, fd) -> GFun (fd, loc0))
  in
  let decl =
    match st.marker with
    | Some v -> [ GFunDecl (Cil.empty_funspec (), v, loc0) ]
    | None -> []
  in
  let defs = decl @ defs in
  let rec insert = function
    | (GFun _ as g) :: rest -> defs @ (g :: rest)
    | g :: rest -> g :: insert rest
    | [] -> defs
  in
  if defs <> [] then file.globals <- insert file.globals
