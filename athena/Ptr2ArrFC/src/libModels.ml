(* Models of external functions that take or return a pointer: those that
   read a program's input (fscanf and scanf with integer conversions, fgets,
   atoi, recv, connect and bind, with which the Juliet tasks read their
   data), the string and memory searches (memcmp, strncmp, strchr, strrchr,
   memchr), GCC's unsigned overflow builtins and __builtin_object_size, and
   the verifier's __VERIFIER_nondet_memory.  Each takes or returns a pointer
   into the program's memory, which puts it outside the fragment: what an
   external function reads and writes through a pointer is unknown in
   general.  For these it is known, and the input they read is arbitrary.

   Before the fragment check, each call is replaced by a call to a function
   added to the program, written with the fragment's constructs and
   __VERIFIER_nondet_* draws.  The added functions are then transformed as any
   other: their reads and writes are reads and writes of the regions their
   pointers point into, checked in a safety mode, so a buffer smaller than
   what the call may write is the invalid dereference it is in the input.

   What each model does, for an arbitrary input (C11 7.21.6.2, 7.21.7.2,
   7.22.1.2; POSIX recv, connect, bind):

   - fscanf(stream, fmt, p1, ..., pk) and scanf(fmt, p1, ..., pk), where the
     format is a string literal whose conversions are d i u o x X with an
     optional length (hh h l ll j z t) and no width, possibly suppressed with
     *: returns some m in -1..k and stores an arbitrary value of its type
     through each of p1..pm (the first m conversions matched, the rest left
     as they are; -1 is end of input before the first conversion).  A value
     out of the type's range is undefined in C, so any value is a value C
     allows.  The stream is not read.
   - fgets(s, n, stream): for n <= 0 returns NULL and writes nothing (C does
     not define this case; glibc does the same).  Otherwise one of: NULL with
     the array unchanged (end of input before any character); NULL with
     s[0..n-1] arbitrary (a read error: C makes the contents indeterminate);
     or s, having written k arbitrary characters, 0 <= k <= n-1, and a 0
     after them.  The model allows a newline before the last character,
     which fgets does not produce: an over-approximation.
   - atoi(s): what C specifies, character by character: white space
     skipped, an optional sign, then decimal digits up to the first
     non-digit; a value int cannot represent is undefined in C, and the
     model returns an arbitrary int for it.
   - recv(fd, buf, len, flags): returns some r in -1..len and writes r
     arbitrary bytes from buf.
   - connect(fd, addr, len) and bind(fd, addr, len): return 0 or -1.  The
     address is not read: an address the kernel cannot read is an error
     (EFAULT, -1), not undefined behaviour.

   - memcmp(a, b, n): reads all n characters of both (C lets it), and
     returns the sign of the first difference as unsigned chars (-1, 0, 1:
     C fixes only the sign).
   - strncmp(a, b, n): reads up to the first difference, the first 0 or n
     characters, and returns the sign as memcmp does.
   - strchr(s, c), strrchr(s, c): read the string up to its 0 and return
     the first (last) position holding (char) c, the 0 included, or NULL.
   - memchr(s, c, n): reads up to the first character equal to
     (unsigned char) c, at most n, and returns its position or NULL.
   - __builtin_u{add,sub,mul}{,l,ll}_overflow(a, b, res): stores the result
     modulo 2^w through res and returns whether the mathematical one differs
     (for the multiplication: a != 0 and the stored result divided by a is
     not b).  Only with GCC's prototype: two operands of one unsigned type
     and a pointer to it.
   - __builtin_object_size(p, t), t a constant: (size_t)-1 for t 0 or 1, 0
     for t 2 or 3, the answers GCC gives for an object it cannot size, which
     it may give for any.
   - __VERIFIER_nondet_memory(p, n): writes n arbitrary bytes from p.

   Left as they are (and refused by the fragment check as before): a format
   that is not a string literal or has another conversion (%s, %c, %f, %n,
   %[), a width, or arguments that do not match it; a scanf argument that
   does not point to an integer. *)

open Cil_types

let loc0 = Fileloc.unknown

let rec strip_casts e = match e.enode with CastE (_, e') -> strip_casts e' | _ -> e

let literal_string e =
  match (strip_casts e).enode with
  | StartOf (Var vi, NoOffset) | AddrOf (Var vi, Index (_, NoOffset))
    when Ast_info.is_string_literal vi -> (
      match Globals.Vars.get_string_literal vi with Str s -> Some s | Wstr _ -> None)
  | _ -> None

(* The number of stored conversions of a scanf format, or None when it has
   anything but integer conversions without a width. *)
let scanf_conversions fmt =
  let n = String.length fmt in
  let rec go i k =
    if i >= n then Some k
    else if fmt.[i] <> '%' then go (i + 1) k
    else if i + 1 < n && fmt.[i + 1] = '%' then go (i + 2) k
    else begin
      let j = ref (i + 1) in
      let suppressed = !j < n && fmt.[!j] = '*' in
      if suppressed then incr j;
      if !j < n && fmt.[!j] >= '0' && fmt.[!j] <= '9' then None
      else begin
        while !j < n && String.contains "hljzt" fmt.[!j] do incr j done;
        if !j < n && String.contains "diuoxX" fmt.[!j] then go (!j + 1) (if suppressed then k else k + 1)
        else None
      end
    end
  in
  go 0 0

(* The integer kind of what a pointer argument points to. *)
let pointee_ikind e =
  match Ast_types.unroll_node (Cil.typeOf e) with
  | TPtr t -> (
      match Ast_types.unroll_node t with
      | TInt (IInt128 | IUInt128) -> None
      | TInt k -> Some k
      | TEnum ei -> Some ei.ekind
      | _ -> None)
  | _ -> None

(* The name suffix and type of the __VERIFIER_nondet_ function for a kind. *)
let nondet_of_ikind = function
  | IBool -> ("bool", Cil_const.boolType)
  | IChar | ISChar -> ("char", Cil_const.charType)
  | IUChar -> ("uchar", Cil_const.ucharType)
  | IShort -> ("short", Cil_const.shortType)
  | IUShort -> ("ushort", Cil_const.ushortType)
  | IInt -> ("int", Cil_const.intType)
  | IUInt -> ("uint", Cil_const.uintType)
  | ILong -> ("long", Cil_const.longType)
  | IULong -> ("ulong", Cil_const.ulongType)
  | ILongLong -> ("longlong", Cil_const.longLongType)
  | IULongLong -> ("ulonglong", Cil_const.ulongLongType)
  | IInt128 | IUInt128 -> invalid_arg "nondet_of_ikind"

let find_function file name =
  List.find_map
    (function
      | GFun (fd, _) when fd.svar.vname = name -> Some fd.svar
      | GFunDecl (_, vi, _) when vi.vname = name -> Some vi
      | _ -> None)
    file.globals

(* What a call becomes: the model's key (one added function per key) and
   the arguments the added function takes. *)
type plan =
  | Scanf of ikind list * exp list (* the pointees' kinds, the pointers *)
  | Fgets of exp * exp (* s, n *)
  | Atoi of exp
  | Recv of ikind * exp * exp (* the element kind, buf, len *)
  | Connect
  | Nondet_memory of ikind * exp * exp (* the element kind, p, n *)
  | Object_size of int (* the value: -1 or 0 *)
  | Unsigned_overflow of binop * string * exp * exp * exp (* op, name, a, b, res *)
  | Memcmp of ikind * ikind * exp * exp * exp
  | Strncmp of exp * exp * exp
  | Strchr of bool * exp * exp (* the last occurrence (strrchr), s, c *)
  | Memchr of ikind * exp * exp * exp

let key = function
  | Scanf (ks, _) -> "scanf:" ^ String.concat "," (List.map (fun k -> fst (nondet_of_ikind k)) ks)
  | Fgets _ -> "fgets"
  | Atoi _ -> "atoi"
  | Recv (k, _, _) -> "recv:" ^ fst (nondet_of_ikind k)
  | Connect -> "connect"
  | Nondet_memory (k, _, _) -> "nondet_memory:" ^ fst (nondet_of_ikind k)
  | Object_size v -> "object_size:" ^ string_of_int v
  | Unsigned_overflow (_, name, _, _, _) -> name
  | Memcmp (ka, kb, _, _, _) -> "memcmp:" ^ fst (nondet_of_ikind ka) ^ "," ^ fst (nondet_of_ikind kb)
  | Strncmp _ -> "strncmp"
  | Strchr (last, _, _) -> if last then "strrchr" else "strchr"
  | Memchr (k, _, _, _) -> "memchr:" ^ fst (nondet_of_ikind k)

(* recv's buffer as a pointer to its characters: the address of a character
   array is the array's start, a pointer to characters is kept, anything
   else is read as bytes. *)
let recv_buffer e =
  let e' = strip_casts e in
  let char_kind t =
    match Ast_types.unroll_node t with
    | TInt ((IChar | ISChar | IUChar) as k) -> Some k
    | _ -> None
  in
  match Ast_types.unroll_node (Cil.typeOf e') with
  | TPtr t -> (
      match (Ast_types.unroll_node t, e'.enode) with
      | TArray (et, _), AddrOf lv when char_kind et <> None ->
          ((match char_kind et with Some k -> k | None -> IChar), Cil.new_exp ~loc:e'.eloc (StartOf lv))
      | _ -> (
          match char_kind t with
          | Some k -> (k, e')
          | None -> (IUChar, Cil.mkCast ~newt:Cil_const.ucharPtrType e')))
  | _ -> (IUChar, Cil.mkCast ~newt:Cil_const.ucharPtrType e)

(* The operation of a GCC unsigned overflow builtin
   (__builtin_u{add,sub,mul}{,l,ll}_overflow). *)
let unsigned_overflow_op name =
  let ops = [ ("add", PlusA); ("sub", MinusA); ("mul", Mult) ] in
  List.find_map
    (fun (o, op) ->
      if List.exists
           (fun w -> name = Printf.sprintf "__builtin_u%s%s_overflow" o w)
           [ ""; "l"; "ll" ]
      then Some op
      else None)
    ops

let plan_of f args =
  if Fragment.is_defined f then None
  else
    match (f.vname, args) with
    | ("fscanf" | "__isoc99_fscanf"), _ :: fmt :: ps | ("scanf" | "__isoc99_scanf"), fmt :: ps -> (
        match match literal_string fmt with Some t -> scanf_conversions t | None -> None with
        | Some k when k = List.length ps -> (
            let ks = List.map pointee_ikind ps in
            if List.for_all Option.is_some ks then
              Some (Scanf (List.filter_map (fun k -> k) ks, ps))
            else None)
        | _ -> None)
    | "fgets", [ s; n; _ ] -> Some (Fgets (s, n))
    | "atoi", [ s ] -> Some (Atoi s)
    | "recv", [ _; buf; len; _ ] ->
        let k, b = recv_buffer buf in
        Some (Recv (k, b, len))
    | ("connect" | "bind"), [ _; _; _ ] -> Some Connect
    | "__VERIFIER_nondet_memory", [ p; n ] ->
        let k, b = recv_buffer p in
        Some (Nondet_memory (k, b, n))
    | "__builtin_object_size", [ _; t ] -> (
        match Cil.isInteger (Cil.constFold true t) with
        | Some z when Z.equal z Z.zero || Z.equal z Z.one -> Some (Object_size (-1))
        | Some z when Z.equal z (Z.of_int 2) || Z.equal z (Z.of_int 3) -> Some (Object_size 0)
        | _ -> None)
    | name, [ a; b; r ] when unsigned_overflow_op name <> None -> (
        (* only with the prototype GCC gives them: two operands of one
           unsigned type and a pointer to it *)
        let unsigned t = match Ast_types.unroll_node t with TInt k -> not (Cil.isSigned k) | _ -> false in
        match (unsigned_overflow_op name, Ast_types.unroll_node f.vtype) with
        | Some op, TFun (_, Some [ (_, ta, _); (_, tb, _); (_, tr, _) ], false)
          when unsigned ta
               && Cil_datatype.Typ.equal (Ast_types.unroll_deep ta) (Ast_types.unroll_deep tb)
               && (match Ast_types.unroll_node tr with
                   | TPtr t -> Cil_datatype.Typ.equal (Cil.typeDeepDropAllAttributes (Ast_types.unroll_deep t)) (Cil.typeDeepDropAllAttributes (Ast_types.unroll_deep ta))
                   | _ -> false) ->
            Some (Unsigned_overflow (op, name, a, b, r))
        | _ -> None)
    | "memcmp", [ a; b; n ] ->
        let ka, a' = recv_buffer a and kb, b' = recv_buffer b in
        Some (Memcmp (ka, kb, a', b', n))
    | "strncmp", [ a; b; n ] -> Some (Strncmp (a, b, n))
    | "strchr", [ s; c ] -> Some (Strchr (false, s, c))
    | "strrchr", [ s; c ] -> Some (Strchr (true, s, c))
    | "memchr", [ p; c; n ] ->
        let k, b = recv_buffer p in
        Some (Memchr (k, b, c, n))
    | _ -> None

(* Statement and expression builders for the added functions. *)
let stmt i = Cil.mkStmtOneInstr ~valid_sid:true i
let set lv e = stmt (Set (lv, Cil.mkCast ~newt:(Cil.typeOfLval lv) e, loc0))
let call r f args = stmt (Call (r, Var f, args, loc0))
let ret e = Cil.mkStmt ~valid_sid:true (Return (e, loc0))
let if_ c th el = Cil.mkStmt ~valid_sid:true (If (c, Cil.mkBlock th, Cil.mkBlock el, loc0))
let bin op a b = Cil.mkBinOp_exn ~loc:loc0 op a b
let int n = Cil.integer ~loc:loc0 n
let ev = Cil.evar ~loc:loc0
let deref p = Cil.new_exp ~loc:loc0 (Lval (Mem p, NoOffset))
let at p i =
  Cil.mkMem ~addr:(Cil.new_exp ~loc:loc0 (BinOp (PlusPI, p, i, Cil.typeOf p))) ~off:NoOffset
let while_ guard body =
  Cil.mkStmt ~valid_sid:true (Block (Cil.mkBlock (Cil.mkWhile ~guard ~body ())))
(* Conditions with && and || written as nested ifs: the later phases read
   normalised C, in which no expression holds a logical operator. The
   branches are thunks, since a statement may appear only once. *)
type cond = A of exp | And of cond * cond | Or of cond * cond

let rec if_b c th el =
  match c with
  | A e -> [ if_ e (th ()) (el ()) ]
  | And (x, y) -> if_b x (fun () -> if_b y th el) el
  | Or (x, y) -> if_b x th (fun () -> if_b y th el)

let while_b c body =
  while_ (int 1)
    (if_b c (fun () -> []) (fun () -> [ Cil.mkStmt ~valid_sid:true (Break loc0) ]) @ body)

let run () =
  let file = Ast.get () in
  (* 1: the calls to replace, by statement *)
  let plans = Hashtbl.create 8 in
  let collect =
    object (self)
      inherit Visitor.frama_c_inplace

      method! vinst i =
        (match i with
         | Call (_, Var f, args, _) | Local_init (_, ConsInit (f, args, Plain_func), _) -> (
             match plan_of f args with
             | Some p -> Option.iter (fun st -> Hashtbl.replace plans st.sid (f, p)) self#current_stmt
             | None -> ())
         | _ -> ());
        Cil.SkipChildren
    end
  in
  Visitor.visitFramacFileSameGlobals collect file;
  if Hashtbl.length plans = 0 then 0
  else begin
    (* 2: the added functions, one per key, with the nondet declarations
       they call *)
    (* the globals added, in reverse order: each nondet declaration before
       the first added function that calls it *)
    let added = ref [] in
    let given = Hashtbl.create 8 in
    let fresh base =
      let rec go k =
        let n = Defunc.fresh_global_name file (if k = 0 then base else Printf.sprintf "%s_%d" base k) in
        if Hashtbl.mem given n then go (k + 1) else (Hashtbl.replace given n (); n)
      in
      go 0
    in
    let nondets = Hashtbl.create 8 in
    let nondet k =
      let suffix, t = nondet_of_ikind k in
      let name = "__VERIFIER_nondet_" ^ suffix in
      match Hashtbl.find_opt nondets name with
      | Some vi -> vi
      | None ->
          let vi =
            match find_function file name with
            | Some vi -> vi
            | None ->
                let ft = Cil_const.mk_tfun t (Some []) false in
                let vi = Cil.makeGlobalVar name ft in
                Cil.setFormalsDecl vi ft;
                let spec = Cil.empty_funspec () in
                added := GFunDecl (spec, vi, loc0) :: !added;
                Globals.Functions.replace_by_declaration spec vi loc0;
                vi
          in
          Hashtbl.replace nondets name vi;
          vi
    in
    (* draws a value of kind [k] into [lv] *)
    let draws = ref 0 in
    let draw fd k lv =
      let _, t = nondet_of_ikind k in
      incr draws;
      let tmp = Cil.makeLocalVar fd (Printf.sprintf "nd%d" !draws) t in
      [ call (Some (Cil.var tmp)) (nondet k) []; set lv (ev tmp) ]
    in
    let helpers = Hashtbl.create 8 in
    let helper (f : varinfo) p =
      let k = key p in
      match Hashtbl.find_opt helpers k with
      | Some vi -> vi
      | None ->
          let rty =
            match Ast_types.unroll_node f.vtype with
            | TFun (r, _, _) -> Ast_types.unroll_deep r
            | _ -> Cil_const.intType
          in
          let base =
            match p with
            | Scanf _ -> "__p2a_scanf"
            | Fgets _ -> "__p2a_fgets"
            | Atoi _ -> "__p2a_atoi"
            | Recv _ -> "__p2a_recv"
            | Connect -> "__p2a_connect"
            | Nondet_memory _ -> "__p2a_nondet_memory"
            | Object_size _ -> "__p2a_object_size"
            | Unsigned_overflow (op, _, _, _, _) ->
                "__p2a_u" ^ (match op with PlusA -> "add" | MinusA -> "sub" | _ -> "mul") ^ "_overflow"
            | Memcmp _ -> "__p2a_memcmp"
            | Strncmp _ -> "__p2a_strncmp"
            | Strchr (last, _, _) -> if last then "__p2a_strrchr" else "__p2a_strchr"
            | Memchr _ -> "__p2a_memchr"
          in
          let fd = Cil.emptyFunction (fresh base) in
          let formals =
            match p with
            | Scanf (ks, _) ->
                List.mapi
                  (fun i k -> (Printf.sprintf "p%d" (i + 1), Cil_const.mk_tptr (snd (nondet_of_ikind k))))
                  ks
            | Fgets _ -> [ ("s", Cil_const.charPtrType); ("n", Cil_const.intType) ]
            | Atoi _ -> [ ("s", Cil_const.charConstPtrType) ]
            | Recv (k, _, len) ->
                [ ("buf", Cil_const.mk_tptr (snd (nondet_of_ikind k)));
                  ("len", Ast_types.unroll_deep (Cil.typeOf len)) ]
            | Connect | Object_size _ -> []
            | Nondet_memory (k, _, n) ->
                [ ("p", Cil_const.mk_tptr (snd (nondet_of_ikind k)));
                  ("n", Ast_types.unroll_deep (Cil.typeOf n)) ]
            | Unsigned_overflow _ -> (
                match Ast_types.unroll_node f.vtype with
                | TFun (_, Some [ (_, ta, _); (_, tb, _); (_, tr, _) ], _) ->
                    [ ("a", Ast_types.unroll_deep ta); ("b", Ast_types.unroll_deep tb);
                      ("res", Ast_types.unroll_deep tr) ]
                | _ -> invalid_arg "unsigned overflow builtin without a prototype")
            | Memcmp (ka, kb, _, _, n) ->
                [ ("a", Cil_const.mk_tptr (snd (nondet_of_ikind ka)));
                  ("b", Cil_const.mk_tptr (snd (nondet_of_ikind kb)));
                  ("n", Ast_types.unroll_deep (Cil.typeOf n)) ]
            | Strncmp (_, _, n) ->
                [ ("a", Cil_const.charConstPtrType); ("b", Cil_const.charConstPtrType);
                  ("n", Ast_types.unroll_deep (Cil.typeOf n)) ]
            | Strchr _ -> [ ("s", Cil_const.charConstPtrType); ("c", Cil_const.intType) ]
            | Memchr (k, _, _, n) ->
                [ ("s", Cil_const.mk_tptr (snd (nondet_of_ikind k))); ("c", Cil_const.intType);
                  ("n", Ast_types.unroll_deep (Cil.typeOf n)) ]
          in
          Cil.update_var_type fd.svar
            (Cil_const.mk_tfun rty (Some (List.map (fun (n, t) -> (n, t, [])) formals)) false);
          let fv = List.map (fun (n, t) -> Cil.makeFormalVar fd n t) formals in
          let local n t = Cil.makeLocalVar fd n t in
          let body =
            match (p, fv) with
            | Scanf (ks, _), ps ->
                let m = local "m" Cil_const.intType in
                let k = List.length ks in
                [ call (Some (Cil.var m)) (nondet IInt) [];
                  if_ (bin Lt (ev m) (int (-1))) [ set (Cil.var m) (int (-1)) ] [];
                  if_ (bin Gt (ev m) (int k)) [ set (Cil.var m) (int (-1)) ] [] ]
                @ List.concat
                    (List.mapi
                       (fun i (kd, pv) ->
                         [ if_ (bin Ge (ev m) (int (i + 1)))
                             (draw fd kd (Cil.mkMem ~addr:(ev pv) ~off:NoOffset))
                             [] ])
                       (List.combine ks ps))
                @ [ ret (Some (Cil.mkCast ~newt:rty (ev m))) ]
            | Fgets _, [ s; n ] ->
                let null = Cil.mkCast ~newt:rty (int 0) in
                let c = local "c" Cil_const.intType and kk = local "k" Cil_const.intType in
                let i = local "i" Cil_const.intType in
                let fill upto =
                  [ set (Cil.var i) (int 0);
                    while_ (bin Lt (ev i) upto)
                      (draw fd IChar (at (ev s) (ev i)) @ [ set (Cil.var i) (bin PlusA (ev i) (int 1)) ]) ]
                in
                let res = local "res" rty in
                (* one return, as Frama-C's normalisation gives every function *)
                [ set (Cil.var res) null;
                  if_ (bin Gt (ev n) (int 0))
                    [ call (Some (Cil.var c)) (nondet IInt) [];
                      (* 0: end of input before any character, nothing written *)
                      if_ (bin Eq (ev c) (int 0)) []
                        [ if_ (bin Eq (ev c) (int 1))
                            (* a read error: the contents indeterminate *)
                            (fill (ev n))
                            ([ call (Some (Cil.var kk)) (nondet IInt) [];
                               if_ (bin Lt (ev kk) (int 0)) [ set (Cil.var kk) (int 0) ] [];
                               if_ (bin Gt (ev kk) (bin MinusA (ev n) (int 1))) [ set (Cil.var kk) (int 0) ] [] ]
                            @ fill (ev kk)
                            @ [ set (at (ev s) (ev kk)) (int 0); set (Cil.var res) (ev s) ]) ] ]
                    [];
                  ret (Some (ev res)) ]
            | Atoi _, [ s ] ->
                let ll = Cil_const.longLongType in
                let llc n = Cil.kinteger64 ~loc:loc0 ~kind:ILongLong n in
                let int_bits = Cil.bitsSizeOf Cil_const.intType in
                let imax = Cil.max_signed_number int_bits in
                let v = local "v" ll and neg = local "neg" Cil_const.intType in
                let big = local "big" Cil_const.intType and r = local "r" Cil_const.intType in
                let cur () = Cil.mkCast ~newt:Cil_const.intType (deref (ev s)) in
                let step () =
                  set (Cil.var s) (Cil.new_exp ~loc:loc0 (BinOp (PlusPI, ev s, int 1, Cil.typeOf (ev s))))
                in
                let ch c = int (Char.code c) in
                [ set (Cil.var v) (int 0); set (Cil.var neg) (int 0); set (Cil.var big) (int 0);
                  while_b
                    (Or (A (bin Eq (cur ()) (ch ' ')),
                         And (A (bin Ge (cur ()) (int 9)), A (bin Le (cur ()) (int 13)))))
                    [ step () ];
                  if_ (bin Eq (cur ()) (ch '-')) [ set (Cil.var neg) (int 1); step () ]
                    [ if_ (bin Eq (cur ()) (ch '+')) [ step () ] [] ];
                  while_b
                    (And (A (bin Ge (cur ()) (ch '0')), A (bin Le (cur ()) (ch '9'))))
                    [ if_ (bin Le (ev v) (llc (Z.succ imax)))
                        [ set (Cil.var v)
                            (bin PlusA (bin Mult (ev v) (llc (Z.of_int 10)))
                               (Cil.mkCast ~newt:ll (bin MinusA (cur ()) (ch '0')))) ]
                        [ set (Cil.var big) (int 1) ];
                      step () ] ]
                @
                (* a value int cannot represent: undefined in C, any int here *)
                let undefined () = [ call (Some (Cil.var r)) (nondet IInt) [] ] in
                [ if_ (ev big) (undefined ())
                    [ if_ (ev neg)
                        [ if_ (bin Gt (ev v) (llc (Z.succ imax))) (undefined ())
                            [ set (Cil.var r) (Cil.new_exp ~loc:loc0 (UnOp (Neg, ev v, ll))) ] ]
                        [ if_ (bin Gt (ev v) (llc imax)) (undefined ()) [ set (Cil.var r) (ev v) ] ] ];
                  ret (Some (Cil.mkCast ~newt:rty (ev r))) ]
            | Recv (k, _, _), [ buf; len ] ->
                let r = local "r" rty and i = local "i" rty in
                let rk = match Ast_types.unroll_node rty with TInt k -> k | _ -> ILong in
                [ call (Some (Cil.var r)) (nondet rk) [];
                  if_ (bin Lt (ev r) (Cil.mkCast ~newt:rty (int (-1)))) [ set (Cil.var r) (int (-1)) ] [];
                  if_ (bin Gt (ev r) (Cil.mkCast ~newt:rty (int 0)))
                    [ if_ (bin Gt (Cil.mkCast ~newt:(Cil.typeOf (ev len)) (ev r)) (ev len))
                        [ set (Cil.var r) (int (-1)) ] [] ]
                    [];
                  set (Cil.var i) (int 0);
                  while_ (bin Lt (ev i) (ev r))
                    (draw fd k (at (ev buf) (ev i)) @ [ set (Cil.var i) (bin PlusA (ev i) (int 1)) ]);
                  ret (Some (ev r)) ]
            | Connect, [] ->
                let m = local "m" Cil_const.intType in
                [ call (Some (Cil.var m)) (nondet IInt) [];
                  if_ (bin Ne (ev m) (int 0)) [ set (Cil.var m) (int (-1)) ] [];
                  ret (Some (Cil.mkCast ~newt:rty (ev m))) ]
            | Nondet_memory (k, _, _), [ p; n ] ->
                let i = local "i" (Cil.typeOf (ev n)) in
                [ set (Cil.var i) (int 0);
                  while_ (bin Lt (ev i) (ev n))
                    (draw fd k (at (ev p) (ev i)) @ [ set (Cil.var i) (bin PlusA (ev i) (int 1)) ]);
                  ret None ]
            | Object_size v, [] -> [ ret (Some (Cil.mkCast ~newt:rty (int v))) ]
            | Unsigned_overflow (op, _, _, _, _), [ a; b; res ] ->
                let t = Cil.typeOf (ev a) in
                let r = local "r" t and ov = local "ov" Cil_const.intType in
                let overflow =
                  match op with
                  | PlusA -> [ if_ (bin Lt (ev r) (ev a)) [ set (Cil.var ov) (int 1) ] [] ]
                  | MinusA -> [ if_ (bin Lt (ev a) (ev b)) [ set (Cil.var ov) (int 1) ] [] ]
                  | _ ->
                      [ if_ (bin Ne (ev a) (Cil.mkCast ~newt:t (int 0)))
                          [ if_ (bin Ne (bin Div (ev r) (ev a)) (ev b)) [ set (Cil.var ov) (int 1) ] [] ]
                          [] ]
                in
                [ set (Cil.var r) (bin op (ev a) (ev b));
                  set (Cil.mkMem ~addr:(ev res) ~off:NoOffset) (ev r);
                  set (Cil.var ov) (int 0) ]
                @ overflow
                @ [ ret (Some (Cil.mkCast ~newt:rty (ev ov))) ]
            | Memcmp _, [ a; b; n ] ->
                (* every one of the n characters is read, as C allows the
                   function to; the sign is the first difference's *)
                let uc = Cil_const.ucharType in
                let i = local "i" (Cil.typeOf (ev n)) and res = local "res" Cil_const.intType in
                let ca = local "ca" uc and cb = local "cb" uc in
                [ set (Cil.var res) (int 0); set (Cil.var i) (int 0);
                  while_ (bin Lt (ev i) (ev n))
                    [ set (Cil.var ca) (Cil.new_exp ~loc:loc0 (Lval (at (ev a) (ev i))));
                      set (Cil.var cb) (Cil.new_exp ~loc:loc0 (Lval (at (ev b) (ev i))));
                      if_ (bin Eq (ev res) (int 0))
                        [ if_ (bin Lt (ev ca) (ev cb)) [ set (Cil.var res) (int (-1)) ]
                            [ if_ (bin Gt (ev ca) (ev cb)) [ set (Cil.var res) (int 1) ] [] ] ]
                        [];
                      set (Cil.var i) (bin PlusA (ev i) (int 1)) ];
                  ret (Some (Cil.mkCast ~newt:rty (ev res))) ]
            | Strncmp _, [ a; b; n ] ->
                let uc = Cil_const.ucharType in
                let brk () = Cil.mkStmt ~valid_sid:true (Break loc0) in
                let i = local "i" (Cil.typeOf (ev n)) and res = local "res" Cil_const.intType in
                let ca = local "ca" uc and cb = local "cb" uc in
                [ set (Cil.var res) (int 0); set (Cil.var i) (int 0);
                  while_ (bin Lt (ev i) (ev n))
                    [ set (Cil.var ca) (Cil.new_exp ~loc:loc0 (Lval (at (ev a) (ev i))));
                      set (Cil.var cb) (Cil.new_exp ~loc:loc0 (Lval (at (ev b) (ev i))));
                      if_ (bin Ne (ev ca) (ev cb))
                        [ if_ (bin Lt (ev ca) (ev cb)) [ set (Cil.var res) (int (-1)) ]
                            [ set (Cil.var res) (int 1) ];
                          brk () ]
                        [];
                      if_ (bin Eq (ev ca) (int 0)) [ brk () ] [];
                      set (Cil.var i) (bin PlusA (ev i) (int 1)) ];
                  ret (Some (Cil.mkCast ~newt:rty (ev res))) ]
            | Strchr (last, _, _), [ s; c ] ->
                let brk () = Cil.mkStmt ~valid_sid:true (Break loc0) in
                let p = local "p" Cil_const.charConstPtrType and r = local "r" Cil_const.charConstPtrType in
                let ch = local "ch" Cil_const.charType in
                let cur () = Cil.new_exp ~loc:loc0 (Lval (Cil.mkMem ~addr:(ev p) ~off:NoOffset)) in
                [ set (Cil.var r) (Cil.mkCast ~newt:Cil_const.charConstPtrType (int 0));
                  set (Cil.var ch) (ev c);
                  set (Cil.var p) (ev s);
                  while_ (int 1)
                    [ if_ (bin Eq (cur ()) (ev ch))
                        ((set (Cil.var r) (ev p)) :: (if last then [] else [ brk () ]))
                        [];
                      if_ (bin Eq (cur ()) (int 0)) [ brk () ] [];
                      set (Cil.var p)
                        (Cil.new_exp ~loc:loc0 (BinOp (PlusPI, ev p, int 1, Cil.typeOf (ev p)))) ];
                  ret (Some (Cil.mkCast ~newt:rty (ev r))) ]
            | Memchr _, [ s; c; n ] ->
                let brk () = Cil.mkStmt ~valid_sid:true (Break loc0) in
                let uc = Cil_const.ucharType in
                let st = Cil.typeOf (ev s) in
                let i = local "i" (Cil.typeOf (ev n)) and r = local "r" st in
                [ set (Cil.var r) (Cil.mkCast ~newt:st (int 0)); set (Cil.var i) (int 0);
                  while_ (bin Lt (ev i) (ev n))
                    [ if_
                        (bin Eq
                           (Cil.mkCast ~newt:uc (Cil.new_exp ~loc:loc0 (Lval (at (ev s) (ev i)))))
                           (Cil.mkCast ~newt:uc (ev c)))
                        [ set (Cil.var r) (Cil.new_exp ~loc:loc0 (BinOp (PlusPI, ev s, ev i, st))); brk () ]
                        [];
                      set (Cil.var i) (bin PlusA (ev i) (int 1)) ];
                  ret (Some (Cil.mkCast ~newt:rty (ev r))) ]
            | _ -> assert false
          in
          fd.sbody.bstmts <- body;
          added := GFun (fd, loc0) :: !added;
          Globals.Functions.replace_by_definition (Cil.empty_funspec ()) fd loc0;
          Cfg.cfgFun fd;
          Hashtbl.replace helpers k fd.svar;
          fd.svar
    in
    let args_of = function
      | Scanf (_, ps) -> ps
      | Fgets (s, n) -> [ s; n ]
      | Atoi s -> [ s ]
      | Recv (_, b, len) -> [ b; len ]
      | Connect | Object_size _ -> []
      | Nondet_memory (_, p, n) -> [ p; n ]
      | Unsigned_overflow (_, _, a, b, r) -> [ a; b; r ]
      | Memcmp (_, _, a, b, n) | Strncmp (a, b, n) -> [ a; b; n ]
      | Strchr (_, s, c) -> [ s; c ]
      | Memchr (_, s, c, n) -> [ s; c; n ]
    in
    let calls = Hashtbl.create 8 in
    Hashtbl.iter
      (fun sid (f, p) ->
        let h = helper f p in
        let formals = match Ast_types.unroll_node h.vtype with
          | TFun (_, Some fs, _) -> List.map (fun (_, t, _) -> t) fs
          | _ -> []
        in
        let args = List.map2 (fun a t -> Cil.mkCast ~newt:t a) (args_of p) formals in
        Hashtbl.replace calls sid (h, args))
      plans;
    file.globals <- Defunc.insert_before_functions (List.rev !added) file.globals;
    (* 3: the calls replaced *)
    let rewrite =
      object (self)
        inherit Visitor.frama_c_inplace

        method! vinst i =
          match match self#current_stmt with Some s -> Hashtbl.find_opt calls s.sid | None -> None with
          | None -> Cil.SkipChildren
          | Some (h, args) -> (
              match i with
              | Call (r, _, _, loc) -> Cil.ChangeTo [ Call (r, Var h, args, loc) ]
              | Local_init (v, ConsInit (_, _, k), loc) ->
                  Cil.ChangeTo [ Local_init (v, ConsInit (h, args, k), loc) ]
              | _ -> Cil.SkipChildren)
      end
    in
    let helper_ids = Hashtbl.fold (fun _ vi acc -> vi.vid :: acc) helpers [] in
    List.iter
      (function
        | GFun (fd, _) when not (List.mem fd.svar.vid helper_ids) ->
            ignore (Visitor.visitFramacFunction rewrite fd)
        | _ -> ())
      file.globals;
    Fragment.mark_ast_changed ();
    Hashtbl.length plans
  end
