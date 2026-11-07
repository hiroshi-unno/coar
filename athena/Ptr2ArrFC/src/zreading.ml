(* A test of --wrap-integers: an output rewritten to run in the reading where
   integers are mathematical integers, approximated by 128-bit arithmetic.

   Every integer type of the program becomes __int128 (except _Bool, the
   prototypes of external functions, whose calls convert their arguments and
   results, and main's result), every conversion between integer types is
   dropped (the identity of that reading), and the body of each reduction
   function __p2a_wrap_k (and __p2a_wrapnn_k) becomes red_k, the reduction into k's range modulo
   2^w. Run on the same inputs, this program must behave as the input does as
   long as no value leaves the 128-bit range: a place where the output relies
   on C's wrap-around without a reduction shows up as a different value.
   (Formatted output of a widened value is not comparable: printf receives an
   __int128 where its format names an int.)

   Contract: [run ()] rewrites the current project in place; the project
   holds an output of the transformation read back. *)

open Cil_types

let i128 = Cil_const.mk_tint IInt128

(* __p2a_wrap_k, and __p2a_wrapnn_k (an unsigned k whose argument the
   transformation showed non-negative): both are red_k here *)
let is_wrap_name n =
  String.starts_with ~prefix:"__p2a_wrap_" n || String.starts_with ~prefix:"__p2a_wrapnn_" n

(* the integer types widened; pointers (to the literals given to external
   functions) and named and composite types (rewritten in place) kept *)
let rec widen t =
  match t.tnode with
  | TInt IBool -> t
  | TInt _ | TEnum _ -> i128
  | TArray (t', len) -> Cil_const.mk_tarray (widen t') len
  | TFun (r, args, va) ->
      Cil_const.mk_tfun (widen r)
        (Option.map (List.map (fun (n, t, a) -> (n, widen t, a))) args)
        va
  | _ -> t

let is_integral_not_bool t =
  match Ast_types.unroll_node t with
  | TInt IBool -> false
  | TInt _ | TEnum _ -> true
  | _ -> false

(* red_k(v) for kind (w, signed): v modulo 2^w, into [0, 2^w) or, signed,
   into [-2^(w-1), 2^(w-1)). *)
let reduction_body fd v ~width ~signed =
  let loc = Fileloc.unknown in
  let mk n = Cil.new_exp ~loc n in
  (* 2^k as ((__int128)1 << k): C has no literal of a 128-bit integer *)
  let pow2 k = mk (BinOp (Shiftlt, mk (CastE (i128, Cil.one ~loc)), Cil.integer ~loc k, i128)) in
  let c n = mk (CastE (i128, Cil.integer ~loc n)) in
  let m = pow2 width in
  let r = Cil.makeLocalVar fd "r" i128 in
  let bin op a b = mk (BinOp (op, a, b, i128)) in
  let set e = Cil.mkStmtOneInstr ~valid_sid:true (Set (Cil.var r, e, loc)) in
  let ifs cond s = Cil.mkStmt ~valid_sid:true (If (cond, Cil.mkBlock [ s ], Cil.mkBlock [], loc)) in
  let half = pow2 (width - 1) in
  [ set (bin Mod (Cil.evar v) m);
    ifs (bin Lt (Cil.evar r) (c 0)) (set (bin PlusA (Cil.evar r) (pow2 width))) ]
  @ (if signed then
       [ ifs (bin Ge (Cil.evar r) half) (set (bin MinusA (Cil.evar r) (pow2 width))) ]
     else [])
  @ [ Cil.mkStmt ~valid_sid:true (Return (Some (Cil.evar r), loc)) ]

let run () =
  let file = Ast.get () in
  let reductions = ref [] in
  List.iter
    (function
      | GType (ti, _) -> ti.ttype <- widen ti.ttype
      | GCompTag (ci, _) ->
          Option.iter
            (List.iter (fun fi ->
                 fi.ftype <- widen fi.ftype;
                 fi.fsize_in_bits <- None;
                 fi.foffset_in_bits <- None))
            ci.cfields
      | GVar (vi, _, _) when not (Ast_info.is_string_literal vi) ->
          Cil.update_var_type vi (widen vi.vtype)
      | GFun (fd, _) ->
          let name = fd.svar.vname in
          let kind =
            if is_wrap_name name then
              match Ast_types.unroll_node (Cil.getReturnType fd.svar.vtype) with
              | TInt ik -> Some (Cil.bitsSizeOfInt ik, Cil.isSigned ik)
              | _ -> None
            else None
          in
          List.iter (fun v -> Cil.update_var_type v (widen v.vtype)) fd.sformals;
          List.iter (fun v -> Cil.update_var_type v (widen v.vtype)) fd.slocals;
          if name <> "main" then
            Cil.setReturnType fd (widen (Cil.getReturnType fd.svar.vtype));
          Cil.setFormals fd fd.sformals;
          Cil.unsafeSetFormalsDecl fd.svar fd.sformals;
          Option.iter (fun k -> reductions := (fd, k) :: !reductions) kind
      | _ -> ())
    file.globals;
  let visitor =
    object
      inherit Visitor.frama_c_inplace

      method! vexpr e =
        match e.enode with
        | CastE (t, a) when is_integral_not_bool t && is_integral_not_bool (Cil.typeOf a) ->
            Cil.ChangeDoChildrenPost (a, fun a -> a)
        | _ -> Cil.DoChildren
    end
  in
  Visitor.visitFramacFileSameGlobals visitor file;
  (* the reductions' bodies last: their own conversions to __int128 stay *)
  List.iter
    (fun (fd, (width, signed)) ->
      match fd.sformals with
      | [ v ] -> fd.sbody.bstmts <- reduction_body fd v ~width ~signed
      | _ -> ())
    !reductions
