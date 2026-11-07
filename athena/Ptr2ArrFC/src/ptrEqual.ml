(* The equality of two pointers written through integers, [(unsigned long)p
   == (unsigned long)q] (and [!=]), as CIL prints a pointer comparison in
   the Linux driver tasks, among them the test against NULL [(unsigned
   long)p != (unsigned long)((void * )0)].  Both operands are pointers
   converted to one integer type at least as wide as a pointer, or one is a
   pointer so converted and the other the integer constant 0.

   Before the fragment check, which would refuse the casts, each such
   comparison becomes the comparison of the pointers themselves, both cast
   to [void *] (the constant 0 becoming the null pointer).  GCC converts a
   pointer to an integer at least as wide as the pointer by keeping its
   address's bits, so two such integers are equal exactly when the pointers
   are (C leaves the conversion implementation-defined, C11 6.3.2.3p6, and
   this relies on GCC's).  The translation of a pointer comparison then
   applies: pointers into different regions are equal only when both are
   NULL.  The null pointer constant converted to an integer, which CIL
   writes on the other side of an integer compared with NULL
   [(unsigned long)x == (unsigned long)((void * )0)], becomes the integer 0,
   its value under GCC.  Operands of any other shape are left as they are
   and refused as before. *)

open Cil_types

let rec is_zero e =
  match e.enode with
  | Const (CInt64 (z, _, _)) -> Z.equal z Z.zero
  | CastE (t, e') when Ast_types.is_integral t -> is_zero e'
  | _ -> false

let void_ptr p = Cil.mkCast ~newt:Cil_const.voidPtrType p

(* Rewrites every such comparison; the number rewritten. *)
let run () =
  let rewritten = ref 0 in
  let visitor =
    object
      inherit Visitor.frama_c_inplace

      method! vexpr e =
        match e.enode with
        | BinOp (((Eq | Ne) as op), a, b, t) -> (
            let ok_pair =
              match (Ptrdiff.pointer_as_integer a, Ptrdiff.pointer_as_integer b) with
              | Some (ta, p), Some (tb, q)
                when Cil_datatype.Typ.equal (Ast_types.unroll ta) (Ast_types.unroll tb) ->
                  Some (p, q)
              | Some (_, p), None when is_zero b -> Some (p, Cil.zero ~loc:b.eloc)
              | None, Some (_, q) when is_zero a -> Some (Cil.zero ~loc:a.eloc, q)
              | _ -> None
            in
            match ok_pair with
            | Some (p, q) ->
                incr rewritten;
                let loc = e.eloc in
                Cil.ChangeTo (Cil.new_exp ~loc (BinOp (op, void_ptr p, void_ptr q, t)))
            | None -> Cil.DoChildren)
        | CastE (t, e') when Ast_types.is_integral t && Fragment.is_null_constant e'
                             && Ast_types.is_ptr (Cil.typeOf e') ->
            (* the null pointer converted to an integer: 0 under GCC *)
            incr rewritten;
            Cil.ChangeTo (Cil.mkCast ~newt:t (Cil.zero ~loc:e.eloc))
        | _ -> Cil.DoChildren
    end
  in
  Visitor.visitFramacFileSameGlobals visitor (Ast.get ());
  if !rewritten > 0 then Fragment.mark_ast_changed ();
  !rewritten
