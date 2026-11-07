(* The difference of two pointers written through integers, [(long)p -
   (long)q], as string helpers write a length (`(long)s - (long)str`).  Both
   operands are converted to one integer type at least as wide as a pointer
   (so no address is truncated), and the pointers point to one type; the
   value is then the distance of p from q in bytes.

   Before the fragment check, which would refuse the two casts, each such
   expression is rewritten as that distance computed with pointer arithmetic:
   [(t) ((p -ₚₚ q) * sizeof(T))], with T the type pointed to (the factor left
   out where T is one byte, a character type or void).  A pointer difference
   is translated as the difference of indices divided by the element's cells
   (E-Diff), and sizeof as the size of the translated type, so the result is
   the distance in the translated layout, as every size and offset the
   translated program computes is.

   The rewriting is exact when p and q point into one object, which is when C
   defines [p - q]; on two different objects the input computes a difference
   of addresses, which the translation has no way to reproduce (a pointer is
   an index into a region), as it has none for any other observation of an
   address.  Operands of other shapes (one side not a cast of a pointer,
   integers narrower than a pointer, pointers to different types) are left as
   they are, and the fragment check refuses them as before. *)

open Cil_types

(* [Some p] when [e] is a pointer converted to an integer type at least as
   wide as a pointer; the integer type is returned beside it. *)
let pointer_as_integer e =
  match e.enode with
  | CastE (t, p)
    when Ast_types.is_integral t && (not (Ast_types.is_bool t))
         && Ast_types.is_ptr (Cil.typeOf p)
         && Cil.bitsSizeOf t >= Cil.bitsSizeOf Cil_const.voidPtrType ->
      Some (t, p)
  | _ -> None

let pointee p =
  match Ast_types.unroll_node (Cil.typeOf p) with
  | TPtr t -> Some (Ast_types.remove_qualifiers (Ast_types.unroll t))
  | _ -> None

let one_byte t =
  Ast_types.is_void t || (Ast_types.is_integral t && Cil.bitsSizeOf t = 8)

(* Rewrites every such difference; the number rewritten. *)
let run () =
  let rewritten = ref 0 in
  let visitor =
    object
      inherit Visitor.frama_c_inplace

      method! vexpr e =
        match e.enode with
        | BinOp (MinusA, a, b, t) -> (
            match (pointer_as_integer a, pointer_as_integer b) with
            | Some (ta, p), Some (tb, q)
              when Cil_datatype.Typ.equal (Ast_types.unroll ta) (Ast_types.unroll tb) -> (
                match (pointee p, pointee q) with
                | Some tp, Some tq when Cil_datatype.Typ.equal tp tq ->
                    incr rewritten;
                    let loc = e.eloc in
                    let diff =
                      Cil.new_exp ~loc (BinOp (MinusPP, p, q, (Machine.ptrdiff_type ())))
                    in
                    let bytes =
                      if one_byte tp then diff
                      else
                        Cil.new_exp ~loc
                          (BinOp
                             ( Mult,
                               diff,
                               Cil.mkCast ~newt:(Machine.ptrdiff_type ())
                                 (Cil.new_exp ~loc (SizeOf tp)),
                               (Machine.ptrdiff_type ()) ))
                    in
                    Cil.ChangeTo (Cil.mkCast ~newt:t bytes)
                | _ -> Cil.DoChildren)
            | _ -> Cil.DoChildren)
        | _ -> Cil.DoChildren
    end
  in
  Visitor.visitFramacFileSameGlobals visitor (Ast.get ());
  if !rewritten > 0 then Fragment.mark_ast_changed ();
  !rewritten
