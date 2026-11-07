(* offsetof written the way C's own macro and the Linux kernel's container_of
   write it: the address of a member of a null pointer, converted to an
   integer, [(size_t) &((T * )0)->f.g[2]].  It reads no pointer value -- nothing
   is dereferenced, the expression is the member's offset -- so it is outside
   what the fragment excludes for casts between pointers and integers, which
   observe an address.

   Before anything else reads the program, each such expression is replaced by
   a read of a placeholder variable, declared nowhere, that the translation
   turns into the offset in the translated layout ([Transform.offset_bytes_in]):
   the layout a byte region uses for the same path, in which a pointer has
   become an index and, in safety mode, holds its shadow fields beside it
   (which is why the offset is computed there and not here).  To the analyses
   in between the placeholder is an integer variable, as the offset is a
   number to them.  So [(char * )p - offsetof(S, f)], container_of's step back
   from a member to the structure holding it, computes in the output the byte
   index a byte region gives the structure (the region is a byte region, since
   a pointer to a field of its cells, [&s->f], is used).  The translated
   program computes every size and offset in the translated layout, as it does
   for sizeof.

   A path with an index that is not a constant, or through a bit-field (which
   a byte region does not implement), is left as it is, and the fragment
   check then rejects it as a cast of a pointer to an integer. *)

open Cil_types

(* [Some (t, base, off)] when [e] is [(t) &(( base * )0) off] with [t] an
   integer type other than _Bool and [off] starting with a field. *)
let member_of_null e =
  match e.enode with
  | CastE (t, a) when Ast_types.is_integral t && not (Ast_types.is_bool t) -> (
      match a.enode with
      | (AddrOf (Mem p, (Field _ as off)) | StartOf (Mem p, (Field _ as off)))
        when Fragment.is_null_constant p -> (
          match Ast_types.unroll_node (Cil.typeOf p) with
          | TPtr base -> Some (t, base, off)
          | _ -> None)
      | _ -> None)
  | _ -> None

(* Replaces every offsetof of the program by a placeholder registered in
   [Transform.offsetof_placeholders]; the number replaced.  A path is replaced
   only when it can be laid out (tried on a scratch layout table, without the
   shadow fields, which change offsets but not whether a path can be laid
   out). *)
let run () =
  let layouts = Hashtbl.create 8 and replaced = ref 0 in
  let visitor =
    object
      inherit Visitor.frama_c_inplace

      method! vexpr e =
        match member_of_null e with
        | None -> Cil.DoChildren
        | Some (t, base, off) -> (
            let bytes =
              try Transform.offset_bytes_in layouts base off
              with Transform.Not_implemented _ -> None
            in
            match (bytes, Ast_types.unroll_node t) with
            | Some _, TInt _ ->
                incr replaced;
                let v =
                  Cil.makeGlobalVar (Printf.sprintf "__p2a_offsetof_%d" !replaced) t
                in
                Hashtbl.replace Transform.offsetof_placeholders v.vid (base, off);
                Cil.ChangeTo (Cil.evar ~loc:e.eloc v)
            | _ -> Cil.SkipChildren)
    end
  in
  Visitor.visitFramacFileSameGlobals visitor (Ast.get ());
  !replaced
