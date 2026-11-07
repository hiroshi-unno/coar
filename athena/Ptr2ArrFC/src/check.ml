(* Static checks of an output program, run on the output re-read by Frama-C
   with the same front-end settings as the input.

   Reading the output at all is the first check: an output the front end cannot
   read is not one the checking tools, or a consumer using the same front end,
   can analyse. On the AST read back, the checks are:
   - no Frama-C-internal name (a [__fc_] or [__FC_] prefix) remains, since the
     output must be self-contained;
   - unless pointers are allowed (the identity output keeps them), no variable,
     parameter, return value or field has a pointer type, and no expression
     dereferences or takes an address, except the string literals passed to
     external functions and those functions' declarations.

   Contract: [run ~allow_pointers] reads the current project and returns the
   violations, one string each; it does not modify the AST. *)

open Cil_types

let internal_name n =
  let p s = String.length n >= String.length s && String.sub n 0 (String.length s) = s in
  p "__fc_" || p "__FC_"

let rec has_pointer seen t =
  match Ast_types.unroll_node t with
  | TPtr _ -> true
  | TArray (t', _) -> has_pointer seen t'
  | TComp ci ->
      if Hashtbl.mem seen ci.ckey then false
      else begin
        Hashtbl.add seen ci.ckey ();
        match ci.cfields with
        | None -> false
        | Some fs -> List.exists (fun fi -> has_pointer seen fi.ftype) fs
      end
  | _ -> false

let has_pointer t = has_pointer (Hashtbl.create 4) t

let run ~allow_pointers =
  let errs = ref [] in
  let err loc fmt =
    Format.kasprintf
      (fun s -> errs := Format.asprintf "%a: %s" Fileloc.pretty loc s :: !errs)
      fmt
  in
  let defined vi =
    try Kernel_function.is_definition (Globals.Functions.get vi)
    with Not_found -> false
  in
  let check_var loc what vi =
    (* A string literal is printed in place, as a literal; the front end gives
       its array an internal name when it reads the output back. *)
    if internal_name vi.vname && not (Ast_info.is_string_literal vi) then err loc "internal name %s (%s)" vi.vname what;
    if (not allow_pointers) && has_pointer vi.vtype
       && not (Ast_info.is_string_literal vi)
    then err loc "%s %s has a pointer type" what vi.vname
  in
  let visitor =
    object (self)
      inherit Visitor.frama_c_inplace

      method! vglob_aux g =
        (match g with
         | GVar (vi, _, loc) -> check_var loc "global" vi
         | GVarDecl (vi, loc) when not (Ast_types.is_fun vi.vtype) ->
             check_var loc "global" vi
         | GFunDecl (_, vi, loc) ->
             if internal_name vi.vname then err loc "internal name %s" vi.vname
         | GFun (fd, loc) -> (
             if internal_name fd.svar.vname then
               err loc "internal name %s" fd.svar.vname;
             List.iter (check_var loc "parameter") fd.sformals;
             List.iter (fun vi -> check_var vi.vdecl "local" vi) fd.slocals;
             match Ast_types.unroll_node fd.svar.vtype with
             | TFun (r, _, _) when (not allow_pointers) && has_pointer r ->
                 err loc "function %s returns a pointer" fd.svar.vname
             | _ -> ())
         | GCompTag (ci, loc) ->
             if not allow_pointers then
               Option.iter
                 (List.iter (fun fi ->
                      if has_pointer fi.ftype then
                        err loc "field %s.%s has a pointer type" ci.cname fi.fname))
                 ci.cfields
         | _ -> ());
        Cil.DoChildren

      method! vinst i =
        (match i with
         | Call (_, Var f, args, loc) when (not allow_pointers) && not (defined f) ->
             List.iter
               (fun a ->
                 (* a null argument (time (NULL)) passes nothing of the
                    program's memory, as the fragment check admits *)
                 if Ast_types.is_ptr (Cil.typeOf a)
                    && (not (Fragment.is_string_literal_ptr a))
                    && not (Fragment.is_null_constant a)
                 then err loc "a pointer is passed to %s" f.vname)
               args;
             (* the arguments are checked above; do not report the literal
                inside them again *)
             ()
         | _ -> ());
        Cil.DoChildren

      method! vexpr e =
        (if not allow_pointers then
           match e.enode with
           | StartOf (Var vi, _) when Ast_info.is_string_literal vi -> ()
           | AddrOf _ | StartOf _ -> err e.eloc "an address is taken"
           | _ -> ());
        Cil.DoChildren

      (* Dereferences are left-value hosts, which occur both inside expressions
         and as the target of an assignment. *)
      method! vlval lv =
        (match lv with
         | Mem _, _ when not allow_pointers ->
             let loc =
               match self#current_stmt with
               | Some s -> Cil_datatype.Stmt.loc s
               | None -> Fileloc.unknown
             in
             err loc "a dereference remains"
         | _ -> ());
        Cil.DoChildren
    end
  in
  Visitor.visitFramacFileSameGlobals visitor (Ast.get ());
  List.rev !errs
