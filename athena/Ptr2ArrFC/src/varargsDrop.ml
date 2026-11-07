(* Variadic functions whose bodies never read their variable arguments: the
   stubs of the Linux driver tasks (printk, dev_err, _dev_info and the like
   are defined to do nothing, or to return a constant).  A user-defined
   variadic function is outside the fragment, since what a body reads
   through va_arg depends on the call.  A body that never starts the
   variable arguments reads none of them.

   Before the fragment check, such a function loses its "...", and every
   call of it its arguments after the named ones.  The extra arguments are
   expressions without side effects (the normalised program evaluates calls
   and assignments as instructions of their own), so dropping them changes
   nothing an execution does.

   A function qualifies when it has a body, its body names no va_list
   variable and calls none of the va_* builtins, and nothing takes its
   address (a function pointer to it would keep its variadic type).  Left as
   they are (and refused by the fragment check as before): every other
   variadic function. *)

open Cil_types

let va_builtins =
  [ "__builtin_va_start"; "__builtin_va_arg"; "__builtin_va_end"; "__builtin_va_copy";
    "__builtin_va_arg_pack"; "__builtin_va_arg_pack_len" ]

let rec mentions_va_list t =
  match Ast_types.unroll_node t with
  | TBuiltin_va_list -> true
  | TArray (t', _) | TPtr t' -> mentions_va_list t'
  | _ -> false

let reads_varargs fd =
  List.exists (fun v -> mentions_va_list v.vtype) (fd.sformals @ fd.slocals)
  ||
  let found = ref false in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vinst i =
        (match i with
         | Call (_, Var f, _, _) | Local_init (_, ConsInit (f, _, _), _) ->
             if List.mem f.vname va_builtins then found := true
         | _ -> ());
        Cil.SkipChildren
    end
  in
  ignore (Visitor.visitFramacFunction v fd);
  !found

let run () =
  let file = Ast.get () in
  let taken = Hashtbl.create 16 in
  let addr =
    object
      inherit Visitor.frama_c_inplace

      method! vexpr e =
        (match e.enode with
         | Lval (Var f, _) | AddrOf (Var f, _) | StartOf (Var f, _) when Ast_types.is_fun f.vtype ->
             Hashtbl.replace taken f.vid ()
         | _ -> ());
        Cil.DoChildren
    end
  in
  Visitor.visitFramacFileSameGlobals addr file;
  let dropped = Hashtbl.create 8 in
  List.iter
    (function
      | GFun (fd, _) -> (
          match Ast_types.unroll_node fd.svar.vtype with
          | TFun (r, args, true)
            when (not (Hashtbl.mem taken fd.svar.vid)) && not (reads_varargs fd) ->
              let n = match args with Some l -> List.length l | None -> 0 in
              Cil.update_var_type fd.svar (Cil_const.mk_tfun ~tattr:fd.svar.vtype.tattr r args false);
              Hashtbl.replace dropped fd.svar.vid n
          | _ -> ())
      | _ -> ())
    file.globals;
  if Hashtbl.length dropped > 0 then begin
    let rec take n = function x :: r when n > 0 -> x :: take (n - 1) r | _ -> [] in
    let rewrite =
      object
        inherit Visitor.frama_c_inplace

        method! vinst i =
          match i with
          | Call (r, (Var f as fv), args, loc) when Hashtbl.mem dropped f.vid ->
              Cil.ChangeTo [ Call (r, fv, take (Hashtbl.find dropped f.vid) args, loc) ]
          | Local_init (v, ConsInit (f, args, k), loc) when Hashtbl.mem dropped f.vid ->
              Cil.ChangeTo [ Local_init (v, ConsInit (f, take (Hashtbl.find dropped f.vid) args, k), loc) ]
          | _ -> Cil.SkipChildren
      end
    in
    Visitor.visitFramacFileSameGlobals rewrite file;
    Fragment.mark_ast_changed ()
  end;
  Hashtbl.length dropped
