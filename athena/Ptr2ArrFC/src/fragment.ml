(* Detection of the constructs outside the supported fragment.

   The transformation is defined only on a fragment of normalised C: integer,
   enumeration, structure and fixed-size array types, pointers to these,
   functions with bodies (recursion included), allocation by malloc / alloca /
   calloc / variable-length arrays, and a fixed table of external functions.
   Everything else is reported here, and a program with any report is refused
   as a whole: a partial transformation would give the consumer a program whose
   meaning differs from the input's with nothing saying so.

   Contract: [check ()] reads the current project's AST and returns every
   occurrence of an unsupported construct it finds (an empty list means the
   later phases must not fail on this input). It does not modify the AST.
   With [~uninit] other than "keep" (see -ptr2arr-uninit) two more constructs
   are refused: a goto that jumps back over the declaration of a variable
   that starts uninitialised, from after it to a label of its block before
   it (C makes the value indeterminate again when the declaration is
   reached, the output where the block starts), and, with "nondet", such a
   variable holding a long double, for which there is no nondeterministic
   value to draw.

   Two checks of the fragment need the region partition and are made where the
   partition is built, not here: a float object stored in a region, and an
   ordered comparison of pointers into different regions. Until then a float
   reachable through a pointer or held in an address-taken variable is refused
   here, which is the conservative superset of the first. *)

open Cil_types

type issue = { kind : string; loc : Fileloc.t; detail : string }

let pretty_issue fmt i =
  Format.fprintf fmt "%a: %s: %s" Fileloc.pretty i.loc i.kind i.detail

(* External functions the transformation models (allocation and release). *)
let allocation_functions =
  [ "malloc"; "calloc"; "realloc"; "alloca"; "__builtin_alloca"; "__fc_vla_alloc" ]

(* External functions modelled as loops over the cells of a region: they
   read and write the memory their pointer arguments point to (and return
   their first argument, except strlen and strcmp). *)
let memory_functions = [ "memset"; "memcpy"; "memmove" ]

let string_functions = [ "strlen"; "strcmp"; "strcpy"; "strncpy"; "strcat" ]

(* atexit, whose argument is a function: modelled by a table of the
   registered functions, run at the ends of the execution that run them. *)
let atexit_function = "atexit"

let release_functions = [ "free"; "__fc_vla_free" ]

(* External functions that return a pointer to a fresh block of arbitrary
   contents: modelled as an allocation of arbitrary length. *)
let nondet_pointer_functions = [ "__VERIFIER_nondet_String" ]

(* Non-local control the transformation cannot follow. *)
let nonlocal_jump_functions =
  [ "setjmp"; "_setjmp"; "__sigsetjmp"; "sigsetjmp"; "longjmp"; "_longjmp";
    "siglongjmp"; "__longjmp_chk" ]

let is_modelled_external name =
  List.mem name allocation_functions
  || List.mem name release_functions
  || List.mem name nondet_pointer_functions
  || List.mem name memory_functions
  || List.mem name string_functions
  || name = atexit_function

(* Bit widths the C standard fixes for the exact-width integer typedefs; a
   typedef of one of these names with another width means the front end read
   the header differently from the compiler (it drops [__mode__] attributes,
   so a typedef of [int] with mode [QI] becomes 32 bits wide). *)
let std_integer_width name =
  let exact = [ 8; 16; 32; 64 ] in
  let rec find = function
    | [] -> None
    | w :: ws ->
        let n = string_of_int w in
        if name = "int" ^ n ^ "_t" || name = "uint" ^ n ^ "_t" then Some w
        else find ws
  in
  find exact

let is_defined vi =
  try Kernel_function.is_definition (Globals.Functions.get vi)
  with Not_found -> false

let rec strip_casts e =
  match e.enode with CastE (_, e') -> strip_casts e' | _ -> e

(* The function an argument of atexit names: a function designator (its
   address, possibly under casts). *)
let atexit_target e =
  match (strip_casts e).enode with
  | AddrOf (Var f, NoOffset) | StartOf (Var f, NoOffset) when Ast_types.is_fun f.vtype -> Some f
  | Lval (Var f, NoOffset) when Ast_types.is_fun f.vtype -> Some f
  | _ -> None

(* A string literal used as a pointer: [StartOf] of a literal's global array,
   possibly under casts. Since Frama-C 32 a literal is a global const array. *)
let is_string_literal_ptr e =
  match (strip_casts e).enode with
  | StartOf (Var vi, NoOffset) | AddrOf (Var vi, Index (_, NoOffset)) ->
      Ast_info.is_string_literal vi
  | _ -> false

let is_null_constant e =
  let e = Cil.constFold true (strip_casts e) in
  Cil.isZero e

(* The typedef of function numbers, once function pointers are replaced by
   them (set by Defunc): a cast between a function number and a data pointer
   is how a function pointer converted to void * and back reads after that,
   and the transformation gives it a value of its own (see Transform). *)
let fnid_typedef : string option ref = ref None

let is_fnid t =
  match (t.tnode, !fnid_typedef) with TNamed ti, Some n -> ti.tname = n | _ -> false

(* The typedef of the numbers of values that point to no object (set by
   NondetPointer): a nonzero integer drawn nondeterministically and
   converted to a pointer is such a value; the transformation gives a cast
   from it to a pointer the value it gives a function number's. *)
let nonobj_typedef : string option ref = ref None

let is_nonobj t =
  match (t.tnode, !nonobj_typedef) with TNamed ti, Some n -> ti.tname = n | _ -> false

(* What a type contains that the fragment excludes. [seen] guards against
   recursive structures. *)
type type_issue = Fun_ptr | Union | Va_list

let type_issues t =
  let seen = Hashtbl.create 8 in
  let acc = ref [] in
  let add k = if not (List.mem k !acc) then acc := k :: !acc in
  let rec go t =
    match Ast_types.unroll_node t with
    | TPtr t' -> if Ast_types.is_fun t' then add Fun_ptr else go t'
    | TArray (t', _) -> go t'
    | TFun (r, args, _) ->
        go r;
        Option.iter (List.iter (fun (_, t, _) -> go t)) args
    | TComp ci ->
        if not (Hashtbl.mem seen ci.ckey) then begin
          Hashtbl.add seen ci.ckey ();
          if not ci.cstruct then add Union;
          Option.iter (List.iter (fun fi -> go fi.ftype)) ci.cfields
        end
    | TBuiltin_va_list -> add Va_list
    | TVoid | TInt _ | TFloat _ | TEnum _ | TNamed _ -> ()
  in
  go t;
  List.rev !acc

let rec contains_float_seen seen t =
  match Ast_types.unroll_node t with
  | TFloat _ -> true
  | TArray (t', _) -> contains_float_seen seen t'
  | TComp ci ->
      if Hashtbl.mem seen ci.ckey then false
      else begin
        Hashtbl.add seen ci.ckey ();
        match ci.cfields with
        | None -> false
        | Some fs -> List.exists (fun fi -> contains_float_seen seen fi.ftype) fs
      end
  | _ -> false

let contains_float t = contains_float_seen (Hashtbl.create 4) t

(* A pointer type whose pointee holds a float: such a pointee lives in a
   region, and regions do not define the byte representation of floats. *)
let rec points_to_float t =
  match Ast_types.unroll_node t with
  | TPtr t' -> contains_float t' || points_to_float t'
  | TArray (t', _) -> points_to_float t'
  | _ -> false

let rec has_long_double seen t =
  match Ast_types.unroll_node t with
  | TFloat FLongDouble -> true
  | TArray (t', _) -> has_long_double seen t'
  | TComp ci ->
      (not (Hashtbl.mem seen ci.ckey))
      && begin
           Hashtbl.add seen ci.ckey ();
           List.exists (fun fi -> has_long_double seen fi.ftype)
             (Option.value ~default:[] ci.cfields)
         end
  | _ -> false

let check ?(uninit = "keep") () =
  let issues = ref [] in
  let report loc kind fmt =
    Format.kasprintf
      (fun detail -> issues := { kind; loc; detail } :: !issues)
      fmt
  in
  let check_type loc what t =
    List.iter
      (function
        | Fun_ptr -> report loc "function-pointer" "%s has a function pointer type" what
        | Union -> report loc "union" "%s involves a union type" what
        | Va_list -> report loc "va_list" "%s involves va_list" what)
      (type_issues t);
    if points_to_float t then
      report loc "float-in-region" "%s points to a floating-point object" what
  in
  (* the atexit arguments: function designators, not function pointers *)
  let designators = Hashtbl.create 4 and registered = ref [] in
  let check_call loc f args =
    if is_defined f then ()
    else if List.mem f.vname nonlocal_jump_functions then
      report loc "setjmp-longjmp" "call to %s" f.vname
    else if f.vname = atexit_function then (
      match args with
      | [ a ] -> (
          match atexit_target a with
          | Some g when is_defined g -> (
              let rec ids e =
                Hashtbl.replace designators e.eid ();
                match e.enode with CastE (_, e') -> ids e' | _ -> ()
              in
              ids a;
              registered := g :: !registered;
              match Ast_types.unroll_node g.vtype with
              | TFun (r, (None | Some []), false) when Ast_types.is_void r -> ()
              | _ -> report loc "atexit" "atexit registers %s, which is not a void function of no argument" g.vname)
          | _ ->
              report loc "atexit" "the argument of atexit is not a function the program defines")
      | _ -> report loc "atexit" "atexit with %d arguments" (List.length args))
    else if is_modelled_external f.vname then ()
    else begin
      (match Ast_types.unroll_node f.vtype with
       | TFun (r, _, _) when Ast_types.is_ptr r ->
           report loc "external-pointer" "external function %s returns a pointer"
             f.vname
       | _ -> ());
      (* A null argument gives the function nothing of the program's memory
         to read or write (time (NULL) returns the time and stores nothing). *)
      List.iter
        (fun a ->
          if Ast_types.is_ptr (Cil.typeOf a)
             && (not (is_string_literal_ptr a))
             && not (is_null_constant a)
          then
            report loc "external-pointer"
              "a pointer that is not a string literal is passed to external \
               function %s"
              f.vname)
        args
    end
  in
  let visitor =
    object
      inherit Visitor.frama_c_inplace

      method! vglob_aux g =
        (match g with
         | GAsm (_, loc) -> report loc "asm" "top-level assembly"
         | GType (ti, loc) -> (
             match std_integer_width ti.tname with
             | Some w
               when Ast_types.is_integral ti.ttype
                    && Cil.bitsSizeOf ti.ttype <> w ->
                 report loc "typedef-width"
                   "%s is read as %d bits wide (an attribute such as __mode__ \
                    was dropped)"
                   ti.tname (Cil.bitsSizeOf ti.ttype)
             | _ -> ())
         | GFun (fd, loc) -> (
             (match Ast_types.unroll_node fd.svar.vtype with
              | TFun (_, _, true) ->
                  report loc "variadic" "function %s is variadic" fd.svar.vname
              | _ -> ());
             match Ast_types.unroll_node fd.svar.vtype with
             | TFun (r, _, _) ->
                 check_type loc ("the return type of " ^ fd.svar.vname) r
             | _ -> ())
         | GVar (vi, _, loc) ->
             if not (Ast_info.is_string_literal vi) then
               check_type loc ("global " ^ vi.vname) vi.vtype
         | _ -> ());
        Cil.DoChildren

      method! vfunc fd =
        let loc = fd.svar.vdecl in
        List.iter
          (fun vi -> check_type loc ("parameter " ^ vi.vname) vi.vtype)
          fd.sformals;
        List.iter
          (fun vi -> check_type vi.vdecl ("local " ^ vi.vname) vi.vtype)
          fd.slocals;
        Cil.DoChildren

      method! vinst i =
        (match i with
         | Asm (_, _, _, loc) -> report loc "asm" "inline assembly"
         | Call (_, Mem _, _, loc) ->
             report loc "function-pointer" "call through a function pointer"
         | Call (_, Var f, args, loc) -> check_call loc f args
         | Local_init (_, ConsInit (f, args, _), loc) -> check_call loc f args
         | Set _ | Local_init (_, AssignInit _, _) | Skip _ | Code_annot _ -> ());
        Cil.DoChildren

      method! vexpr e =
        let loc = e.eloc in
        (match e.enode with
         | _ when Hashtbl.mem designators e.eid -> ()
         | AddrOf (Var vi, _) | StartOf (Var vi, _) ->
             if Ast_types.is_fun vi.vtype then
               report loc "function-pointer" "address of function %s" vi.vname
             else if
               (not (Ast_info.is_string_literal vi)) && contains_float vi.vtype
             then
               report loc "float-in-region"
                 "the address of %s, which holds a floating-point value, is \
                  taken"
                 vi.vname
         | CastE (t, e') ->
             let src = Cil.typeOf e' in
             if Ast_types.is_ptr t && Ast_types.is_integral src
                && not (is_null_constant e') && not (is_fnid src) && not (is_nonobj src)
             then report loc "int-pointer-cast" "integer cast to a pointer"
             else if
               Ast_types.is_integral t && Ast_types.is_ptr src
               && not (Ast_types.is_bool t) && not (is_fnid t)
             then report loc "int-pointer-cast" "pointer cast to an integer";
             check_type loc "a cast" t
         | SizeOf t | AlignOf (t, _) -> check_type loc "a sizeof operand" t
         | _ -> ());
        Cil.DoChildren
    end
  in
  Visitor.visitFramacFileSameGlobals visitor (Ast.get ());
  if uninit <> "keep" then
    List.iter
      (function
        | GFun (fd, _) ->
            List.iter
              (fun ((t : UninitTargets.target), g, _) ->
                report (Cil_datatype.Stmt.loc g) "uninit-backward-goto"
                  "this goto jumps back over the declaration of %s (%a), which C \
                   makes indeterminate again when it is reached"
                  t.var.vorig_name Fileloc.pretty t.var.vdecl)
              (UninitTargets.backward_gotos fd);
            if uninit = "nondet" then
              List.iter
                (fun (t : UninitTargets.target) ->
                  let ty =
                    match t.vla with
                    | Some _ -> Ast_types.direct_pointed_type t.var.vtype
                    | None -> t.var.vtype
                  in
                  if has_long_double (Hashtbl.create 4) ty then
                    report t.var.vdecl "uninit-long-double"
                      "%s starts uninitialised and holds a long double, which has no \
                       nondeterministic value to start with"
                      t.var.vorig_name)
                (UninitTargets.targets fd)
        | _ -> ())
      (Ast.get ()).globals;
  (* a function atexit registers that calls exit, directly or through the
     functions it calls: C leaves that undefined *)
  if !registered <> [] then begin
    let file = Ast.get () in
    let calls = Hashtbl.create 16 in
    List.iter
      (function
        | GFun (fd, _) ->
            let v =
              object
                inherit Visitor.frama_c_inplace

                method! vinst i =
                  (match i with
                   | Call (_, Var g, _, _) | Local_init (_, ConsInit (g, _, _), _) ->
                       Hashtbl.add calls fd.svar.vid g
                   | _ -> ());
                  Cil.SkipChildren
              end
            in
            ignore (Visitor.visitFramacFunction v fd)
        | _ -> ())
      file.globals;
    let seen = Hashtbl.create 16 in
    let rec reaches_exit g =
      if Hashtbl.mem seen g.vid then false
      else begin
        Hashtbl.add seen g.vid ();
        List.exists
          (fun h -> ((not (is_defined h)) && h.vname = "exit") || (is_defined h && reaches_exit h))
          (Hashtbl.find_all calls g.vid)
      end
    in
    List.iter
      (fun g ->
        Hashtbl.reset seen;
        if reaches_exit g then
          report g.vdecl "atexit" "%s, which atexit registers, calls exit" g.vname)
      (List.sort_uniq (fun a b -> compare a.vid b.vid) !registered)
  end;
  List.rev !issues

(* Tells Frama-C the input's AST was rewritten in place, keeping the
   untyped AST: Ast.mark_as_changed clears it with the states that depend
   on the AST, and the source map reads the input's statements and
   function extents from it (without it every entry loses its function and
   falls back to the position Frama-C gave the expression). *)
let mark_ast_changed () =
  let untyped =
    try Some (Ast.UntypedFiles.get ()) with Ast.NoUntypedAst | Ast.Bad_Initialization _ -> None
  in
  Ast.mark_as_changed ();
  Option.iter Ast.UntypedFiles.set untyped

(* The global variables of a function pointer type (a table of functions)
   that nothing refers to, removed from the input before it is checked and
   transformed: no function body and no other global's initialiser reads
   them, so the program means the same without them, and the function
   addresses their initialisers take are gone with them. Returns their
   names. *)
let drop_unused_function_tables () =
  let file = Ast.get () in
  let used = Hashtbl.create 64 in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vvrbl vi =
        Hashtbl.replace used vi.vid ();
        Cil.SkipChildren
    end
  in
  Visitor.visitFramacFileSameGlobals v file;
  let unused vi =
    vi.vglob
    && (not (Hashtbl.mem used vi.vid))
    && List.mem Fun_ptr (type_issues vi.vtype)
  in
  let dropped =
    List.filter_map
      (function GVar (vi, _, _) | GVarDecl (vi, _) when unused vi -> Some vi.vname | _ -> None)
      file.globals
  in
  if dropped <> [] then begin
    file.globals <-
      List.filter
        (function GVar (vi, _, _) | GVarDecl (vi, _) -> not (unused vi) | _ -> true)
        file.globals;
    mark_ast_changed ()
  end;
  List.sort_uniq compare dropped
