(* Function pointers removed by defunctionalization, before the rest of the
   transformation sees the program.

   A function pointer value becomes an integer, the function number: 0 for
   NULL and 1, 2, ... for the functions whose address the program takes, in
   the order of their first declaration. A call through a function pointer
   becomes a chain of tests of the number, each branch a direct call of one
   candidate: an address-taken function whose type is compatible with the
   type the call is made at (C11 6.7.6.3p15) and that takes as many
   arguments as the call passes. The last branch calls
   __p2a_bad_function_call(), defined as abort(): calling through NULL,
   through an uninitialised value or at an incompatible type is undefined
   in C (C11 6.3.2.3p8), and the safety modes replace that call by their
   invalid-dereference marker. Every function pointer type becomes the
   typedef __p2a_fnid of int, so the program left has no function pointer,
   and the points-to analysis, the regions and the checks treat function
   numbers as the integers they are; the typedef name tells
   --uninit=nondet to start such a variable at NULL (0), as it does a
   pointer.

   Why this preserves meaning, for an execution with no undefined
   behaviour: the program makes a function pointer value only from the
   address of a function, from the null constant and by copying or casting
   between function pointer types (the forms [check] refuses are the other
   ways), so every value is NULL or the address of an address-taken
   function. Numbers are distinct and never 0, so equality tests keep their
   truth values. A cast to or from an integer type is the number converted;
   a cast to or from a data pointer is a cast to or from the number's type,
   which the transformation writes as minus the number (a data pointer is a
   region index, never negative, so a function never equals an object).
   C makes the integer value implementation-defined and the conversion to a
   data pointer undefined, so this assumes the program uses such a value
   only for equality, for a test against NULL and to convert it back;
   [check] refuses the uses it can see that read more (an ordered
   comparison, arithmetic or a bit operation on the value, the value passed
   to an external function, a conversion to an integer narrower than a
   pointer), and a value stored in an integer variable is not followed. A
   call goes through the address of a function of a
   compatible type, which is among the candidates, and exactly one branch
   matches it. The arguments are converted to the callee's parameter types,
   as the call converts them.

   The functions atexit registers are function designators the
   transformation models by name; they and atexit's declaration are left
   alone.

   Contract: [check ()] reads the current project and returns the
   occurrences of the forms that stay unsupported (a cast between a function
   pointer and a type that is neither an integer nor a pointer, a function
   pointer given to or returned by an
   external function, a function pointer to a variadic function, an ordered
   comparison or a difference of function pointers). [run ()] rewrites the
   current project in place when the program uses function pointers and
   [check ()] found nothing, and does nothing otherwise; the statement of
   each indirect call is kept (its kind becomes a block), so statements keep
   their identities. *)

open Cil_types

type result = {
  function_ids : (string * int * bool) list;  (** name, number, has a body *)
  temps : (string * string) list;  (** (function, local): the branch temporaries *)
  fnid_type : string option;  (** the typedef of function numbers *)
  bad_call : string option;  (** the function an invalid call calls *)
}

let none = { function_ids = []; temps = []; fnid_type = None; bad_call = None }

let loc0 = Fileloc.unknown

let is_fn_ptr t =
  match Ast_types.unroll_node t with TPtr t' -> Ast_types.is_fun t' | _ -> false

(* The function types reachable from [t] as the pointee of a function
   pointer: inside arrays, structure fields, pointers and function types. *)
let fn_pointees t =
  let seen = Hashtbl.create 8 and acc = ref [] in
  let rec go t =
    match Ast_types.unroll_node t with
    | TPtr t' ->
        if Ast_types.is_fun t' then begin
          acc := t' :: !acc;
          go t'
        end
        else go t'
    | TArray (t', _) -> go t'
    | TFun (r, args, _) ->
        go r;
        Option.iter (List.iter (fun (_, t, _) -> go t)) args
    | TComp ci ->
        if not (Hashtbl.mem seen ci.ckey) then begin
          Hashtbl.add seen ci.ckey ();
          Option.iter (List.iter (fun fi -> go fi.ftype)) ci.cfields
        end
    | _ -> ()
  in
  go t;
  !acc

let is_variadic t =
  match Ast_types.unroll_node t with TFun (_, _, va) -> va | _ -> false

(* A function type with a function pointer among its result and parameters. *)
let fun_type_has_fn_ptr t =
  match Ast_types.unroll_node t with
  | TFun (r, args, _) ->
      fn_pointees r <> []
      || List.exists (fun (_, t, _) -> fn_pointees t <> []) (Option.value ~default:[] args)
  | _ -> false

let is_atexit f = f.vname = Fragment.atexit_function && not (Fragment.is_defined f)

(* The expressions of atexit's argument: a function designator under casts. *)
let designators file =
  let ids = Hashtbl.create 4 in
  let rec mark e =
    Hashtbl.replace ids e.eid ();
    match e.enode with CastE (_, e') -> mark e' | _ -> ()
  in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vinst i =
        (match i with
         | Call (_, Var f, [ a ], _) | Local_init (_, ConsInit (f, [ a ], _), _)
           when is_atexit f && Fragment.atexit_target a <> None ->
             mark a
         | _ -> ());
        Cil.SkipChildren
    end
  in
  Visitor.visitFramacFileSameGlobals v file;
  ids

(* Whether the program uses function pointers: the fragment check reports a
   function pointer somewhere. *)
let uses_fn_ptrs () =
  List.exists (fun (i : Fragment.issue) -> i.kind = "function-pointer") (Fragment.check ())

(* A function pointer's value converted to an integer or a data pointer:
   a cast from a function pointer type, possibly under further casts to
   types that are not function pointers.  Function numbers replace the
   addresses such a value holds, so only the uses that do not read an
   address's magnitude keep their meaning (see [check]). *)
let rec fn_value e =
  match e.enode with
  | CastE (t, e') ->
      if is_fn_ptr (Cil.typeOf e') then not (is_fn_ptr t) else (not (is_fn_ptr t)) && fn_value e'
  | _ -> false

let check () =
  let file = Ast.get () in
  let des = designators file in
  let issues = ref [] in
  let report loc kind fmt =
    Format.kasprintf (fun detail -> issues := { Fragment.kind; loc; detail } :: !issues) fmt
  in
  let check_variadic loc what t =
    if List.exists is_variadic (fn_pointees t) then
      report loc "function-pointer-variadic" "%s points to a variadic function" what
  in
  let v =
    object (self)
      inherit Visitor.frama_c_inplace

      method! vglob_aux g =
        match g with
        | GFunDecl _ | GVarDecl _ -> Cil.SkipChildren
        | _ -> Cil.DoChildren

      method! vvdec vi =
        if not (Ast_types.is_fun vi.vtype) then
          check_variadic vi.vdecl ("the type of " ^ vi.vname) vi.vtype;
        Cil.DoChildren

      method! vfunc fd =
        (match Ast_types.unroll_node fd.svar.vtype with
         | TFun (r, _, _) -> check_variadic fd.svar.vdecl ("the return type of " ^ fd.svar.vname) r
         | _ -> ());
        Cil.DoChildren

      method! vinst i =
        let external_call loc f args =
          if (not (Fragment.is_defined f)) && not (is_atexit f) then
            if fun_type_has_fn_ptr f.vtype
               || List.exists (fun a -> fn_pointees (Cil.typeOf a) <> []) args
            then
              report loc "function-pointer-external"
                "a function pointer is passed to or returned by external function %s" f.vname
        in
        (match i with
         | Call (_, Var f, args, loc) | Local_init (_, ConsInit (f, args, _), loc) ->
             external_call loc f args;
             if (not (Fragment.is_defined f)) && List.exists fn_value args then
               report loc "function-pointer-value"
                 "the value of a function pointer converted to another type is passed to \
                  external function %s (it would see a function number, not an address)"
                 f.vname
         | Call (_, Mem e, _, loc) ->
             check_variadic loc "a call through a function pointer" (Cil.typeOf e)
         | _ -> ());
        Cil.DoChildren

      method! vexpr e =
        let loc = e.eloc in
        if Hashtbl.mem des e.eid then Cil.SkipChildren
        else begin
          (match e.enode with
           | CastE (t, e') ->
               let src = Cil.typeOf e' in
               if is_fn_ptr t <> is_fn_ptr src then begin
                 (* to and from integers and data pointers: function numbers *)
                 let other = if is_fn_ptr t then src else t in
                 let ok = Ast_types.is_integral other || Ast_types.is_ptr other in
                 if not ok then
                   report loc "function-pointer-cast"
                     "a cast between a function pointer and %a"
                     Cil_datatype.Typ.pretty other
                 else if
                   is_fn_ptr src && Ast_types.is_integral t && (not (Ast_types.is_bool t))
                   && Cil.bitsSizeOf t < Cil.bitsSizeOf Cil_const.voidPtrType
                 then
                   (* an address would lose bits there, a small function
                      number would not *)
                   report loc "function-pointer-value"
                     "a function pointer converted to %a, narrower than a pointer"
                     Cil_datatype.Typ.pretty t
               end
               else if
                 fn_value e' && Ast_types.is_integral t && (not (Ast_types.is_bool t))
                 && Cil.bitsSizeOf t < Cil.bitsSizeOf Cil_const.voidPtrType
               then
                 report loc "function-pointer-value"
                   "a function pointer's value converted to %a, narrower than a pointer"
                   Cil_datatype.Typ.pretty t
               else if fn_pointees t <> [] || fn_pointees src <> [] then
                 check_variadic loc "a cast" t
           | BinOp ((Lt | Gt | Le | Ge | MinusPP), e1, _, _) when is_fn_ptr (Cil.typeOf e1) ->
               report loc "function-pointer-compare"
                 "an ordered comparison or a difference of function pointers"
           (* a function pointer's value converted to an integer or a data
              pointer is a function number, not an address: what an ordered
              comparison, arithmetic or a bit operation computes from it
              differs from the input's (only equality, tests against NULL
              and converting it back keep their meaning) *)
           | BinOp
               ( ( Lt | Gt | Le | Ge | PlusA | MinusA | Mult | Div | Mod | Shiftlt | Shiftrt
                 | BAnd | BXor | BOr | PlusPI | MinusPI | MinusPP ),
                 e1, e2, _ )
             when fn_value e1 || fn_value e2 ->
               report loc "function-pointer-value"
                 "the value of a function pointer converted to another type is used in an \
                  ordered comparison or in arithmetic (a function number is not an address)"
           | UnOp ((Neg | BNot), e1, _) when fn_value e1 ->
               report loc "function-pointer-value"
                 "the value of a function pointer converted to another type is used in \
                  arithmetic (a function number is not an address)"
           | AddrOf (Var f, NoOffset) | StartOf (Var f, NoOffset) when Ast_types.is_fun f.vtype ->
               if is_variadic f.vtype then
                 report loc "function-pointer-variadic" "the address of variadic function %s"
                   f.vname
               else if (not (Fragment.is_defined f)) && fun_type_has_fn_ptr f.vtype then
                 report loc "function-pointer-external"
                   "the address of external function %s, which takes or returns a function \
                    pointer"
                   f.vname
           | _ -> ());
          ignore self;
          Cil.DoChildren
        end
    end
  in
  Visitor.visitFramacFileSameGlobals v file;
  List.rev !issues

(* A name no global of [file] has, from [base]. *)
let fresh_global_name file base =
  let used = Hashtbl.create 64 in
  let note n = Hashtbl.replace used n () in
  List.iter
    (function
      | GVar (vi, _, _) | GVarDecl (vi, _) | GFunDecl (_, vi, _) -> note vi.vname
      | GFun (fd, _) -> note fd.svar.vname
      | GType (ti, _) -> note ti.tname
      | GEnumTag (ei, _) | GEnumTagDecl (ei, _) ->
          List.iter (fun it -> note it.einame) ei.eitems
      | _ -> ())
    file.globals;
  let rec go k =
    let n = if k = 0 then base else Printf.sprintf "%s_%d" base k in
    if Hashtbl.mem used n then go (k + 1) else n
  in
  go 0

(* [g] inserted right before the first function of [globals] (after the
   types and the variables declared before it). *)
let insert_before_functions gs globals =
  let rec go = function
    | [] -> gs
    | (GFun _ | GFunDecl _) :: _ as rest -> gs @ rest
    | g :: rest -> g :: go rest
  in
  go globals

let noreturn = [ ("noreturn", []) ]

let run () =
  if not (uses_fn_ptrs ()) then none
  else begin
    let file = Ast.get () in
    let des = designators file in
    (* --- the analysis, on the types before the rewrite --- *)
    let taken = Hashtbl.create 16 in
    let calls = ref [] in
    let collect =
      object (self)
        inherit Visitor.frama_c_inplace

        method! vexpr e =
          if Hashtbl.mem des e.eid then Cil.SkipChildren
          else begin
            (match e.enode with
             | AddrOf (Var f, NoOffset) | StartOf (Var f, NoOffset) when Ast_types.is_fun f.vtype ->
                 Hashtbl.replace taken f.vid f
             | _ -> ());
            Cil.DoChildren
          end

        method! vstmt_aux s =
          (match (s.skind, self#current_func) with
           | Instr (Call (_, Mem e, args, _)), Some fd -> (
               match Ast_types.unroll_node (Cil.typeOf e) with
               | TPtr phi -> calls := (s, fd, phi, List.length args) :: !calls
               | _ -> ())
           | _ -> ());
          Cil.DoChildren
      end
    in
    Visitor.visitFramacFileSameGlobals collect file;
    (* numbers in the order of first declaration *)
    let ids = Hashtbl.create 16 and order = ref [] in
    let number vi =
      if Hashtbl.mem taken vi.vid && not (Hashtbl.mem ids vi.vid) then begin
        Hashtbl.add ids vi.vid (Hashtbl.length ids + 1);
        order := vi :: !order
      end
    in
    List.iter
      (function GFun (fd, _) -> number fd.svar | GFunDecl (_, vi, _) -> number vi | _ -> ())
      file.globals;
    Hashtbl.iter (fun _ vi -> number vi) taken;
    let functions = List.rev !order in
    let id vi = Hashtbl.find ids vi.vid in
    let arity_ok f n =
      match Ast_types.unroll_node f.vtype with
      | TFun (_, Some ps, false) -> List.length ps = n
      | TFun (_, None, false) -> true
      | _ -> false
    in
    let calls =
      List.rev_map
        (fun (s, fd, phi, n) ->
          let cands =
            List.filter
              (fun f -> arity_ok f n && Cil.areCompatibleTypes f.vtype phi)
              functions
          in
          (s, fd, cands))
        !calls
    in
    (* --- the type of function numbers --- *)
    let tname = fresh_global_name file "__p2a_fnid" in
    let ti = { torig_name = tname; tname; ttype = Cil_const.intType; treferenced = true } in
    let fnid = Cil_const.mk_tnamed ti in
    Fragment.fnid_typedef := Some tname;
    (* --- expressions and types --- *)
    let rewrite =
      object (self)
        inherit Visitor.frama_c_inplace

        method! vglob_aux g =
          match g with
          | GFunDecl (_, vi, _) when is_atexit vi -> Cil.SkipChildren
          | _ -> Cil.DoChildren

        method! vexpr e =
          if Hashtbl.mem des e.eid then Cil.SkipChildren
          else
            match e.enode with
            | (AddrOf (Var f, NoOffset) | StartOf (Var f, NoOffset))
              when Ast_types.is_fun f.vtype ->
                Cil.ChangeTo (Cil.new_exp ~loc:e.eloc (CastE (fnid, Cil.integer ~loc:e.eloc (id f))))
            | CastE (t, e') when is_fn_ptr t ->
                (* a cast between function pointer types or of the null
                   constant keeps the number; from an integer, the integer
                   is the number; from a data pointer, the transformation
                   reads the number back from the pointer's value *)
                let e'' = Visitor.visitFramacExpr (self :> Visitor.frama_c_visitor) e' in
                Cil.ChangeTo (Cil.new_exp ~loc:e.eloc (CastE (fnid, e'')))
            | _ -> Cil.DoChildren

        method! vtype t =
          match t.tnode with
          | TPtr t' when Ast_types.is_fun t' -> Cil.ChangeTo fnid
          | _ -> Cil.DoChildren
      end
    in
    Visitor.visitFramacFileSameGlobals rewrite file;
    file.globals <- GType (ti, loc0) :: file.globals;
    (* --- the invalid call --- *)
    let bad =
      if calls = [] then None
      else begin
        let decls = ref [] in
        let abort_vi =
          match
            List.find_map
              (function
                | GFun (fd, _) when fd.svar.vname = "abort" -> Some fd.svar
                | GFunDecl (_, vi, _) when vi.vname = "abort" -> Some vi
                | _ -> None)
              file.globals
          with
          | Some vi -> vi
          | None ->
              let t = Cil_const.mk_tfun ~tattr:noreturn Cil_const.voidType (Some []) false in
              let vi = Cil.makeGlobalVar "abort" t in
              Cil.setFormalsDecl vi t;
              let spec = Cil.empty_funspec () in
              decls := [ GFunDecl (spec, vi, loc0) ];
              Globals.Functions.replace_by_declaration spec vi loc0;
              vi
        in
        let fd = Cil.emptyFunction (fresh_global_name file "__p2a_bad_function_call") in
        Cil.update_var_type fd.svar
          (Cil_const.mk_tfun ~tattr:noreturn Cil_const.voidType (Some []) false);
        fd.sbody.bstmts <-
          [ Cil.mkStmtOneInstr ~valid_sid:true (Call (None, Var abort_vi, [], loc0));
            Cil.mkStmt ~valid_sid:true (Return (None, loc0)) ];
        file.globals <- insert_before_functions (!decls @ [ GFun (fd, loc0) ]) file.globals;
        Globals.Functions.replace_by_definition (Cil.empty_funspec ()) fd loc0;
        Some fd.svar
      end
    in
    (* --- the calls --- *)
    let temps = ref [] and changed = Hashtbl.create 8 in
    List.iter
      (fun (s, fd, cands) ->
        match s.skind with
        | Instr (Call (ret, Mem e, args, loc)) ->
            let pre, sel =
              match e.enode with
              | Lval (Var _, NoOffset) -> ([], e)
              | _ ->
                  let t = Cil.makeTempVar fd ~name:"__p2a_fn" fnid in
                  temps := (fd.svar.vname, t.vname) :: !temps;
                  ( [ Cil.mkStmtOneInstr ~valid_sid:true (Set (Cil.var t, e, loc)) ],
                    Cil.evar ~loc t )
            in
            let branch f =
              let args' =
                match Ast_types.unroll_node f.vtype with
                | TFun (_, Some ps, _) ->
                    List.map2 (fun a (_, t, _) -> Cil.mkCast ~newt:t a) args ps
                | _ -> args
              in
              let rt =
                match Ast_types.unroll_node f.vtype with TFun (r, _, _) -> r | _ -> Cil_const.voidType
              in
              match ret with
              | Some lv when Cil.need_cast rt (Cil.typeOfLval lv) ->
                  let r = Cil.makeTempVar fd ~name:"__p2a_ret" rt in
                  temps := (fd.svar.vname, r.vname) :: !temps;
                  [ Cil.mkStmtOneInstr ~valid_sid:true (Call (Some (Cil.var r), Var f, args', loc));
                    Cil.mkStmtOneInstr ~valid_sid:true
                      (Set (lv, Cil.mkCast ~newt:(Cil.typeOfLval lv) (Cil.evar ~loc r), loc)) ]
              | _ -> [ Cil.mkStmtOneInstr ~valid_sid:true (Call (ret, Var f, args', loc)) ]
            in
            let last =
              match bad with
              | Some b -> [ Cil.mkStmtOneInstr ~valid_sid:true (Call (None, Var b, [], loc)) ]
              | None -> []
            in
            let chain =
              List.fold_right
                (fun f rest ->
                  let c =
                    Cil.new_exp ~loc
                      (BinOp (Eq, Cil.copy_exp sel, Cil.integer ~loc (id f), Cil_const.intType))
                  in
                  [ Cil.mkStmt ~valid_sid:true (If (c, Cil.mkBlock (branch f), Cil.mkBlock rest, loc)) ])
                cands last
            in
            s.skind <- Block (Cil.mkBlock (pre @ chain));
            Hashtbl.replace changed fd.svar.vid fd
        | _ -> ())
      calls;
    (* A call through a pointer becomes a direct call of each candidate, which
       may come before the candidate's definition: the program only took its
       address, which needs no declaration before it is defined.  A prototype
       of every defined candidate before the first function lets the direct
       call name it (C does not allow a call of a static function before any
       declaration of it). *)
    let called = Hashtbl.create 8 in
    List.iter (fun (_, _, cands) -> List.iter (fun f -> Hashtbl.replace called f.vid f) cands) calls;
    let protos =
      List.filter_map
        (function
          | GFun (fd, _) when Hashtbl.mem called fd.svar.vid ->
              Some (GFunDecl (Cil.empty_funspec (), fd.svar, loc0))
          | _ -> None)
        file.globals
    in
    if protos <> [] then file.globals <- insert_before_functions protos file.globals;
    Hashtbl.iter
      (fun _ fd ->
        Cfg.clearCFGinfo ~clear_id:false fd;
        Cfg.cfgFun fd)
      changed;
    Fragment.mark_ast_changed ();
    { function_ids = List.map (fun vi -> (vi.vname, id vi, Fragment.is_defined vi)) functions;
      temps = List.rev !temps;
      fnid_type = Some tname;
      bad_call = Option.map (fun vi -> vi.vname) bad }
  end
