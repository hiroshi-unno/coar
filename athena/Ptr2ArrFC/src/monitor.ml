(* Instrumentation of the input that checks the region partition at run time.

   The instrumented program registers every object instance as it comes into
   existence (a global at the start of main, a local at the entry of its
   block, a parameter at the entry of its function, an allocated block right
   after the allocation), with its address range and the region the analysis
   put it in; and before each dereference [*e], it looks up the registration
   that contains the value of [e] and checks that its region is the region the
   analysis gives [e]. A mismatch is a pointer that reached an object outside
   the region the transformation would read it from: the partition is not
   sound for this execution.

   The region numbers are those of the transformation because the analysis is
   deterministic and runs on the same input. A string literal is registered
   through another occurrence of the same literal, which has the same address
   when the compiler merges identical literals (gcc does within a translation
   unit; C does not require it). A value no registration contains is counted
   as unknown rather than as a violation.
   Registrations are never removed: the latest one containing an address
   wins, so a block reused after a release or a return is attributed to its
   new object.

   For valid-memcleanup the monitor also counts the heap blocks left
   allocated when the execution ends: a block from malloc or calloc is
   registered as a heap block, a call of free marks the latest heap block
   starting at its argument released, and at the end the blocks not released
   are counted. The ends are those of the transformation: the return from
   main and exit (counted by a function registered with atexit at the start
   of main, which runs after every function the program registers), and the
   calls that end the execution without the atexit functions (abort, _Exit,
   __assert_fail, and reach_error and __VERIFIER_error when the program does
   not define them), counted right before the call.

   Contract: [run ()] works in the current project, a copy of the input, and
   instruments it in place; the runtime is tools/p2a_monitor.c. *)

open Cil_types

let loc0 = Fileloc.unknown

let declare name ret args =
  let t =
    Cil_const.mk_tfun ret (Some (List.map (fun (n, t) -> (n, t, [])) args)) false
  in
  let vi = Cil.makeGlobalVar name t in
  Cil.setFormalsDecl vi t;
  vi

let run () =
  let file = Ast.get () in
  let st = PointsTo.analyse () in
  let regs = Regions.compute st in
  let rid n = match Regions.find regs n with Some r -> r.Regions.rid | None -> -1 in
  let is_object vi = Hashtbl.mem st.address_taken vi.vid in
  let voidp = Cil_const.voidPtrType and ulong = Cil_const.ulongType in
  let ity = Cil_const.intType in
  let reg_f = declare "p2a_mon_reg" Cil_const.voidType [ ("p", voidp); ("n", ulong); ("rid", ity) ] in
  let chk_f = declare "p2a_mon_chk" Cil_const.voidType [ ("p", voidp); ("rid", ity); ("line", ity) ] in
  let heap_f = declare "p2a_mon_heap" Cil_const.voidType [ ("p", voidp); ("n", ulong); ("rid", ity) ] in
  let free_f = declare "p2a_mon_free" Cil_const.voidType [ ("p", voidp) ] in
  let end_f = declare "p2a_mon_end" Cil_const.voidType [] in
  let start_f = declare "p2a_mon_start" Cil_const.voidType [] in
  let call f args loc = Call (None, Var f, args, loc) in
  let to_voidp e = Cil.mkCast ~newt:voidp e in
  let register_var v loc =
    call reg_f
      [ to_voidp (Cil.mkAddrOrStartOf ~loc (Cil.var v));
        Cil.new_exp ~loc (SizeOfE (Cil.evar v));
        Cil.integer ~loc (rid (PointsTo.var_node st v)) ]
      loc
  in
  let register_alloc ?(heap = false) lv bytes sid loc =
    call (if heap then heap_f else reg_f)
      [ to_voidp (Cil.new_exp ~loc (Lval lv)); Cil.mkCast ~newt:ulong bytes;
        Cil.integer ~loc (rid (PointsTo.alloc_node st sid)) ]
      loc
  in
  (* the checks for every dereference in a piece of code *)
  let checks_of visit loc =
    let acc = ref [] in
    let v =
      object
        inherit Visitor.frama_c_inplace

        (* the operand of sizeof is not evaluated *)
        method! vexpr e =
          match e.enode with
          | SizeOfE _ | AlignOfE _ -> Cil.SkipChildren
          | _ -> Cil.DoChildren

        method! vlval lv =
          (match lv with
           | Mem e, _ ->
               acc :=
                 call chk_f
                   [ to_voidp e; Cil.integer ~loc (rid (PointsTo.ptee st e));
                     Cil.integer ~loc (Fileloc.line loc) ]
                   loc
                 :: !acc
           | _ -> ());
          Cil.DoChildren
      end
    in
    visit v;
    List.rev !acc
  in
  let allocation_bytes f args =
    match ((if PointsTo.is_defined f then "" else f.vname), args) with
    | ("malloc" | "alloca" | "__builtin_alloca" | "__fc_vla_alloc"), [ n ] -> Some n
    | "calloc", [ n; s ] -> Some (Cil.new_exp ~loc:n.eloc (BinOp (Mult, n, s, Cil.typeOf n)))
    | "realloc", [ _; n ] -> Some n
    | _ -> None
  in
  let external_name f = if PointsTo.is_defined f then "" else f.vname in
  let is_heap f = List.mem (external_name f) [ "malloc"; "calloc"; "realloc" ] in
  let wrapped = Hashtbl.create 16 in
  let instrument fd =
    let visitor =
      object (self)
        inherit Visitor.frama_c_inplace

        method! vinst i =
          let loc = Cil_datatype.Instr.loc i in
          let sid = match self#current_stmt with Some s -> s.sid | None -> -1 in
          let before = checks_of (fun v -> ignore (Visitor.visitFramacInstr v i)) loc in
          let after =
            match i with
            | Call (Some lv, Var f, args, _) -> (
                match allocation_bytes f args with
                | Some n -> [ register_alloc ~heap:(is_heap f) lv n sid loc ]
                | None -> [])
            | Local_init (v, ConsInit (f, args, _), _) -> (
                match allocation_bytes f args with
                | Some n -> [ register_alloc ~heap:(is_heap f) (Cil.var v) n sid loc ]
                | None -> [])
            | _ -> []
          in
          (* a release, and an end of the execution that skips the atexit
             functions *)
          let before =
            match i with
            | Call (_, Var f, [ p ], _) when external_name f = "free" ->
                before @ [ call free_f [ to_voidp p ] loc ]
            | (Call (_, Var f, [ p; _ ], _) | Local_init (_, ConsInit (f, [ p; _ ], _), _))
              when external_name f = "realloc" ->
                (* realloc releases its argument's block (the result is
                   registered as a new one, the same address included) *)
                before @ [ call free_f [ to_voidp p ] loc ]
            | Call (_, Var f, _, _)
              when List.mem (external_name f)
                     [ "abort"; "_Exit"; "__assert_fail"; "reach_error"; "__VERIFIER_error" ] ->
                before @ [ call end_f [] loc ]
            | _ -> before
          in
          (* a local declared with an initialiser is printed where it is
             initialised, so it is registered right after *)
          let after =
            match i with
            | Local_init (v, _, _) when is_object v -> register_var v loc :: after
            | _ -> after
          in
          Cil.ChangeTo (before @ [ i ] @ after)

        method! vstmt_aux s =
          let guard e loc =
            let cs = checks_of (fun v -> ignore (Visitor.visitFramacExpr v e)) loc in
            if cs <> [] && not (Hashtbl.mem wrapped s.sid) then begin
              let inner = Cil.mkStmt ~valid_sid:true s.skind in
              (* the children of the new block include [inner], which must not
                 be wrapped again *)
              Hashtbl.add wrapped inner.sid ();
              s.skind <-
                Block
                  (Cil.mkBlock
                     (List.map (Cil.mkStmtOneInstr ~valid_sid:true) cs @ [ inner ]))
            end
          in
          (match s.skind with
           | Return (Some e, loc) | If (e, _, _, loc) | Switch (e, _, _, loc) -> guard e loc
           | _ -> ());
          Cil.DoChildren

        method! vblock b =
          let regs =
            List.filter_map
              (fun v ->
                if is_object v && not v.vdefined then Some (register_var v v.vdecl)
                else None)
              b.blocals
          in
          Cil.DoChildrenPost
            (fun b ->
              b.bstmts <- List.map (Cil.mkStmtOneInstr ~valid_sid:true) regs @ b.bstmts;
              b)
      end
    in
    ignore (Visitor.visitFramacFunction visitor fd);
    let formals =
      List.filter_map
        (fun v -> if is_object v then Some (register_var v v.vdecl) else None)
        fd.sformals
    in
    fd.sbody.bstmts <- List.map (Cil.mkStmtOneInstr ~valid_sid:true) formals @ fd.sbody.bstmts
  in
  List.iter (function GFun (fd, _) -> instrument fd | _ -> ()) file.globals;
  let globals_reg =
    List.filter_map
      (function
        | GVar (vi, _, loc) when is_object vi -> Some (register_var vi loc)
        | _ -> None)
      file.globals
  in
  List.iter
    (function
      | GFun (fd, _) when fd.svar.vname = "main" ->
          fd.sbody.bstmts <-
            List.map (Cil.mkStmtOneInstr ~valid_sid:true) (call start_f [] loc0 :: globals_reg)
            @ fd.sbody.bstmts
      | _ -> ())
    file.globals;
  file.globals <-
    List.map
      (fun f -> GFunDecl (Cil.empty_funspec (), f, loc0))
      [ reg_f; chk_f; heap_f; free_f; end_f; start_f ]
    @ file.globals;
  ignore loc0
