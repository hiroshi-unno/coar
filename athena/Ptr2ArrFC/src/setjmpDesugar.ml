(* setjmp and longjmp written with ordinary control: a longjmp leaves each
   function between it and the target setjmp through the function's return,
   and the function holding the setjmp jumps to it.

   - Each call of setjmp (_setjmp) gets a number k.  It stores k and the
     number of the current activation of its function in the first two
     words of the jmp_buf's __jmpbuf (an activation number is drawn from a
     global counter on entry to every function holding a setjmp), and gives
     0; a statement labelled for k, reached only by a jump, gives the value
     the longjmp passed instead.
   - longjmp(buf, v) reads k and the activation from buf, records them with
     v (1 when v is 0, C11 7.13.2.1p4) and sets a global flag "unwinding".
   - After a longjmp and after every call of a function that can reach one,
     while the flag is set: a function holding a setjmp whose activation is
     the one recorded jumps to the recorded k's label (and clears the flag);
     any other function leaves through its return statement (its return
     value is not read: every caller tests the flag first, and a call whose
     result is assigned assigns it only when the flag is clear, since the
     call never returned in the input); main, which nothing returns to, ends
     the execution with abort(): the target's function has returned, which
     is undefined in C (7.13.2.1p2).

   The executions are those of the input: a longjmp transfers control to
   the setjmp that saved buf, in the activation that saved it, with the
   functions in between left; objects keep the values they hold at the
   longjmp (C makes the non-volatile automatic objects of the target's
   function changed in between indeterminate, 7.13.2.1p3, and their last
   values are among those).

   Applies when every call of setjmp and longjmp passes a pointer to a
   struct __jmp_buf_tag whose __jmpbuf is an array of at least two words
   (glibc's jmp_buf; the activation numbers are counted in the word's
   type, so they are assumed not to wrap: fewer activations than 2^31), every call is direct (function pointers are
   numbers by now), and every function has one return statement (the
   front end's normalisation).  Otherwise nothing is rewritten and the calls
   are refused as before.  sigsetjmp and siglongjmp are not handled.

   Contract: [run ()] rewrites the current project in place and returns the
   number of setjmp and longjmp calls rewritten. *)

open Cil_types

let loc0 = Fileloc.unknown
let setjmp_names = [ "_setjmp"; "setjmp" ]
let longjmp_names = [ "longjmp"; "_longjmp" ]

let is_external_named names f = List.mem f.vname names && not (Fragment.is_defined f)

let rec strip_casts e = match e.enode with CastE (_, e') -> strip_casts e' | _ -> e

(* The __jmpbuf field of [buf]'s structure and its element type, when
   [buf] points to a struct __jmp_buf_tag holding at least two words there
   (long under LP64, int under ILP32). *)
let jmpbuf_field buf =
  match Ast_types.unroll_node (Cil.typeOf (strip_casts buf)) with
  | TPtr t -> (
      match Ast_types.unroll_node t with
      | TComp ci when ci.cname = "__jmp_buf_tag" -> (
          match ci.cfields with
          | Some fs -> (
              match List.find_opt (fun f -> f.fname = "__jmpbuf") fs with
              | Some f -> (
                  match Ast_types.unroll_node f.ftype with
                  | TArray (et, Some n) -> (
                      match (Ast_types.unroll_node et, Cil.isInteger (Cil.constFold true n)) with
                      | TInt (IInt | ILong | ILongLong), Some z when Z.geq z (Z.of_int 2) ->
                          Some (f, et)
                      | _ -> None)
                  | _ -> None)
              | None -> None)
          | None -> None)
      | _ -> None)
  | _ -> None

let word buf f i =
  let b = strip_casts buf in
  (Mem b, Field (f, Index (Cil.integer ~loc:loc0 i, NoOffset)))

(* The unique return statement of [fd]. *)
let return_stmt fd =
  let found = ref [] in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vstmt_aux s =
        (match s.skind with Return _ -> found := s :: !found | _ -> ());
        Cil.DoChildren
    end
  in
  ignore (Visitor.visitFramacFunction v fd);
  match !found with [ s ] -> Some s | _ -> None

let run () =
  let file = Ast.get () in
  let funcs = List.filter_map (function GFun (fd, _) -> Some fd | _ -> None) file.globals in
  (* the calls of setjmp and longjmp, by function *)
  let sj = Hashtbl.create 8 and lj = Hashtbl.create 8 and calls = Hashtbl.create 64 in
  let well_formed = ref true in
  List.iter
    (fun fd ->
      let v =
        object
          inherit Visitor.frama_c_inplace

          method! vinst i =
            (match i with
             | Call (_, Var f, args, _) | Local_init (_, ConsInit (f, args, _), _) ->
                 if is_external_named setjmp_names f || is_external_named longjmp_names f then begin
                   (match args with
                    | buf :: _ when jmpbuf_field buf <> None -> ()
                    | _ -> well_formed := false);
                   if is_external_named setjmp_names f then Hashtbl.replace sj fd.svar.vid ()
                   else Hashtbl.replace lj fd.svar.vid ()
                 end
                 else Hashtbl.replace calls (fd.svar.vid, f.vid) ()
             | Call (_, Mem _, _, _) -> well_formed := false
             | _ -> ());
            Cil.SkipChildren
        end
      in
      ignore (Visitor.visitFramacFunction v fd))
    funcs;
  if Hashtbl.length sj = 0 && Hashtbl.length lj = 0 then 0
  else if (not !well_formed) || List.exists (fun fd -> return_stmt fd = None) funcs then 0
  else begin
    (* the type of a word of the buffers (one structure type per program) *)
    let word_type = ref None in
    List.iter
      (fun fd ->
        let v =
          object
            inherit Visitor.frama_c_inplace

            method! vinst i =
              (match i with
               | Call (_, Var f, buf :: _, _) | Local_init (_, ConsInit (f, buf :: _, _), _)
                 when is_external_named setjmp_names f || is_external_named longjmp_names f ->
                   if !word_type = None then word_type := Option.map snd (jmpbuf_field buf)
               | _ -> ());
              Cil.SkipChildren
          end
        in
        ignore (Visitor.visitFramacFunction v fd))
      funcs;
    let wt = Option.get !word_type in
    (* the functions that can reach a longjmp *)
    let unwinds = Hashtbl.create 8 in
    Hashtbl.iter (fun vid () -> Hashtbl.replace unwinds vid ()) lj;
    let changed = ref true in
    while !changed do
      changed := false;
      Hashtbl.iter
        (fun (caller, callee) () ->
          if Hashtbl.mem unwinds callee && not (Hashtbl.mem unwinds caller) then begin
            Hashtbl.replace unwinds caller ();
            changed := true
          end)
        calls
    done;
    (* the globals of the protocol *)
    let gvar name t =
      let vi = Cil.makeGlobalVar (Defunc.fresh_global_name file name) t in
      let ii = { init = Some (CInit (SingleInit (Cil.mkCast ~newt:t (Cil.zero ~loc:loc0)))) } in
      file.globals <- Defunc.insert_before_functions [ GVar (vi, ii, loc0) ] file.globals;
      Globals.Vars.add vi ii;
      vi
    in
    let int = Cil_const.intType in
    let active = gvar "__p2a_jmp_active" int in
    let site = gvar "__p2a_jmp_site" wt in
    let frame_g = gvar "__p2a_jmp_frame" wt in
    let value = gvar "__p2a_jmp_value" int in
    let frames = gvar "__p2a_activations" wt in
    let abort_vi =
      match LibModels.find_function file "abort" with
      | Some vi -> vi
      | None ->
          let t = Cil_const.mk_tfun ~tattr:Defunc.noreturn Cil_const.voidType (Some []) false in
          let vi = Cil.makeGlobalVar "abort" t in
          Cil.setFormalsDecl vi t;
          let spec = Cil.empty_funspec () in
          file.globals <- Defunc.insert_before_functions [ GFunDecl (spec, vi, loc0) ] file.globals;
          Globals.Functions.replace_by_declaration spec vi loc0;
          vi
    in
    let mk = Cil.mkStmt ~valid_sid:true in
    let instr i = Cil.mkStmtOneInstr ~valid_sid:true i in
    let set lv e = instr (Set (lv, Cil.mkCast ~newt:(Cil.typeOfLval lv) e, loc0)) in
    let ev = Cil.evar ~loc:loc0 in
    let count = ref 0 and next_site = ref 0 in
    List.iter
      (fun fd ->
        let has_sites = Hashtbl.mem sj fd.svar.vid in
        let reaches = Hashtbl.mem unwinds fd.svar.vid in
        if has_sites || reaches then begin
          let frame_l = if has_sites then Some (Cil.makeLocalVar fd "__p2a_activation" wt) else None in
          let ret =
            match return_stmt fd with Some s -> s | None -> assert false
          in
          if ret.labels = [] then ret.labels <- [ Label ("__p2a_return", loc0, false) ];
          (* the sites of this function: number, statement *)
          let sites = ref [] in
          let sj_value = lazy (Cil.makeLocalVar fd "__p2a_setjmp_value" int) in
          (* leaving while unwinding: to the recorded site, or out *)
          let leave () =
            let out =
              if fd.svar.vname = "main" then [ instr (Call (None, Var abort_vi, [], loc0)) ]
              else
                (match ret.skind with
                 | Return (Some { enode = Lval ((Var r, NoOffset) as lv); _ }, _) when not r.vglob ->
                     (* not read: every caller tests the flag; written so
                        that no uninitialised value is returned *)
                     if Ast_types.is_scalar r.vtype then [ set lv (Cil.zero ~loc:loc0) ] else []
                 | _ -> [])
                @ [ mk (Goto (ref ret, loc0)) ]
            in
            let dispatch =
              match frame_l with
              | None -> []
              | Some fl ->
                  let jumps =
                    List.fold_right
                      (fun (k, target) rest ->
                        [ mk
                            (If
                               ( Cil.mkBinOp_exn ~loc:loc0 Eq (ev site) (Cil.mkCast ~newt:wt (Cil.integer ~loc:loc0 k)),
                                 Cil.mkBlock [ mk (Goto (ref target, loc0)) ],
                                 Cil.mkBlock rest,
                                 loc0 )) ])
                      !sites []
                  in
                  [ mk
                      (If
                         ( Cil.mkBinOp_exn ~loc:loc0 Eq (ev frame_g) (ev fl),
                           Cil.mkBlock jumps,
                           Cil.mkBlock [],
                           loc0 )) ]
            in
            mk (If (ev active, Cil.mkBlock (dispatch @ out), Cil.mkBlock [], loc0))
          in
          (* the checks are built after every site is known *)
          let pending = ref [] in
          let check () =
            let s = mk (Instr (Skip loc0)) in
            pending := s :: !pending;
            s
          in
          let rewrite_stmt s =
            match s.skind with
            | Instr (Call (r, Var f, args, loc)) when is_external_named setjmp_names f
                                                   || is_external_named longjmp_names f
                                                   || Hashtbl.mem unwinds f.vid ->
                Some (r, None, f, args, loc)
            | Instr (Local_init (v, ConsInit (f, args, _), loc))
              when is_external_named setjmp_names f || is_external_named longjmp_names f
                   || Hashtbl.mem unwinds f.vid ->
                Some (None, Some v, f, args, loc)
            | _ -> None
          in
          let v =
            object
              inherit Visitor.frama_c_inplace

              method! vstmt_aux s =
                match rewrite_stmt s with
                | None -> Cil.DoChildren
                | Some (r, init, f, args, loc) ->
                    incr count;
                    let assign_result e =
                      match (r, init) with
                      | Some lv, _ -> [ set lv e ]
                      | None, Some vi ->
                          vi.vdefined <- false;
                          [ set (Cil.var vi) e ]
                      | None, None -> []
                    in
                    let stmts =
                      if is_external_named setjmp_names f then begin
                        let buf = List.hd args in
                        let fld = fst (Option.get (jmpbuf_field buf)) in
                        let k = !next_site in
                        incr next_site;
                        let sv = Lazy.force sj_value in
                        let fl = Option.get frame_l in
                        let target =
                          mk (Block (Cil.mkBlock [ set (Cil.var active) (Cil.zero ~loc:loc0);
                                                   set (Cil.var sv) (ev value) ]))
                        in
                        target.labels <- [ Label (Printf.sprintf "__p2a_setjmp_%d" k, loc0, false) ];
                        let after = mk (Block (Cil.mkBlock (assign_result (ev sv)))) in
                        after.labels <- [ Label (Printf.sprintf "__p2a_setjmp_%d_done" k, loc0, false) ];
                        sites := (k, target) :: !sites;
                        [ set (word buf fld 0) (Cil.integer ~loc k);
                          set (word buf fld 1) (ev fl);
                          set (Cil.var sv) (Cil.zero ~loc);
                          mk (Goto (ref after, loc));
                          target;
                          after ]
                      end
                      else if is_external_named longjmp_names f then begin
                        let buf, arg = match args with [ b; a ] -> (b, a) | _ -> assert false in
                        let fld = fst (Option.get (jmpbuf_field buf)) in
                        [ set (Cil.var site) (Cil.new_exp ~loc (Lval (word buf fld 0)));
                          set (Cil.var frame_g) (Cil.new_exp ~loc (Lval (word buf fld 1)));
                          set (Cil.var value) arg;
                          mk
                            (If
                               ( Cil.mkBinOp_exn ~loc Eq (ev value) (Cil.zero ~loc),
                                 Cil.mkBlock [ set (Cil.var value) (Cil.one ~loc) ],
                                 Cil.mkBlock [],
                                 loc ));
                          set (Cil.var active) (Cil.one ~loc);
                          check () ]
                      end
                      else begin
                        (* a call of a function that can reach a longjmp *)
                        let rt =
                          match Ast_types.unroll_node f.vtype with TFun (t, _, _) -> t | _ -> Cil_const.voidType
                        in
                        match (r, init) with
                        | None, None -> [ instr (Call (None, Var f, args, loc)); check () ]
                        | _ ->
                            let tmp = Cil.makeTempVar fd ~name:"__p2a_result" rt in
                            [ instr (Call (Some (Cil.var tmp), Var f, args, loc)); check () ]
                            @ assign_result (ev tmp)
                      end
                    in
                    s.skind <- Block (Cil.mkBlock stmts);
                    Cil.SkipChildren
            end
          in
          ignore (Visitor.visitFramacFunction v fd);
          (* every check, now that the sites are known *)
          List.iter (fun s -> s.skind <- (leave ()).skind) !pending;
          (* a new activation number on entry *)
          (match frame_l with
           | Some fl ->
               fd.sbody.bstmts <-
                 set (Cil.var frames) (Cil.mkBinOp_exn ~loc:loc0 PlusA (ev frames) (Cil.mkCast ~newt:wt (Cil.one ~loc:loc0)))
                 :: set (Cil.var fl) (ev frames) :: fd.sbody.bstmts
           | None -> ());
          Cfg.clearCFGinfo ~clear_id:false fd;
          Cfg.cfgFun fd
        end)
      funcs;
    if !count > 0 then Fragment.mark_ast_changed ();
    !count
  end
