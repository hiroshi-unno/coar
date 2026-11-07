(* A pointer converted to an integer whose value only becomes main's return
   value, the exit status: [return (int) strcpy(out, in);] in the dietlibc
   termination tasks, which the front end writes [__retres = (int)tmp;] and
   [return __retres;].

   The exit status is read by no property this tool translates for
   (reachability of an error, termination, memory safety, overflow): only
   the process that ran the program reads it.  The value is the low bits of
   an address under GCC, which the translation does not have; it becomes a
   nondeterministic integer of the conversion's type, which includes GCC's
   value.  The pointer expression is dropped, so it must read no memory
   (a variable, an address, pointer arithmetic on those); one that
   dereferences is left as it is.

   Applies only in main, when no function calls main or takes its address,
   to an assignment [v = (I)e] of such an expression to a local variable v
   of main whose address is not taken and which main reads only in
   [return v], and to [return (I)e].  Anything else is left and refused as
   before.

   Contract: [run ()] rewrites the current project in place and returns the
   number of conversions replaced. *)

open Cil_types

let rec reads_memory e =
  match e.enode with
  | Lval (Mem _, _) -> true
  | Lval (Var _, off) | AddrOf (Var _, off) | StartOf (Var _, off) -> offset_reads off
  | AddrOf (Mem a, off) | StartOf (Mem a, off) -> reads_memory a || offset_reads off
  | CastE (_, e') | UnOp (_, e', _) -> reads_memory e'
  | BinOp (_, a, b, _) -> reads_memory a || reads_memory b
  | _ -> false

and offset_reads = function
  | NoOffset -> false
  | Field (_, o) -> offset_reads o
  | Index (i, o) -> reads_memory i || offset_reads o

(* [Some (ik, e)] for [(I)e], I an integer type (not _Bool) of kind ik and
   e a pointer reading no memory. *)
let pointer_cast e =
  match e.enode with
  | CastE (t, p) when Ast_types.is_ptr (Cil.typeOf p) && not (reads_memory p) -> (
      match Ast_types.unroll_node t with
      | TInt ik when ik <> IBool && ik <> IInt128 && ik <> IUInt128 -> Some (t, ik)
      | TEnum ei -> Some (t, ei.ekind)
      | _ -> None)
  | _ -> None

let run () =
  let file = Ast.get () in
  let main =
    List.find_map (function GFun (fd, _) when fd.svar.vname = "main" -> Some fd | _ -> None) file.globals
  in
  match main with
  | None -> 0
  | Some main ->
      (* main called or its address taken: its return value is read *)
      let used = ref false in
      let v =
        object
          inherit Visitor.frama_c_inplace

          method! vvrbl vi =
            if vi.vid = main.svar.vid then used := true;
            Cil.SkipChildren
        end
      in
      (* main's own body may name main only by calling itself *)
      ignore (Visitor.visitFramacBlock v main.sbody);
      List.iter
        (function
          | GFun (fd, _) when fd.svar.vid <> main.svar.vid -> ignore (Visitor.visitFramacFunction v fd)
          | GVar _ as g -> ignore (Visitor.visitFramacGlobal v g)
          | _ -> ())
        file.globals;
      if !used then 0
      else begin
        (* the locals of main read anywhere but in [return v] *)
        let read_elsewhere = Hashtbl.create 8 in
        let reads =
          object (self)
            inherit Visitor.frama_c_inplace

            method! vstmt_aux s =
              match s.skind with
              | Return (Some { enode = Lval (Var _, NoOffset); _ }, _) -> Cil.SkipChildren
              | _ -> Cil.DoChildren

            method! vlval lv =
              (match lv with
               | Var vi, _ -> Hashtbl.replace read_elsewhere vi.vid ()
               | _ -> ());
              Cil.DoChildren

            method! vinst i =
              match i with
              | Set ((Var _, NoOffset), e, _) ->
                  (* the assigned variable is written, not read *)
                  ignore (Visitor.visitFramacExpr (self :> Visitor.frama_c_visitor) e);
                  Cil.SkipChildren
              | _ -> Cil.DoChildren
          end
        in
        ignore (Visitor.visitFramacFunction reads main);
        let nondets = Hashtbl.create 4 in
        let nondet ik =
          let suffix, t = LibModels.nondet_of_ikind ik in
          let name = "__VERIFIER_nondet_" ^ suffix in
          match Hashtbl.find_opt nondets name with
          | Some vi -> vi
          | None ->
              let vi =
                match LibModels.find_function file name with
                | Some vi -> vi
                | None ->
                    let ft = Cil_const.mk_tfun t (Some []) false in
                    let vi = Cil.makeGlobalVar name ft in
                    Cil.setFormalsDecl vi ft;
                    let spec = Cil.empty_funspec () in
                    file.globals <- Defunc.insert_before_functions [ GFunDecl (spec, vi, Fileloc.unknown) ] file.globals;
                    Globals.Functions.replace_by_declaration spec vi Fileloc.unknown;
                    vi
              in
              Hashtbl.replace nondets name vi;
              vi
        in
        let count = ref 0 in
        let draw (t, ik) loc =
          let _, nt = LibModels.nondet_of_ikind ik in
          let tmp = Cil.makeLocalVar main "__p2a_status" nt in
          incr count;
          (Call (Some (Cil.var tmp), Var (nondet ik), [], loc), Cil.mkCast ~newt:t (Cil.evar ~loc tmp))
        in
        let rewrite =
          object
            inherit Visitor.frama_c_inplace

            method! vstmt_aux s =
              match s.skind with
              | Return (Some e, loc) -> (
                  match pointer_cast e with
                  | Some k ->
                      let call, value = draw k loc in
                      s.skind <-
                        Block
                          (Cil.mkBlock
                             [ Cil.mkStmtOneInstr ~valid_sid:true call;
                               Cil.mkStmt ~valid_sid:true (Return (Some value, loc)) ]);
                      Cil.SkipChildren
                  | None -> Cil.DoChildren)
              | _ -> Cil.DoChildren

            method! vinst i =
              match i with
              | Set (((Var vi, NoOffset) as lv), e, loc)
                when (not vi.vglob) && (not vi.vaddrof) && not (Hashtbl.mem read_elsewhere vi.vid) -> (
                  match pointer_cast e with
                  | Some k ->
                      let call, value = draw k loc in
                      Cil.ChangeTo [ call; Set (lv, Cil.mkCast ~newt:(Cil.typeOfLval lv) value, loc) ]
                  | None -> Cil.SkipChildren)
              | _ -> Cil.SkipChildren
          end
        in
        ignore (Visitor.visitFramacFunction rewrite main);
        if !count > 0 then begin
          Cfg.clearCFGinfo ~clear_id:false main;
          Cfg.cfgFun main;
          Fragment.mark_ast_changed ()
        end;
        !count
      end
