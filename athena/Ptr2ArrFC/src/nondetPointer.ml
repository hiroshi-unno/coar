(* A pointer made from a nondeterministic integer: [(void * )
   __VERIFIER_nondet_ulong()], which the front end writes [tmp =
   __VERIFIER_nondet_ulong(); p = (void * )tmp;].  The AWS-C-Common harnesses
   (nondet_voidp), the sequentialized programs and the openssl tasks use it
   for a pointer of which nothing is known.

   Under GCC the value is an arbitrary address: NULL when the integer is 0,
   and otherwise an address the program did not obtain from an object.
   The translation has no addresses, so a nonzero integer becomes a value
   that points to no object: a number of its own, K + (v mod 2^20) with K
   above every function number, cast to the pointer type, which the
   transformation writes as minus the number (as a function number converted
   to a data pointer; an object's index is never negative).  Tests against
   NULL keep their meaning, and two such pointers are equal when the low
   bits of their integers are, as GCC's are when the integers are equal (two
   different integers with equal low bits give an execution in which the
   pointers compare equal, which GCC has when the integers are equal: the
   pointers have no other observable value).  A dereference, a free or any
   use as an object is invalid in the translation (the points-to analysis
   gives such a pointer no object, and the safety modes no bounds).

   Assumption: the program never relies on such a pointer being equal to
   the address of one of its objects, or on reading through it.  GCC may
   give it the address of an object, which the translation excludes; C
   makes both the conversion and the comparison implementation-defined.

   Applies when the integer is a local variable whose address is not taken,
   every write of which is the result of a __VERIFIER_nondet_* call of an
   integer type, and every read of which is converted to a pointer type.
   Anything else is left and refused as before.

   Contract: [run ()] rewrites the current project in place and returns the
   number of conversions replaced. *)

open Cil_types

let loc0 = Fileloc.unknown

(* The first number given to a value pointing to no object; a program has
   fewer functions than that. *)
let base = 1 lsl 24
let mask = (1 lsl 20) - 1

let is_nondet f =
  String.starts_with ~prefix:"__VERIFIER_nondet_" f.vname && not (Fragment.is_defined f)

let rec strip_ptr_casts e =
  match e.enode with
  | CastE (t, e') when Ast_types.is_ptr t && Ast_types.is_ptr (Cil.typeOf e') -> strip_ptr_casts e'
  | _ -> e

(* [Some (t, vi)] when [e] is [(T * )v] under pointer casts, v an integer
   variable *)
let pointer_of_int e =
  match (strip_ptr_casts e).enode with
  | CastE (t, { enode = Lval (Var vi, NoOffset); _ })
    when Ast_types.is_ptr t && Ast_types.is_integral vi.vtype ->
      Some (t, vi)
  | _ -> None

let run () =
  let file = Ast.get () in
  (* per local integer variable: written only by a nondet call, read only
     under a cast to a pointer *)
  let ok = Hashtbl.create 16 and bad = Hashtbl.create 16 in
  let candidates fd =
    let v =
      object (self)
        inherit Visitor.frama_c_inplace

        method! vinst i =
          match i with
          | Call (Some (Var vi, NoOffset), Var f, [], _)
            when (not vi.vglob) && Ast_types.is_integral vi.vtype && is_nondet f ->
              Hashtbl.replace ok vi.vid ();
              Cil.SkipChildren
          | Call (Some (Var vi, _), _, args, _) | Local_init (vi, ConsInit (_, args, _), _) ->
              Hashtbl.replace bad vi.vid ();
              List.iter (fun a -> ignore (Visitor.visitFramacExpr (self :> Visitor.frama_c_visitor) a)) args;
              Cil.SkipChildren
          | Set ((Var vi, NoOffset), e, _) ->
              Hashtbl.replace bad vi.vid ();
              ignore (Visitor.visitFramacExpr (self :> Visitor.frama_c_visitor) e);
              Cil.SkipChildren
          | Local_init (vi, AssignInit _, _) ->
              Hashtbl.replace bad vi.vid ();
              Cil.DoChildren
          | _ -> Cil.DoChildren

        method! vexpr e =
          match pointer_of_int e with
          | Some _ -> Cil.SkipChildren
          | None -> Cil.DoChildren

        method! vlval lv =
          (match lv with Var vi, _ -> Hashtbl.replace bad vi.vid () | _ -> ());
          Cil.DoChildren
      end
    in
    ignore (Visitor.visitFramacFunction v fd)
  in
  List.iter (function GFun (fd, _) -> candidates fd | _ -> ()) file.globals;
  let eligible vi =
    Hashtbl.mem ok vi.vid && (not (Hashtbl.mem bad vi.vid)) && (not vi.vglob) && not vi.vaddrof
  in
  let count = ref 0 in
  let typedef = ref None in
  let nonobj () =
    match !typedef with
    | Some t -> t
    | None ->
        let tname = Defunc.fresh_global_name file "__p2a_nonobj" in
        let ti = { torig_name = tname; tname; ttype = Cil_const.intType; treferenced = true } in
        file.globals <- GType (ti, loc0) :: file.globals;
        Fragment.nonobj_typedef := Some tname;
        let t = Cil_const.mk_tnamed ti in
        typedef := Some t;
        t
  in
  List.iter
    (function
      | GFun (fd, _) ->
          let changed = ref false in
          (* the statements computing the pointer of [(T * )v] into a fresh
             local, which replaces the cast *)
          let lift loc t vi =
            let nt = nonobj () in
            let p = Cil.makeTempVar fd ~name:"__p2a_nondet_ptr" t in
            let n = Cil.makeTempVar fd ~name:"__p2a_nondet_num" nt in
            let vt = vi.vtype in
            let v = Cil.evar ~loc vi in
            let num =
              Cil.mkCast ~newt:nt
                (Cil.mkBinOp_exn ~loc PlusA (Cil.integer ~loc base)
                   (Cil.mkCast ~newt:Cil_const.intType
                      (Cil.mkBinOp_exn ~loc BAnd v (Cil.kinteger ~loc (match Ast_types.unroll_node vt with TInt k -> k | _ -> IULong) mask))))
            in
            let set lv e = Cil.mkStmtOneInstr ~valid_sid:true (Set (lv, e, loc)) in
            let test =
              Cil.mkStmt ~valid_sid:true
                (If
                   ( Cil.mkBinOp_exn ~loc Eq v (Cil.mkCast ~newt:vt (Cil.zero ~loc)),
                     Cil.mkBlock [ set (Cil.var p) (Cil.mkCast ~newt:t (Cil.zero ~loc)) ],
                     Cil.mkBlock
                       [ set (Cil.var n) num;
                         set (Cil.var p) (Cil.new_exp ~loc (CastE (t, Cil.evar ~loc n))) ],
                     loc ))
            in
            incr count;
            changed := true;
            (test, Cil.evar ~loc p)
          in
          let pre = ref [] in
          let rewrite =
            object
              inherit Visitor.frama_c_inplace

              method! vexpr e =
                match pointer_of_int e with
                | Some (t, vi) when eligible vi ->
                    (* the casts above the conversion stay *)
                    let rec rebuild e =
                      match e.enode with
                      | CastE (t', e') when Ast_types.is_ptr t' && Ast_types.is_ptr (Cil.typeOf e') ->
                          { e with enode = CastE (t', rebuild e') }
                      | _ ->
                          let s, p = lift e.eloc t vi in
                          pre := s :: !pre;
                          p
                    in
                    Cil.ChangeTo (rebuild e)
                | _ -> Cil.DoChildren
            end
          in
          (* statement by statement: a statement using the conversion
             becomes a block of the computation and the statement, so the
             statement keeps its identity, its labels and the jumps to it *)
          let block_visitor =
            object
              inherit Visitor.frama_c_inplace

              method! vstmt_aux s =
                match s.skind with
                | Instr _ | Return (Some _, _) ->
                    pre := [];
                    let kind =
                      match s.skind with
                      | Instr i -> (
                          match Visitor.visitFramacInstr rewrite i with [ i' ] -> Instr i' | _ -> s.skind)
                      | Return (Some e, l) -> Return (Some (Visitor.visitFramacExpr rewrite e), l)
                      | k -> k
                    in
                    (match List.rev !pre with
                     | [] -> ()
                     | ps -> s.skind <- Block (Cil.mkBlock (ps @ [ Cil.mkStmt ~valid_sid:true kind ])));
                    Cil.SkipChildren
                | _ -> Cil.DoChildren
            end
          in
          ignore (Visitor.visitFramacFunction block_visitor fd);
          if !changed then begin
            Cfg.clearCFGinfo ~clear_id:false fd;
            Cfg.cfgFun fd
          end
      | _ -> ())
    file.globals;
  if !count > 0 then Fragment.mark_ast_changed ();
  !count
