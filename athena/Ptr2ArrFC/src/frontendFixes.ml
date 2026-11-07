(* Two artefacts of the front end that make the printed program one a C
   compiler rejects, removed before the transformation copies the input.

   - A branch that cannot run, of an if whose condition folds to a constant,
     reading a temporary whose declaration the front end dropped: glibc's
     fpclassify and isnan macros select by sizeof, and Frama-C 33 keeps
     [else tmp_2 = tmp_1;] after removing tmp_1 with the arm of the
     conditional it belonged to (clang: use of undeclared identifier).  Such
     an if becomes the branch that runs.  Only when the other branch holds no
     label (no jump can enter it), so no execution changes.
   - The declaration the front end prints for a GCC builtin called without a
     prototype ([extern int (/* missing proto */ __builtin_isnan)(double)]),
     which clang refuses ("cannot redeclare builtin function").  The
     declaration is dropped; the calls stay, as in the input, which declared
     nothing either.
   - In the printed program ([infinity_texts], run on the program about to
     be printed, since the transformation folds the constant expressions it
     copies): a floating-point constant that folds to an infinity
     ([1.0f/0.0f]), which the printer writes [inff], an identifier no
     compiler knows.  Its text becomes the division [(1.0f/0.0f)] (with the
     constant's suffix and sign): GCC folds it to the same infinity, and the
     front end reads it back to the same constant.  A constant that folds to
     a NaN is not rewritten but reported: the front end's folding does not
     give a NaN the sign GCC's does ([0.0f * (1.0f/0.0f)] is a negative NaN
     to Frama-C 33 and a positive one to GCC 13), and the sign is visible to
     signbit, copysign and a read of the bits. *)

open Cil_types

let undeclared_locals fd block =
  let known = Hashtbl.create 16 in
  List.iter (fun v -> Hashtbl.replace known v.vid ()) (fd.sformals @ fd.slocals);
  let found = ref false in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vvrbl vi =
        if (not vi.vglob) && not (Hashtbl.mem known vi.vid) then found := true;
        Cil.SkipChildren
    end
  in
  ignore (Visitor.visitFramacBlock v block);
  !found

let has_label block =
  let found = ref false in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vstmt_aux s =
        if s.labels <> [] then found := true;
        Cil.DoChildren
    end
  in
  ignore (Visitor.visitFramacBlock v block);
  !found

(* The ifs folded; the number. *)
let fold_dead_branches () =
  let file = Ast.get () in
  let count = ref 0 in
  List.iter
    (function
      | GFun (fd, _) ->
          let changed = ref false in
          let v =
            object
              inherit Visitor.frama_c_inplace

              method! vstmt_aux s =
                (match s.skind with
                 | If (c, b1, b2, _) -> (
                     match Cil.isInteger (Cil.constFold true c) with
                     | Some z ->
                         let live, dead = if Z.equal z Z.zero then (b2, b1) else (b1, b2) in
                         if undeclared_locals fd dead && not (has_label dead) then begin
                           s.skind <- Block live;
                           changed := true;
                           incr count
                         end
                     | None -> ())
                 | _ -> ());
                Cil.DoChildren
            end
          in
          ignore (Visitor.visitFramacFunction v fd);
          if !changed then begin
            Cfg.clearCFGinfo ~clear_id:false fd;
            Cfg.cfgFun fd
          end
      | _ -> ())
    file.globals;
  !count

(* The prototype-less builtin declarations dropped; the number. *)
let drop_implicit_builtin_decls () =
  let file = Ast.get () in
  let implicit vi =
    String.starts_with ~prefix:"__builtin_" vi.vname
    && (not (Fragment.is_defined vi))
    && Ast_attributes.contains Ast_attributes.fc_missingproto vi.vtype.tattr
  in
  let n = List.length (List.filter (function GFunDecl (_, vi, _) -> implicit vi | _ -> false) file.globals) in
  if n > 0 then
    file.globals <- List.filter (function GFunDecl (_, vi, _) -> not (implicit vi) | _ -> true) file.globals;
  n

(* The NaN constants met by the last [run]. *)
let nan_constants : Fileloc.t list ref = ref []

(* The infinite constants given a text; the number.  Records the NaN
   constants in [nan_constants]. *)
let infinity_texts () =
  let file = Ast.get () in
  let count = ref 0 in
  nan_constants := [];
  (* a visitor of CIL, not of Frama-C: the printed program holds functions
     the transformation added without registering them as kernel functions *)
  let v =
    object
      inherit Cil.nopCilVisitor

      method! vexpr e =
        match e.enode with
        | Const (CReal (r, _, None)) when Float.is_nan r ->
            nan_constants := e.eloc :: !nan_constants;
            Cil.SkipChildren
        | Const (CReal (r, ((FFloat | FDouble | FLongDouble) as k), None))
          when Float.abs r = Float.infinity ->
            let suffix = match k with FFloat -> "f" | FLongDouble -> "L" | _ -> "" in
            let text =
              Printf.sprintf "(%s1.0%s/0.0%s)" (if r < 0. then "-" else "") suffix suffix
            in
            incr count;
            Cil.ChangeTo { e with enode = Const (CReal (r, k, Some text)) }
        | _ -> Cil.DoChildren
    end
  in
  Cil.visitCilFileSameGlobals v file;
  nan_constants := List.rev !nan_constants;
  !count

let nan_issues () =
  List.map
    (fun loc ->
      { Fragment.kind = "float-constant";
        loc;
        detail =
          "a NaN constant folded by the front end (its sign may differ from the one GCC gives)" })
    !nan_constants

let run () =
  let a = fold_dead_branches () and b = drop_implicit_builtin_decls () in
  if a + b > 0 then Fragment.mark_ast_changed ();
  (a, b)
