(* The functions the program can run: main, every function a global
   initializer names (a table of functions), and, transitively, every function
   a reachable function's body names (called directly, or used as a value: a
   function pointer, an atexit argument).  Naming is the test, not calling, so
   a function reached only through a pointer stays.

   The functions that are not reachable are dropped, definitions and
   declarations alike, before anything else reads the program: they are never
   run, so dropping them changes no execution, and a construct outside the
   fragment inside them no longer refuses the whole program.  The tasks of
   SV-COMP's Juliet suite carry a support library (thread locks passing a
   pointer to pthread_mutex_destroy, string helpers) of which a test calls a
   few functions; before, any construct in the rest refused every task.  The
   global variables those functions used are kept: an unused variable changes
   nothing. *)

open Cil_types

(* The function variables named in [x], by vid. *)
let functions_named visit x =
  let found = Hashtbl.create 8 in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vvrbl vi =
        if Ast_types.is_fun vi.vtype then Hashtbl.replace found vi.vid ();
        Cil.SkipChildren
    end
  in
  visit v x;
  found

(* Drops the unreachable functions; their names, in the order of the file.
   Nothing is dropped from a program without main. *)
let drop_unreachable () =
  let file = Ast.get () in
  let bodies = Hashtbl.create 64 and roots = ref [] in
  List.iter
    (function
      | GFun (fd, _) ->
          Hashtbl.replace bodies fd.svar.vid
            (functions_named (fun v fd -> ignore (Visitor.visitFramacFunction v fd)) fd);
          if fd.svar.vname = "main" then roots := fd.svar.vid :: !roots
      | GVar (_, { init = Some _ }, _) as g ->
          Hashtbl.iter
            (fun vid () -> roots := vid :: !roots)
            (functions_named (fun v g -> ignore (Visitor.visitFramacGlobal v g)) g)
      | _ -> ())
    file.globals;
  let has_main =
    List.exists (function GFun (fd, _) -> fd.svar.vname = "main" | _ -> false) file.globals
  in
  if not has_main then []
  else begin
    let live = Hashtbl.create 64 in
    let rec visit vid =
      if not (Hashtbl.mem live vid) then begin
        Hashtbl.replace live vid ();
        match Hashtbl.find_opt bodies vid with
        | Some named -> Hashtbl.iter (fun f () -> visit f) named
        | None -> ()
      end
    in
    List.iter visit !roots;
    let dead vi = Ast_types.is_fun vi.vtype && not (Hashtbl.mem live vi.vid) in
    let dropped =
      List.filter_map
        (function
          | GFun (fd, _) when dead fd.svar -> Some fd.svar.vname
          | _ -> None)
        file.globals
    in
    let before = List.length file.globals in
    file.globals <-
      List.filter
        (function
          | GFun (fd, _) -> not (dead fd.svar)
          | GFunDecl (_, vi, _) -> not (dead vi)
          | _ -> true)
        file.globals;
    if List.length file.globals <> before then Fragment.mark_ast_changed ();
    dropped
  end

(* main's parameters, dropped when its body names none of them, as in the many
   tasks declaring `int main(int argc, char **argv)` and reading neither: main
   becomes `int main(void)`, which receives nothing the program reads.  Without
   this a pointer parameter becomes an index, `int main(int argc, int argv)`,
   which C does not allow as main, and in a safety mode it would need shadow
   parameters, which main cannot take.  True when they were dropped. *)
let drop_unused_main_params () =
  let file = Ast.get () in
  match
    List.find_map (function GFun (fd, _) when fd.svar.vname = "main" -> Some fd | _ -> None) file.globals
  with
  | Some fd when fd.sformals <> [] ->
      let named = Hashtbl.create 8 in
      let v =
        object
          inherit Visitor.frama_c_inplace

          method! vvrbl vi =
            Hashtbl.replace named vi.vid ();
            Cil.SkipChildren
        end
      in
      ignore (Visitor.visitFramacBlock v fd.sbody);
      if List.exists (fun p -> Hashtbl.mem named p.vid) fd.sformals then false
      else begin
        let ret = match Ast_types.unroll_node fd.svar.vtype with TFun (r, _, _) -> r | _ -> Cil_const.intType in
        Cil.setFormals fd [];
        Cil.update_var_type fd.svar (Cil_const.mk_tfun ret (Some []) false);
        Fragment.mark_ast_changed ();
        true
      end
  | _ -> false
