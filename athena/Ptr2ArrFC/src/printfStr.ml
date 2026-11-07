(* printf printing a string the program holds, [printf("%s\n", line)], as the
   Juliet tasks' printLine does.  printf is an external function, and a pointer
   other than a string literal passed to one is outside the fragment: what the
   function reads through it is unknown in general.  For a %s conversion it is
   known: the characters from the pointer to the first 0.

   Before the fragment check, such a call is split at each plain %s (no flag,
   width, precision or length) whose argument is such a pointer: the text and
   the other conversions before it are printed by printf with their own
   arguments, as before, and the string by __p2a_print_string(p), a function
   added to the program that reads the characters one at a time and prints
   each with putchar.  The output is the same characters in the same order.
   That function is then transformed as any other: its reads are reads of the
   region the pointer points into, checked in a safety mode, so a string
   without its 0 inside its block is the invalid dereference it is in the
   input.

   Left as they are (and refused by the fragment check as before): a call whose
   result is used (the count printf returns would change), a format that is not
   a string literal, a %s with a flag, width, precision or length (%.5s, %ls),
   %n (it writes through a pointer), %p (it prints an address), a * width or
   precision, and a pointer passed to any other conversion. *)

open Cil_types

type piece = Text of string * exp list | Str of exp

exception Refused

let rec strip_casts e = match e.enode with CastE (_, e') -> strip_casts e' | _ -> e

let literal_string e =
  match (strip_casts e).enode with
  | StartOf (Var vi, NoOffset) | AddrOf (Var vi, Index (_, NoOffset))
    when Ast_info.is_string_literal vi -> (
      match Globals.Vars.get_string_literal vi with Str s -> Some s | Wstr _ -> None)
  | _ -> None

let program_pointer a =
  Ast_types.is_ptr (Cil.typeOf a)
  && (not (Fragment.is_string_literal_ptr a))
  && not (Fragment.is_null_constant a)

(* The pieces of [printf(fmt, args)], or [None] when nothing needs splitting
   (no %s of a program pointer); raises [Refused] on a form left as it is. *)
let pieces fmt args =
  let n = String.length fmt in
  let buf = Buffer.create 32 and cur = ref [] and out = ref [] and rest = ref args in
  let split = ref false in
  let take () = match !rest with a :: r -> rest := r; a | [] -> raise Refused in
  let flush () =
    if Buffer.length buf > 0 then out := Text (Buffer.contents buf, List.rev !cur) :: !out
    else if !cur <> [] then raise Refused;
    Buffer.clear buf;
    cur := []
  in
  let rec go i =
    if i >= n then ()
    else if fmt.[i] <> '%' then (Buffer.add_char buf fmt.[i]; go (i + 1))
    else if i + 1 < n && fmt.[i + 1] = '%' then (Buffer.add_string buf "%%"; go (i + 2))
    else begin
      let j = ref (i + 1) in
      let skip p = while !j < n && p fmt.[!j] do incr j done in
      skip (fun c -> String.contains "-+ #0'" c);
      if !j < n && fmt.[!j] = '*' then raise Refused;
      skip (fun c -> c >= '0' && c <= '9');
      if !j < n && fmt.[!j] = '.' then begin
        incr j;
        if !j < n && fmt.[!j] = '*' then raise Refused;
        skip (fun c -> c >= '0' && c <= '9')
      end;
      skip (fun c -> String.contains "hljztLq" c);
      if !j >= n then raise Refused;
      let conv = fmt.[!j] and plain = !j = i + 1 in
      let spec = String.sub fmt i (!j - i + 1) in
      (match conv with
       | 'n' | 'p' -> raise Refused
       | 's' when plain ->
           let a = take () in
           if program_pointer a then (flush (); out := Str a :: !out; split := true)
           else (Buffer.add_string buf spec; cur := a :: !cur)
       | _ ->
           let a = take () in
           if program_pointer a then raise Refused;
           Buffer.add_string buf spec;
           cur := a :: !cur);
      go (!j + 1)
    end
  in
  go 0;
  if !rest <> [] then raise Refused;
  flush ();
  if !split then Some (List.rev !out) else None

let find_function file name =
  List.find_map
    (function
      | GFun (fd, _) when fd.svar.vname = name -> Some fd.svar
      | GFunDecl (_, vi, _) when vi.vname = name -> Some vi
      | _ -> None)
    file.globals

(* Splits every such call; the number split.  In three passes, since adding a
   string literal or a function changes the list of globals, which a visit is
   walking: the calls to split, then the literals and the helper, then the
   calls rewritten. *)
let run () =
  let file = Ast.get () in
  let printf_ext =
    match find_function file "printf" with
    | Some vi when not (Fragment.is_defined vi) -> Some vi
    | _ -> None
  in
  match printf_ext with
  | None -> 0
  | Some printf_vi ->
      let loc0 = Fileloc.unknown in
      let split_of = function
        | Call (None, Var f, fmt :: args, _) when f.vid = printf_vi.vid -> (
            match literal_string fmt with
            | None -> None
            | Some text -> ( try pieces text args with Refused -> None))
        | _ -> None
      in
      (* 1: the texts the split calls print *)
      let texts = Hashtbl.create 8 and count = ref 0 in
      let collect =
        object
          inherit Visitor.frama_c_inplace

          method! vinst i =
            (match split_of i with
             | Some ps ->
                 incr count;
                 List.iter (function Text (t, _) -> Hashtbl.replace texts t () | Str _ -> ()) ps
             | None -> ());
            Cil.SkipChildren
        end
      in
      Visitor.visitFramacFileSameGlobals collect file;
      if !count = 0 then 0
      else begin
        (* 2: a literal per text, putchar's declaration, the helper *)
        let literals = Hashtbl.create 8 in
        Hashtbl.iter
          (fun t () -> Hashtbl.replace literals t (Globals.Vars.add_string_literal ~loc:loc0 (Str t)))
          texts;
        let decls = ref [] in
        let putchar =
          match find_function file "putchar" with
          | Some vi -> vi
          | None ->
              let t =
                Cil_const.mk_tfun Cil_const.intType (Some [ ("c", Cil_const.intType, []) ]) false
              in
              let vi = Cil.makeGlobalVar "putchar" t in
              Cil.setFormalsDecl vi t;
              let spec = Cil.empty_funspec () in
              decls := [ GFunDecl (spec, vi, loc0) ];
              Globals.Functions.replace_by_declaration spec vi loc0;
              vi
        in
        let fd = Cil.emptyFunction (Defunc.fresh_global_name file "__p2a_print_string") in
        Cil.update_var_type fd.svar
          (Cil_const.mk_tfun Cil_const.voidType (Some [ ("s", Cil_const.charPtrType, []) ]) false);
        let s = Cil.makeFormalVar fd "s" Cil_const.charPtrType in
        let cur () =
          Cil.mkCast ~newt:Cil_const.intType (Cil.new_exp ~loc:loc0 (Lval (Mem (Cil.evar s), NoOffset)))
        in
        fd.sbody.bstmts <-
          Cil.mkWhile
            ~guard:(Cil.new_exp ~loc:loc0 (BinOp (Ne, cur (), Cil.zero ~loc:loc0, Cil_const.intType)))
            ~body:
              [ Cil.mkStmtOneInstr ~valid_sid:true (Call (None, Var putchar, [ cur () ], loc0));
                Cil.mkStmtOneInstr ~valid_sid:true
                  (Set
                     ( Cil.var s,
                       Cil.new_exp ~loc:loc0
                         (BinOp (PlusPI, Cil.evar s, Cil.one ~loc:loc0, Cil_const.charPtrType)),
                       loc0 )) ]
            ()
          @ [ Cil.mkStmt ~valid_sid:true (Return (None, loc0)) ];
        file.globals <- Defunc.insert_before_functions (!decls @ [ GFun (fd, loc0) ]) file.globals;
        Globals.Functions.replace_by_definition (Cil.empty_funspec ()) fd loc0;
        (* 3: the calls rewritten *)
        let changed = Hashtbl.create 8 in
        let rewrite =
          object (self)
            inherit Visitor.frama_c_inplace

            method! vinst i =
              match (i, split_of i) with
              | Call (_, f, _, loc), Some ps ->
                  Option.iter (fun g -> Hashtbl.replace changed g.svar.vid g) self#current_func;
                  Cil.ChangeTo
                    (List.map
                       (function
                         | Text (t, a) ->
                             let lit = Hashtbl.find literals t in
                             Call (None, f, Cil.new_exp ~loc (StartOf (Cil.var lit)) :: a, loc)
                         | Str p ->
                             Call (None, Var fd.svar, [ Cil.mkCast ~newt:Cil_const.charPtrType p ], loc))
                       ps)
              | _ -> Cil.SkipChildren
          end
        in
        Visitor.visitFramacFileSameGlobals rewrite file;
        Hashtbl.iter
          (fun _ g ->
            Cfg.clearCFGinfo ~clear_id:false g;
            Cfg.cfgFun g)
          changed;
        Cfg.cfgFun fd;
        Fragment.mark_ast_changed ();
        !count
      end
