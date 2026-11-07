(* Library functions that GCC knows as builtins, called before the program
   declares them.

   A call of a function with no declaration in scope declares it implicitly
   as returning int (C90; C99 removed the rule).  When the program then
   declares the function with its real type, the two declarations conflict,
   and the front end refuses the input.  GCC reads such a call differently
   for its builtin library functions (memcpy, malloc, ...): the implicit
   declaration takes the builtin's type, GCC warns, and the later
   declaration agrees with it.  For any other function GCC reports the
   conflict as an error.

   Before the front end types the program, a copy of the program's own
   first file-scope declaration of such a function is placed right before
   the first top-level definition that names the function.  The calls then
   have that declaration in scope, as GCC reads them.  This is done only
   when:
   - the name is one of [builtins], and no declaration of it, at file scope
     or in a block, precedes its first use;
   - the later declaration is a prototype whose types are built from base
     types and typedef names defined before the point of insertion (no
     structure, union or enumeration tag, no typeof), so that the copy
     declares the same type there.
   After typing, [check] compares each copied declaration's type with the
   type GCC gives the builtin, qualifiers dropped (the Linux headers declare
   memcpy's source as [void *]: converting a pointer to a differently
   qualified pointer type keeps its value, C11 6.3.2.3p2, so the call passes
   the same values either way).  A program that declares another type is
   one GCC reads with the builtin's type at the call and the program's type
   after it, and it is refused.

   Contract: [transform] is applied by the front end to every parsed file
   when [enabled ()] holds; it adds declarations and changes nothing else.
   [check ()] reads the typed program and returns the copied declarations
   whose type is not the builtin's. *)

open Cabs

(* GCC's builtin library functions this pass places, with their types. *)
let builtins : (string * (unit -> Cil_types.typ)) list =
  let open Cil_const in
  let size () = Machine.sizeof_type () in
  let vp () = voidPtrType and cvp () = mk_tptr (mk_tvoid ~tattr:[ ("const", []) ] ()) in
  let fn r ps = mk_tfun r (Some (List.map (fun t -> ("", t, [])) ps)) false in
  [ ("memcpy", fun () -> fn (vp ()) [ vp (); cvp (); size () ]);
    ("memmove", fun () -> fn (vp ()) [ vp (); cvp (); size () ]);
    ("memset", fun () -> fn (vp ()) [ vp (); intType; size () ]);
    ("memcmp", fun () -> fn intType [ cvp (); cvp (); size () ]);
    ("malloc", fun () -> fn (vp ()) [ size () ]);
    ("calloc", fun () -> fn (vp ()) [ size (); size () ]);
    ("free", fun () -> fn voidType [ vp () ]) ]

(* The names copied by the last [transform]. *)
let copied : string list ref = ref []

let enabled = ref (fun () -> false)

(* The names a top-level definition declares at file scope. *)
let declared = function
  | DECDEF (_, (_, ns), _) -> List.map (fun ((n, _, _, _), _) -> n) ns
  | FUNDEF (_, (_, (n, _, _, _)), _, _, _) -> [ n ]
  | _ -> []

(* The names [d] uses as variables, and the names it declares in a block
   (a function body's declarations, nested prototypes included). *)
let uses_and_locals d =
  let used = Hashtbl.create 16 and local = Hashtbl.create 16 in
  let uses =
    object
      inherit Cabsvisit.nopCabsVisitor

      method! vexpr e =
        (match e.expr_node with VARIABLE n -> Hashtbl.replace used n () | _ -> ());
        Cil.DoChildren
    end
  in
  let locals =
    object
      inherit Cabsvisit.nopCabsVisitor

      method! vname _ _ ((n, _, _, _) as nm) =
        Hashtbl.replace local n ();
        Cil.ChangeTo nm
    end
  in
  ignore (Cabsvisit.visitCabsDefinition uses d);
  (match d with
   | FUNDEF (_, _, body, _, _) -> ignore (Cabsvisit.visitCabsBlock locals body)
   | _ -> ());
  (used, local)

(* The typedef names a definition introduces. *)
let typedefs = function
  | TYPEDEF ((_, ns), _) -> List.map (fun (n, _, _, _) -> n) ns
  | _ -> []

(* Whether the types of declaration [spec, name] use only base types and the
   typedef names [known], and declare a function with a prototype. *)
let placeable known (spec, (_, dt, _, _)) =
  let ok = ref true in
  let v =
    object
      inherit Cabsvisit.nopCabsVisitor

      method! vtypespec t =
        (match t with
         | Tnamed n -> if not (Hashtbl.mem known n) then ok := false
         | Tstruct _ | Tunion _ | Tenum _ | TtypeofE _ | TtypeofT _ -> ok := false
         | _ -> ());
        Cil.DoChildren
    end
  in
  ignore (Cabsvisit.visitCabsSpecifier v spec);
  ignore (Cabsvisit.visitCabsDeclType v false dt);
  (* a function's declarator: a prototype applied to the name, under the
     pointers of its result type (CIL prints [void *f(int)] as
     [PTR (PROTO (JUSTBASE, ...))]) *)
  let rec proto = function
    | PROTO ((JUSTBASE | PARENTYPE (_, JUSTBASE, _)), _, _, _) -> true
    | PTR (_, d) | PARENTYPE (_, d, _) -> proto d
    | _ -> false
  in
  !ok && proto dt

let transform ((path, defs) as file : Cabs.file) : Cabs.file =
  copied := [];
  if not (!enabled ()) then file
  else begin
    let defs_a = Array.of_list defs in
    let n = Array.length defs_a in
    let info = Array.map (fun (_, d) -> uses_and_locals d) defs_a in
    (* name -> index of its first file-scope declaration *)
    let first_decl = Hashtbl.create 16 in
    Array.iteri
      (fun i (_, d) ->
        List.iter
          (fun x -> if not (Hashtbl.mem first_decl x) then Hashtbl.add first_decl x i)
          (declared d))
      defs_a;
    (* insertions: index -> declarations to place before it *)
    let inserts = Hashtbl.create 4 in
    List.iter
      (fun (name, _) ->
        match Hashtbl.find_opt first_decl name with
        | None -> ()
        | Some k -> (
            let rec first_use i =
              if i >= k then None
              else
                let used, local = info.(i) in
                if Hashtbl.mem local name then Some (-1)
                else if Hashtbl.mem used name then Some i
                else first_use (i + 1)
            in
            match first_use 0 with
            | None | Some -1 -> ()
            | Some u -> (
                (* the declaration at k, reduced to [name] *)
                match snd defs_a.(k) with
                | DECDEF (_, (spec, ns), loc) -> (
                    match List.find_opt (fun ((x, _, _, _), _) -> x = name) ns with
                    | Some (nm, _) ->
                        let known = Hashtbl.create 64 in
                        for i = 0 to u - 1 do
                          List.iter (fun t -> Hashtbl.replace known t ()) (typedefs (snd defs_a.(i)))
                        done;
                        if placeable known (spec, nm) then begin
                          let d = DECDEF (None, (spec, [ (nm, NO_INIT) ]), loc) in
                          (* the flag of the copied declaration: not ghost
                             code when the original is not *)
                          Hashtbl.replace inserts u
                            ((fst defs_a.(k), d) :: Option.value ~default:[] (Hashtbl.find_opt inserts u));
                          copied := name :: !copied
                        end
                    | None -> ())
                | _ -> ())))
      builtins;
    if Hashtbl.length inserts = 0 then file
    else begin
      let out = ref [] in
      for i = n - 1 downto 0 do
        out := defs_a.(i) :: !out;
        match Hashtbl.find_opt inserts i with
        | Some ds -> out := List.rev ds @ !out
        | None -> ()
      done;
      (path, !out)
    end
  end

let () = Frontc.add_syntactic_transformation transform

let check () =
  let file = Ast.get () in
  List.filter_map
    (fun name ->
      let vi =
        List.find_map
          (function
            | Cil_types.GFunDecl (_, vi, _) when vi.vname = name -> Some vi
            | Cil_types.GFun (fd, _) when fd.svar.vname = name -> Some fd.svar
            | _ -> None)
          file.globals
      in
      match vi with
      | Some vi
        when not
               (Cil.areCompatibleTypes
                  (Cil.typeDeepDropAllAttributes vi.vtype)
                  (Cil.typeDeepDropAllAttributes ((List.assoc name builtins) ()))) ->
          Some
            { Fragment.kind = "implicit-declaration";
              loc = vi.vdecl;
              detail =
                Printf.sprintf
                  "%s is called before it is declared, and its declaration's type is not the \
                   one GCC gives the builtin"
                  name }
      | _ -> None)
    (List.rev !copied)
