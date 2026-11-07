(* The transformation record: a JSON file written beside the output, read by the
   checking tools and by consumers of the output.

   Fields (all present in every record; the lists the current stage does not
   fill are empty):
   - input: path, sha256, frama_c (version), args (the Frama-C command line),
     machdep (the machine description the input was read with, which fixes
     the width of every integer type);
   - mode: "normal" | "memory-safety" | "memory-cleanup" | "assume-safety";
     wrap_integers: null (no --wrap-integers), "unsigned" (unsigned
     operations wrap, signed ones are assumed not to overflow) or "all"
     (signed ones wrap too); integers (only with --integers=auto): the
     reading chosen ("int" or "bv"), whether the value analysis was used
     ("used", "off", "fallback:<reason>"), the bitwise operations that made
     it "bv", the reductions kept, placed as non-negative and left out, the
     nondet results not reduced, and how many operands were made constants;
     check_overflow: bool; unbounded_regions: bool
     (--unbounded-regions: the region arrays are read as having no length,
     so the output is meant for a consumer whose arrays have none, not to be
     run as C); scalar_cells: with --scalar-cells, the regions held in one
     scalar: region (its id) and name (the scalar); dropped_globals: the
     global variables of a function pointer type nothing refers to, removed
     before the transformation; function_ids (only when the program uses
     function pointers): the function numbers that replace function pointer
     values, name, id and whether the function has a body (see [Defunc]);
   - uninit: "keep" | "check" | "nondet" (-ptr2arr-uninit); uninit_targets:
     with check or nondet, the local variables that start uninitialised: name
     (in the input), variable (its name in the normalised input, where the
     front end renames a local that shadows another), function, location
     (of the declaration), leaves (the
     scalars it holds; null for a variable-length array), placed (where it
     is given its starting state: "block-entry", "function-entry",
     "jump-source", "declaration" for a variable-length array, right after
     its allocation) and, with check, checked (whether its reads are
     checked: its address is never taken); uninit_parameters: with check,
     the structure parameters that receive the state of their argument,
     whose reads are checked too (name, function); uninit_generators: with nondet,
     the functions the starting values are drawn from (name, and kind, the
     suffix of the __VERIFIER_nondet_ function each returns); uninit_elided:
     with check, the reads left unchecked because every path writes them
     first (function, location, variable);
   - violations: the functions whose call marks a memory-safety violation:
     name, property ("valid-deref", "valid-free", "valid-memtrack",
     "valid-memcleanup", or "valid-memsafety" for the one reach_error marker
     that stands for every property) and exit_status (what the marker's
     definition exits with in the output, null when the output only declares
     it); with --check-overflow, the reach_error() called before a signed
     operation that overflows (property "no-overflow", declared only), when
     the program has one to check; with --uninit=check, the marker a read of
     an uninitialised variable calls (property "uninit-read": reach_error,
     declared only, in the normal mode; in a safety mode as its other
     violations, __p2a_violation_uninit_read with status 82 for the split
     markers); empty otherwise;
   - memtrack: in --memory-safety (and --memory-cleanup with
     --memtrack-nonterminating), how valid-memtrack is checked: check
     ("guess" | "fixpoint"), nonterminating (whether it is also checked
     where an execution that does not halt passes), guess_function (the weak
     function the guess form draws its choices from), probe_function (the
     weak function that chooses whether to check at such a place) and
     stop_function (the function that ends the execution after such a check
     that found nothing), each null when the output has none; null in the
     other modes;
   - memtrack_points: the output statements of those checks (function-entry,
     loop-head);
   - region_exhausted: the function an allocation past the end of a
     region's array stops the execution at (name, exit_status 81), which
     reports neither a violation nor its absence; null when the output has
     none (the normal mode, and the reach-error markers, where such an
     allocation calls reach_error);
   - end_points: the output statements that hold an end check (before the
     call that ends the execution, or after the return from the input's
     main), each with its kind ("main-return" | "exit" | "abort"); empty when
     the output checks no end (a mode without end checks, or a program with
     no heap allocation, where valid-memtrack and valid-memcleanup cannot
     fail);
   - regions, objects, pointers: the region partition and what it is made of;
     a variable object's reason is "address-taken", or "memtrack-root" for a
     variable made an object so that an end check deeper in the call stack
     sees it as a root;
   - names: one entry per name in the output: name, original (the name in the
     input, for a name that comes from it, the roles program and index; null
     for a name the transformation made), function (the enclosing function,
     for a formal or a local), kind (global | function | formal | local), role
     (program | index | addr | generated | shadow | marker | stop | exhausted) and, for an
     integer-typed name, type = { kind: "int" | "bool" | "enum", width,
     signed }. A function the output only declares is listed when the
     transformation gave it a role: a marker, or the input's reach_error
     renamed;
   - statements: original statement id -> output statement ids;
   - source_map: for every statement the output prints, where (output_line,
     output_column: the first character, physical lines), in which function,
     its role for a witness (loop-head | branch | call | target | other),
     the position of the input statement it comes from (input: line, column
     and function, physical in the input file; null for a statement from
     another file or made by the transformation), for a target the property
     violated there and for a branch whether the output prints the input's
     condition negated (cond_negated); input_file names the input as input
     does (see Srcmap);
   - rejected: the unsupported constructs, when the output was written anyway. *)

open Cil_types

let int_type t =
  match Ast_types.unroll_node t with
  | TInt IBool -> Some (`Assoc [ ("kind", `String "bool") ])
  | TInt ik ->
      Some
        (`Assoc
          [ ("kind", `String "int");
            ("width", `Int (Cil.bitsSizeOfInt ik));
            ("signed", `Bool (Cil.isSigned ik)) ])
  | TEnum ei ->
      Some
        (`Assoc
          [ ("kind", `String "enum");
            ("width", `Int (Cil.bitsSizeOfInt ei.ekind));
            ("signed", `Bool (Cil.isSigned ei.ekind)) ])
  | _ -> None

(* The roles of the names the input has: any other is a name the
   transformation made, which has no original. *)
let from_input role = role = "program" || role = "index"

let name_entry ?func ~kind ~role vi =
  let fields =
    [ ("name", `String vi.vname);
      ("original", if from_input role then `String vi.vorig_name else `Null);
      ("kind", `String kind);
      ("role", `String role) ]
    @ (match func with Some f -> [ ("function", `String f) ] | None -> [])
    @ match int_type vi.vtype with Some t -> [ ("type", t) ] | None -> []
  in
  `Assoc fields

(* Names of the program in [prj], each with its role ([roles], by variable
   id; [program] when absent), and the functions [prj] only declares that have
   a role, each once. String-literal arrays are not names a reader of the C
   sees. *)
let program_names ?(roles = Hashtbl.create 1) prj =
  let role vi = Option.value ~default:"program" (Hashtbl.find_opt roles vi.vid) in
  Project.on prj
    (fun () ->
      let acc = ref [] in
      let add e = acc := e :: !acc in
      let globals = (Ast.get ()).globals in
      let defined = Hashtbl.create 16 in
      List.iter (function GFun (fd, _) -> Hashtbl.replace defined fd.svar.vid () | _ -> ()) globals;
      List.iter
        (function
          | GFunDecl (_, vi, _)
            when Hashtbl.mem roles vi.vid && not (Hashtbl.mem defined vi.vid) ->
              Hashtbl.replace defined vi.vid ();
              add (name_entry ~kind:"function" ~role:(role vi) vi)
          | GVar (vi, _, _) when not (Ast_info.is_string_literal vi) ->
              add (name_entry ~kind:"global" ~role:(role vi) vi)
          | GVarDecl (vi, _) when not (Ast_types.is_fun vi.vtype) ->
              add (name_entry ~kind:"global" ~role:(role vi) vi)
          | GFun (fd, _) ->
              add (name_entry ~kind:"function" ~role:(role fd.svar) fd.svar);
              let func = fd.svar.vname in
              List.iter
                (fun vi -> add (name_entry ~func ~kind:"formal" ~role:(role vi) vi))
                fd.sformals;
              List.iter
                (fun vi -> add (name_entry ~func ~kind:"local" ~role:(role vi) vi))
                fd.slocals
          | _ -> ())
        globals;
      List.rev !acc)
    ()

let opt_int = function Some n -> `Int n | None -> `Null

let pretty_typ t = `String (Format.asprintf "%a" Cil_datatype.Typ.pretty t)

(* The region partition, read in the output project (the arrays and the
   static indices are the output's; the cell types are the input's). *)
let transform_parts prj ~size (ctx : Transform.ctx) pairs =
  Project.on prj
    (fun () ->
      let st = ctx.st in
      let regions =
        List.map
          (fun (r : Regions.region) ->
            let info = Hashtbl.find ctx.infos r.rid in
            let succ =
              Option.map
                (fun (s : Regions.region) -> s.rid)
                (Regions.find ctx.regs (PointsTo.pt st r.rep))
            in
            `Assoc
              [ ("id", `Int r.rid);
                ("array", `String info.arr.vname);
                ("kind", `String (if info.byte then "byte" else "typed"));
                ("cell_type", pretty_typ info.sigma);
                ("cell_type_output", pretty_typ (Transform.tr_type info.sigma));
                ("length", `Int size);
                ("initial", `String "arbitrary");
                ("succ", opt_int succ) ])
          ctx.regs.list
      in
      let objects =
        List.concat_map
          (fun (r : Regions.region) ->
            let info = Hashtbl.find ctx.infos r.rid in
            List.map
              (function
                | Regions.Var vi ->
                    let kind =
                      if Ast_info.is_string_literal vi then "string" else "var"
                    in
                    `Assoc
                      [ ("kind", `String kind);
                        ( "reason",
                          `String
                            (if Hashtbl.mem ctx.memtrack_roots vi.vid then "memtrack-root"
                             else "address-taken") );
                        ("name", `String vi.vorig_name);
                        ("location", `String (Format.asprintf "%a" Fileloc.pretty vi.vdecl));
                        ("region", `Int r.rid);
                        ("static_index", opt_int (Hashtbl.find_opt ctx.static_index vi.vid));
                        ("cells", `Int (Regions.cells_of vi.vtype)) ]
                | Regions.Alloc site ->
                    `Assoc
                      [ ("kind", `String "alloc");
                        ("allocator", `String site.PointsTo.allocator);
                        ("function", `String site.func);
                        ("location", `String (Format.asprintf "%a" Fileloc.pretty site.loc));
                        ("region", `Int r.rid);
                        ("static_index", `Null) ])
              (List.rev r.objects)
            |> fun l -> ignore info; l)
          ctx.regs.list
      in
      let pointers =
        List.map
          (fun (name, func, kind, reg) ->
            `Assoc
              ([ ("name", `String name); ("kind", `String kind); ("region", opt_int reg) ]
              @ match func with Some f -> [ ("function", `String f) ] | None -> []))
          ctx.pointers
      in
      let statements =
        let tbl = Hashtbl.create 64 in
        List.iter
          (fun (o, n) ->
            Hashtbl.replace tbl o (n :: Option.value ~default:[] (Hashtbl.find_opt tbl o)))
          pairs;
        Hashtbl.fold (fun o ns acc -> (o, List.sort compare ns) :: acc) tbl []
        |> List.sort compare
        |> List.map (fun (o, ns) ->
               `Assoc [ ("input", `Int o); ("output", `List (List.map (fun n -> `Int n) ns)) ])
      in
      (regions, objects, pointers, statements))
    ()

let uninit_parts (ctx : Transform.ctx) =
  let target (t : Transform.uninit_target) =
    `Assoc
      ([ ("name", `String t.u_name);
         ("variable", `String t.u_var);
         ("function", `String t.u_func);
         ("location", `String (Format.asprintf "%a" Fileloc.pretty t.u_loc));
         ("leaves", opt_int t.u_leaves);
         ("placed", `List (List.map (fun p -> `String p) t.u_placed)) ]
      @ match t.u_checked with Some b -> [ ("checked", `Bool b) ] | None -> [])
  in
  ( List.map target ctx.uninit_targets,
    List.map
      (fun (name, func) -> `Assoc [ ("name", `String name); ("function", `String func) ])
      ctx.uninit_parameters,
    List.map
      (fun ((v : varinfo), k) -> `Assoc [ ("name", `String v.vname); ("kind", `String k) ])
      ctx.uninit_generators,
    List.map
      (fun (func, loc, name) ->
        `Assoc
          [ ("function", `String func);
            ("location", `String (Format.asprintf "%a" Fileloc.pretty loc));
            ("variable", `String name) ])
      ctx.uninit_elided )

let make ?transform ~source_map ~input ~machdep ~args ~mode ~wrap_integers ~check_overflow
    ?(unbounded_regions = false) ?(dropped_globals = []) ?(function_ids = [])
    ?(uninit = "keep") ?integers ~output_prj ~rejected () =
  let regions, objects, pointers, statements, roles =
    match transform with
    | Some (size, ctx, pairs) ->
        let r, o, p, s = transform_parts output_prj ~size ctx pairs in
        (r, o, p, s, Some ctx.Transform.roles)
    | None -> ([], [], [], [], None)
  in
  let violations =
    match transform with
    | Some (_, ctx, _) ->
        List.map
          (fun (name, property, status) ->
            `Assoc
              [ ("name", `String name);
                ("property", `String property);
                ("exit_status", opt_int status) ])
          (Transform.violations ctx)
    | None -> []
  in
  let uninit_targets, uninit_parameters, uninit_generators, uninit_elided =
    match transform with
    | Some (_, ctx, _) -> uninit_parts ctx
    | None -> ([], [], [], [])
  in
  let name_of = function Some (v : varinfo) -> `String v.vname | None -> `Null in
  let memtrack, end_points, memtrack_points =
    match transform with
    | Some (_, (ctx : Transform.ctx), _) ->
        ( (match ctx.memtrack with
           | Some form ->
               `Assoc
                 [ ("check", `String (match form with Transform.Guess -> "guess" | Fixpoint -> "fixpoint"));
                   ("nonterminating", `Bool ctx.nonterminating);
                   ("guess_function", name_of ctx.guess_fn);
                   ("probe_function", name_of ctx.probe_fn);
                   ("stop_function", name_of ctx.stop_fn) ]
           | None -> `Null),
          List.rev_map
            (fun (sid, kind) ->
              `Assoc [ ("stmt", `Int sid); ("kind", `String (Transform.end_kind_name kind)) ])
            ctx.end_points,
          List.rev_map
            (fun (sid, kind) -> `Assoc [ ("stmt", `Int sid); ("kind", `String kind) ])
            ctx.mt3_points )
    | None -> (`Null, [], [])
  in
  `Assoc
    ([ ( "input",
        `Assoc
          [ ("path", `String input);
            ("sha256", `String (Sha256.file input));
            ("frama_c", `String System_config.Version.id_and_codename);
            ("args", `List (List.map (fun a -> `String a) args));
            ("machdep", `String machdep) ] );
      ("mode", `String mode);
      ("wrap_integers", match wrap_integers with Some k -> `String k | None -> `Null);
      ("check_overflow", `Bool check_overflow);
      ("unbounded_regions", `Bool unbounded_regions);
      ("dropped_globals", `List (List.map (fun n -> `String n) dropped_globals));
    ]
    @ (match integers with Some sc -> [ ("integers", IntScan.to_json sc) ] | None -> [])
    @ (if function_ids = [] then []
       else
         [ ( "function_ids",
             `List
               (List.map
                  (fun (n, k, defined) ->
                    `Assoc [ ("name", `String n); ("id", `Int k); ("defined", `Bool defined) ])
                  function_ids) ) ])
    @ [
      ( "scalar_cells",
        match transform with
        | Some (_, (ctx : Transform.ctx), _) ->
            `List
              (Hashtbl.fold
                 (fun rid ((c : Cil_types.varinfo), _) acc ->
                   `Assoc [ ("region", `Int rid); ("name", `String c.vname) ] :: acc)
                 ctx.scalar_cells []
              |> List.sort compare)
        | None -> `List [] );
      ("uninit", `String uninit);
      ("uninit_targets", `List uninit_targets);
      ("uninit_parameters", `List uninit_parameters);
      ("uninit_generators", `List uninit_generators);
      ("uninit_elided", `List uninit_elided);
      ("violations", `List violations);
      ("memtrack", memtrack);
      ( "region_exhausted",
        match transform with
        | Some (_, (ctx : Transform.ctx), _) -> (
            match ctx.exhausted_fn with
            | Some v ->
                `Assoc
                  [ ("name", `String v.vname); ("exit_status", `Int Transform.exhausted_status) ]
            | None -> `Null)
        | None -> `Null );
      ("end_points", `List end_points);
      ("memtrack_points", `List memtrack_points);
      ("regions", `List regions);
      ("objects", `List objects);
      ("pointers", `List pointers);
      ("names", `List (program_names ?roles output_prj));
      ("statements", `List statements);
      ("source_map", source_map);
      ( "rejected",
        `List
          (List.map
             (fun (i : Fragment.issue) ->
               `Assoc
                 [ ("kind", `String i.kind);
                   ("location", `String (Format.asprintf "%a" Fileloc.pretty i.loc));
                   ("detail", `String i.detail) ])
             rejected) ) ])

let write path json =
  let oc = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out oc)
    (fun () ->
      Yojson.Safe.pretty_to_channel oc json;
      output_char oc '\n')
