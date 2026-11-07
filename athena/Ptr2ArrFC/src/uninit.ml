(* Uninitialised local variables made nondeterministic (--uninit=nondet).

   C gives an automatic local variable declared without an initialiser an
   indeterminate value each time its declaration is reached, and the
   variables the front end makes (its temporaries, and the array a
   variable-length array allocates) start the same way. In the output each
   such variable (see [UninitTargets]) starts with a nondeterministic value
   of its type instead, written where its block starts: every scalar of it
   (every element of an array, every field of a structure) gets the result
   of a generated function __p2a_uninit_k() for its type k, and a pointer
   gets NULL, as does a function number (a function pointer before
   [Defunc] rewrote it). A variable-length array is filled right after its allocation.
   An enumeration takes a value of its underlying integer type (C lets the
   variable hold any of them), a bit-field the value of its declared type,
   converted on assignment as C converts it.

   __p2a_uninit_k() is defined weak, as __VERIFIER_nondet_k() returned (the
   signed char one returns __VERIFIER_nondet_char(), char being signed on
   the machines the front end describes), so that a consumer reads it as
   that nondeterministic function and a checking tool can link a strong
   definition in its place (one that returns zero reproduces a run of the
   input whose uninitialised memory is zero). The definitions are added to
   the program before the integer reductions run, so that with
   --wrap-integers the result of __VERIFIER_nondet_k() is reduced as the
   result of any external function is.

   A block a jump enters without passing its start (the body of a switch,
   whose declarations the front end gathers at its start, or a block with a
   label a goto from outside it jumps to) skips the writes at its start. Its
   variables are written also at the start of the function and right before
   every such jump, so that they start anew each time the block is entered
   as C says; for that their declarations are moved to the function's
   outermost block, in scope at both places (the front end gives every local
   of a function a distinct name, so nothing changes meaning). A variable
   whose address is taken is not moved: it is a block of a region, which the
   transformation allocates where its block starts, and is written there
   only. A goto that jumps back over a declaration is refused before this
   runs (see [Fragment.check]).

   Globals and static locals are left as they are: C gives them zero, the
   transformation writes the ones in a region at the start of main, and the
   others are C globals with C's initial value.

   Contract: [run st] rewrites the current project in place; it must run
   before the overflow checks, the integer reductions and the
   pointer-replacing transformation, which see the writes as ordinary
   assignments and calls. [created st] lists the variables made,
   [generators st] the generated functions with their kinds, [targets st]
   the variables made nondeterministic: name in the input, function,
   declaration, scalar count (None for a variable-length array) and where
   they are written. *)

open Cil_types

type placement = Block_entry | Function_entry | Jump_source | Declaration

let placement_name = function
  | Block_entry -> "block-entry"
  | Function_entry -> "function-entry"
  | Jump_source -> "jump-source"
  | Declaration -> "declaration"

type st = {
  names : (string, unit) Hashtbl.t;  (** every ordinary identifier taken *)
  gens : (string, fundec) Hashtbl.t;  (** kind -> __p2a_uninit_k *)
  mutable gen_order : (string * fundec) list;  (** reversed *)
  mutable created : varinfo list;
  mutable targets : (varinfo * string * int option * placement list) list;  (** reversed *)
  mutable new_globals : global list;  (** reversed *)
  counters : (int * int, varinfo) Hashtbl.t;
      (** (function id, loop depth) -> the loop counter at that depth *)
  fnid : string option;
      (** the typedef of function numbers (see [Defunc]): a function pointer
          before the rewrite, so it starts at NULL (0) as a pointer does *)
}

let loc0 = Fileloc.unknown

let create ?fnid () =
  { names = Hashtbl.create 64; gens = Hashtbl.create 8; gen_order = []; created = [];
    targets = []; new_globals = []; counters = Hashtbl.create 8; fnid }

(* Whether [t] names the type of function numbers, through typedefs. *)
let rec is_fnid st t =
  match (t.tnode, st.fnid) with
  | TNamed ti, Some n -> ti.tname = n || is_fnid st ti.ttype
  | _ -> false

let created st = st.created
let generators st = List.rev_map (fun (k, fd) -> (fd.svar, k)) st.gen_order
let targets st = List.rev st.targets

let fresh st base =
  let rec go i =
    let n = if i = 0 then base else Printf.sprintf "%s_%d" base i in
    if Hashtbl.mem st.names n then go (i + 1)
    else begin
      Hashtbl.replace st.names n ();
      n
    end
  in
  go 0

let stmt i = Cil.mkStmtOneInstr ~valid_sid:true i

(* The kind of a scalar type: the suffix of its __VERIFIER_nondet_ function. *)
let kind_of_ikind = function
  | IBool -> "bool"
  | IChar -> "char"
  | ISChar -> "schar"
  | IUChar -> "uchar"
  | IShort -> "short"
  | IUShort -> "ushort"
  | IInt -> "int"
  | IUInt -> "uint"
  | ILong -> "long"
  | IULong -> "ulong"
  | ILongLong -> "longlong"
  | IULongLong -> "ulonglong"
  | IInt128 | IUInt128 -> raise (Transform.Not_implemented "an uninitialised 128-bit integer")

let type_of_kind = function
  | "bool" -> Cil_const.boolType
  | "char" -> Cil_const.charType
  | "schar" -> Cil_const.scharType
  | "uchar" -> Cil_const.ucharType
  | "short" -> Cil_const.shortType
  | "ushort" -> Cil_const.ushortType
  | "int" -> Cil_const.intType
  | "uint" -> Cil_const.uintType
  | "long" -> Cil_const.longType
  | "ulong" -> Cil_const.ulongType
  | "longlong" -> Cil_const.longLongType
  | "ulonglong" -> Cil_const.ulongLongType
  | "float" -> Cil_const.floatType
  | "double" -> Cil_const.doubleType
  | k -> invalid_arg k

let nondet_name k = "__VERIFIER_nondet_" ^ if k = "schar" then "char" else k

(* The input's __VERIFIER_nondet_k when it has one, declared otherwise. *)
let nondet_fn st k =
  let name = nondet_name k in
  match
    List.find_map
      (function
        | GFun (fd, _) when fd.svar.vname = name -> Some fd.svar
        | GFunDecl (_, vi, _) when vi.vname = name -> Some vi
        | _ -> None)
      ((Ast.get ()).globals @ List.rev st.new_globals)
  with
  | Some vi -> vi
  | None ->
      let rt = type_of_kind (if k = "schar" then "char" else k) in
      let t = Cil_const.mk_tfun rt (Some []) false in
      let vi = Cil.makeGlobalVar name t in
      Cil.setFormalsDecl vi t;
      Hashtbl.replace st.names name ();
      st.new_globals <- GFunDecl (Cil.empty_funspec (), vi, loc0) :: st.new_globals;
      (* the visitors of the later passes look every function up *)
      Globals.Functions.replace_by_declaration (Cil.empty_funspec ()) vi loc0;
      vi

(* __p2a_uninit_k, defined weak on first use. *)
let generator st k =
  match Hashtbl.find_opt st.gens k with
  | Some fd -> fd.svar
  | None ->
      let nd = nondet_fn st k in
      let ty = type_of_kind k in
      let fd = Cil.emptyFunction (fresh st ("__p2a_uninit_" ^ k)) in
      Cil.setReturnType fd ty;
      fd.svar.vattr <- Ast_attributes.add ("weak", []) fd.svar.vattr;
      (* in the front end's normal form, so that the output reads back
         unchanged: a result of another type is converted into a variable of
         the returned type before the return *)
      let nt = Cil.getReturnType nd.vtype in
      let r = Cil.makeLocalVar fd "r" ty in
      let draw =
        if Cil_datatype.Typ.equal (Ast_types.unroll nt) (Ast_types.unroll ty) then
          [ stmt (Call (Some (Cil.var r), Var nd, [], loc0)) ]
        else begin
          let d = Cil.makeLocalVar fd "d" nt in
          st.created <- d :: st.created;
          [ stmt (Call (Some (Cil.var d), Var nd, [], loc0));
            stmt (Set (Cil.var r, Cil.mkCast ~newt:ty (Cil.evar d), loc0)) ]
        end
      in
      fd.sbody.bstmts <-
        draw @ [ Cil.mkStmt ~valid_sid:true (Return (Some (Cil.evar r), loc0)) ];
      st.created <- fd.svar :: r :: st.created;
      Hashtbl.add st.gens k fd;
      st.gen_order <- (k, fd) :: st.gen_order;
      (* the front end reads a weak definition back as a declaration that
         carries the attribute followed by the definition, so the output
         has both and reads back unchanged *)
      Cil.unsafeSetFormalsDecl fd.svar fd.sformals;
      st.new_globals <-
        GFun (fd, loc0) :: GFunDecl (Cil.empty_funspec (), fd.svar, loc0) :: st.new_globals;
      Globals.Functions.replace_by_definition (Cil.empty_funspec ()) fd loc0;
      fd.svar

(* The loop counters of a function, one per nesting depth. *)
let counter st fd depth =
  match Hashtbl.find_opt st.counters (fd.svar.vid, depth) with
  | Some v -> v
  | None ->
      let v = Cil.makeLocalVar fd (fresh st "p2a_u") Cil_const.intType in
      st.created <- v :: st.created;
      Hashtbl.add st.counters (fd.svar.vid, depth) v;
      v

let rec is_bitfield = function
  | NoOffset -> false
  | Field (f, NoOffset) -> f.fbitfield <> None
  | Field (_, o) | Index (_, o) -> is_bitfield o

(* The statements that write a nondeterministic value of type [t] into the
   left value [lv], scalar by scalar; [depth] counts the loops around. A
   value converted on its way (to an enumeration, to a bit-field) is drawn
   into a temporary first, as the front end would write it. *)
let rec fill st fd ?(depth = 0) lv t =
  let via_temp k =
    let tmp = Cil.makeTempVar fd ~name:"p2a_e" (type_of_kind k) in
    st.created <- tmp :: st.created;
    [ stmt (Call (Some (Cil.var tmp), Var (generator st k), [], loc0));
      stmt (Set (lv, Cil.new_exp ~loc:loc0 (CastE (Cil.typeOfLval lv, Cil.evar tmp)), loc0)) ]
  in
  if is_fnid st t then [ stmt (Set (lv, Cil.mkCast ~newt:t (Cil.zero ~loc:loc0), loc0)) ]
  else
  match Ast_types.unroll_node t with
  | TPtr _ -> [ stmt (Set (lv, Cil.mkCast ~newt:t (Cil.zero ~loc:loc0), loc0)) ]
  | TInt ik when is_bitfield (snd lv) -> via_temp (kind_of_ikind ik)
  | TInt ik -> [ stmt (Call (Some lv, Var (generator st (kind_of_ikind ik)), [], loc0)) ]
  | TEnum ei ->
      (* a value of the underlying type, converted *)
      via_temp (kind_of_ikind ei.ekind)
  | TFloat FFloat -> [ stmt (Call (Some lv, Var (generator st "float"), [], loc0)) ]
  | TFloat FDouble -> [ stmt (Call (Some lv, Var (generator st "double"), [], loc0)) ]
  | TFloat FLongDouble ->
      (* refused by the fragment check *)
      raise (Transform.Unsupported "an uninitialised long double")
  | TArray (t', (Some _ as len)) ->
      let n = Cil.lenOfArray len in
      let k = counter st fd depth in
      let elt = Cil.addOffsetLval (Index (Cil.evar k, NoOffset)) lv in
      Cil.mkForIncr ~iter:k ~first:(Cil.zero ~loc:loc0) ~stopat:(Cil.integer ~loc:loc0 n)
        ~incr:(Cil.one ~loc:loc0)
        ~body:(fill st fd ~depth:(depth + 1) elt t')
        ()
  | TComp ci when ci.cstruct ->
      List.concat_map
        (fun f -> fill st fd ~depth (Cil.addOffsetLval (Field (f, NoOffset)) lv) f.ftype)
        (Option.value ~default:[] ci.cfields)
  | _ ->
      raise
        (Transform.Not_implemented
           (Format.asprintf "an uninitialised %a" Cil_datatype.Typ.pretty t))

(* The writes of a variable-length array's elements, after the allocation
   of [size] bytes it is initialised by. *)
let fill_vla st fd v size =
  let elt = Ast_types.direct_pointed_type v.vtype in
  let k = counter st fd 0 in
  let count =
    Cil.mkCast ~newt:Cil_const.intType
      (Cil.new_exp ~loc:loc0
         (BinOp (Div, Cil.copy_exp size, Cil.new_exp ~loc:loc0 (SizeOf elt), Cil.typeOf size)))
  in
  let lv = Cil.mkMem ~addr:(Cil.new_exp ~loc:loc0 (BinOp (PlusPI, Cil.evar v, Cil.evar k, v.vtype))) ~off:NoOffset in
  Cil.mkForIncr ~iter:k ~first:(Cil.zero ~loc:loc0) ~stopat:count ~incr:(Cil.one ~loc:loc0)
    ~body:(fill st fd ~depth:1 lv elt)
    ()

let addr_taken fd =
  let h = Hashtbl.create 8 in
  let v =
    object
      inherit Visitor.frama_c_inplace

      method! vexpr e =
        (match e.enode with
         | AddrOf (Var vi, _) | StartOf (Var vi, _) -> Hashtbl.replace h vi.vid ()
         | _ -> ());
        Cil.DoChildren
    end
  in
  ignore (Visitor.visitFramacFunction v fd);
  h

let rewrite st fd =
  let targets = UninitTargets.targets fd in
  if targets <> [] then begin
    let jumps = UninitTargets.jumps fd in
    let taken = addr_taken fd in
    (* the writes placed before each jump into a block, by statement id *)
    let before = Hashtbl.create 4 and entry = ref [] in
    let blocks = ref [] in
    List.iter
      (fun (t : UninitTargets.target) ->
        if not (List.memq t.block !blocks) then blocks := t.block :: !blocks)
      targets;
    let vla_writes = Hashtbl.create 4 in
    List.iter
      (fun b ->
        let here = List.filter (fun (t : UninitTargets.target) -> t.block == b) targets in
        let sources = UninitTargets.jump_sources jumps b in
        let at_entry =
          List.concat_map
            (fun (t : UninitTargets.target) ->
              match t.vla with
              | Some size ->
                  Hashtbl.replace vla_writes t.var.vid (fill_vla st fd t.var size);
                  st.targets <- (t.var, fd.svar.vname, None, [ Declaration ]) :: st.targets;
                  []
              | None ->
                  let moved = sources <> [] && not (Hashtbl.mem taken t.var.vid) in
                  let w () = fill st fd (Cil.var t.var) t.var.vtype in
                  if moved then begin
                    b.blocals <- List.filter (fun v -> v != t.var) b.blocals;
                    fd.sbody.blocals <- fd.sbody.blocals @ [ t.var ];
                    entry := !entry @ w ();
                    List.iter
                      (fun s ->
                        let prev =
                          match Hashtbl.find_opt before s.sid with Some (_, w) -> w | None -> []
                        in
                        Hashtbl.replace before s.sid (s, prev @ w ()))
                      sources
                  end;
                  st.targets <-
                    ( t.var, fd.svar.vname, Some (UninitTargets.leaves t.var.vtype),
                      Block_entry :: (if moved then [ Function_entry; Jump_source ] else []) )
                    :: st.targets;
                  w ())
            here
        in
        b.bstmts <- at_entry @ b.bstmts)
      (List.rev !blocks);
    (* the elements of a variable-length array, right after its allocation
       (which the front end places in a block or, with the computation of
       its length, in an unspecified sequence) *)
    if Hashtbl.length vla_writes > 0 then begin
      let writes s =
        match s.skind with
        | Instr (Local_init (v, _, _)) -> Hashtbl.find_opt vla_writes v.vid
        | _ -> None
      in
      let v =
        object
          inherit Visitor.frama_c_inplace

          method! vblock b =
            b.bstmts <-
              List.concat_map
                (fun s -> match writes s with Some w -> s :: w | None -> [ s ])
                b.bstmts;
            Cil.DoChildren

          method! vstmt_aux s =
            (match s.skind with
             | UnspecifiedSequence l ->
                 s.skind <-
                   UnspecifiedSequence
                     (List.concat_map
                        (fun ((s', _, _, _, _) as e) ->
                          match writes s' with
                          | Some w -> e :: List.map (fun w -> (w, [], [], [], [])) w
                          | None -> [ e ])
                        l)
             | _ -> ());
            Cil.DoChildren
        end
      in
      ignore (Visitor.visitFramacFunction v fd)
    end;
    (* before each jump into a block whose variables were moved; the
       labels stay on the statement, so that a jump to them writes too *)
    Hashtbl.iter
      (fun _ (s, writes) ->
        let inner = Cil.mkStmt ~valid_sid:true s.skind in
        s.skind <- Block (Cil.mkBlock (writes @ [ inner ])))
      before;
    fd.sbody.bstmts <- !entry @ fd.sbody.bstmts
  end

let run st =
  let file = Ast.get () in
  let note n = Hashtbl.replace st.names n () in
  List.iter
    (function
      | GVar (vi, _, _) | GVarDecl (vi, _) | GFunDecl (_, vi, _) -> note vi.vname
      | GFun (fd, _) ->
          note fd.svar.vname;
          List.iter (fun v -> note v.vname) fd.sformals;
          List.iter (fun v -> note v.vname) fd.slocals
      | GType (ti, _) -> note ti.tname
      | GEnumTag (ei, _) | GEnumTagDecl (ei, _) -> List.iter (fun it -> note it.einame) ei.eitems
      | _ -> ())
    file.globals;
  List.iter (function GFun (fd, _) -> rewrite st fd | _ -> ()) file.globals;
  (* the declarations of the nondeterministic functions and the generators,
     before the first function definition, so that the integer reductions
     and the transformation see the generators' bodies *)
  let defs = List.rev st.new_globals in
  let rec insert = function
    | (GFun _ as g) :: rest -> defs @ (g :: rest)
    | g :: rest -> g :: insert rest
    | [] -> defs
  in
  if defs <> [] then file.globals <- insert file.globals
